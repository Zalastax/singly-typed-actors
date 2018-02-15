module SimulationEnvironment where
open import Membership-equality using (_∈_)
open import ActorMonad

open import Data.List using (List ; _∷_ ; [] ; map)
open import Data.List.All using (All ; _∷_ ; [] ; lookup) renaming (map to ∀map)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Nat using (ℕ ; _≟_)
open import Data.Unit using (⊤ ; tt)

open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)

Name = ℕ

NamedInbox = Name × InboxShape
Store = List NamedInbox

¬[_] : ∀ {a b : Name} → Dec (a ≡ b) → Set
¬[ (yes x₁) ] = ⊥
¬[ (no x₁) ] = ⊤

_¬≡_ : ( a b : Name) → Set
a ¬≡ b = ¬[ a ≟ b ]

data _↦_∈e_ (n : Name) (S : InboxShape) : List NamedInbox → Set where
  zero : ∀ {xs}            → n ↦ S ∈e ((n , S) ∷ xs)
  suc  : ∀ {n' : Name} { S' xs} {pr : n ¬≡ n'}
         → n ↦ S ∈e xs → n ↦ S ∈e ((n' , S') ∷ xs)

justInbox : (Name × InboxShape) → InboxShape
justInbox = Σ.proj₂

-- An ActorM wrapped up with all of its parameters
-- Useful for storing ActorM of different type in the same list
-- We give each actor a name as preparation for the proof writing.
-- The proofs will use a heap, just as in separation logic.
record Actor : Set₂ where
  field
    IS : InboxShape
    A : Set₁
    references : List NamedInbox
    es : List InboxShape
    esEqRefs : (map justInbox references) ≡ es
    ce : A → List InboxShape
    act : ActorM IS A es ce
    name : Name

data NamedMessage (S : InboxShape): Set₁ where
  Value : ∀ {A} → A ∈ InboxShape.Values S → A → NamedMessage S
  Reference : ∀ {Fw} → Fw ∈ InboxShape.References S → Name → NamedMessage S

-- A list of messages, wrapped up with the shape of the messages
-- Each inbox is given a name, matching those for actors
record Inbox : Set₂ where
  field
    IS : InboxShape
    inb : List (NamedMessage IS)
    name : Name

-- Property that there exists an inbox of the right shape in the list of inboxes
-- This is used both for proving that every actor has an inbox, and for proving that every reference known by an actor has an inbox
hasInbox : Store → Actor → Set
hasInbox store actor = Actor.name actor ↦ Actor.IS actor ∈e store

-- Property that for every shape, there exists an inbox of that shape
-- Used for proving that every reference known by an actor has an inbox
allPointersCorrect : Store → Actor → Set₁
allPointersCorrect store actor = All (λ ref → Σ.proj₁ ref ↦ Σ.proj₂ ref ∈e store) (Actor.references actor)

-- An actor is valid in the context 'ls' iff:
-- There is an inbox of the right shape in 'ls'.
-- For every reference in the actor's list of references has an inbox of the right shape in 'ls'
record ValidActor (store : Store) (act : Actor) : Set₂ where
  field
    hasInb : hasInbox store act
    points : allPointersCorrect store act

inboxRightPointer : Store → Inbox → Set
inboxRightPointer store inb = Inbox.name inb ↦ Inbox.IS inb ∈e store

messageValid : ∀ {IS} → Store → NamedMessage IS → Set
messageValid store (Value _ _) = ⊤
messageValid store (Reference {Fw} _ name) = name ↦ Fw ∈e store

allMessagesValid : Store → Inbox → Set₁
allMessagesValid store inb = All (messageValid store) (Inbox.inb inb)

inboxToStoreEntry : Inbox → NamedInbox
inboxToStoreEntry inb = (Inbox.name inb) , (Inbox.IS inb)

inboxesToStore : List Inbox → Store
inboxesToStore = map inboxToStoreEntry

NameFresh : Store → ℕ → Set₁
NameFresh store n = All (λ v → Σ.proj₁ v Data.Nat.< n) store

-- The environment is a list of actors and inboxes, with a proof that every ector is valid in the context of said list of inboxes
--
-- What's missing here is a separation between actors that are running, and actors that are stuck.
-- An actor can become stuck if it is doing a receive but has no messages in its inbox.
-- Actors that become stuck by running to completion should instead just be discarded.
record Env : Set₂ where
  field
    acts : List Actor
    blocked : List Actor
    inbs : List Inbox
    store : Store
    inbs=store : store ≡ inboxesToStore inbs
    freshName : Name
    actorsValid : All (ValidActor store) acts
    blockedValid : All (ValidActor store) blocked
    messagesValid : All (allMessagesValid store) inbs
    nameIsFresh : NameFresh store freshName

-- The empty environment
emptyEnv : Env
emptyEnv = record
             { acts = []
             ; blocked = []
             ; inbs = []
             ; store = []
             ; inbs=store = refl
             ; freshName = 0
             ; actorsValid = []
             ; blockedValid = []
             ; messagesValid = []
             ; nameIsFresh = []
             }

-- An environment containing a single actor.
-- The actor can't have any known references
singletonEnv : ∀ {IS A ce} → ActorM IS A [] ce → Env
singletonEnv {IS} {A} {ce} actor = record
                       { acts = record
                                  { IS = IS
                                  ; A = A
                                  ; references = []
                                  ; es = []
                                  ; esEqRefs = refl
                                  ; ce = ce
                                  ; act = actor
                                  ; name = 0
                                  } ∷ []
                       ; blocked = []
                       ; inbs = record { IS = IS ; inb = [] ; name = 0 } ∷ []
                       ; store = (0 , IS) ∷ []
                       ; inbs=store = refl
                       ; freshName = 1
                       ; actorsValid = (record { hasInb = zero ; points = [] }) ∷ []
                       ; blockedValid = []
                       ; messagesValid = [] ∷ []
                       ; nameIsFresh = Data.Nat.s≤s Data.Nat.z≤n ∷ []
                       }
