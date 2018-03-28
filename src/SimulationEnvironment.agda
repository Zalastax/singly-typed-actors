module SimulationEnvironment where
open import Membership using (_∈_ ; find-∈)
open import ActorMonad

open import Data.List using (List ; _∷_ ; [] ; map)
open import Data.List.All using (All ; _∷_ ; [] ; lookup) renaming (map to ∀map)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Nat using (ℕ ; _≟_)
open import Data.Unit using (⊤ ; tt)

open import Level using (Lift ; lift)
open import Size using (∞)

open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)
open import Relation.Unary using (Decidable) renaming (_⊆_ to _⋐_)

-- We give every actor and inbox a name.
-- The internal type of an actor is not important,
-- but the type needs to have an easy way of creating
-- new unique values and an easy way to prove that the name
-- is not already used.
-- For ℕ we can create new values using suc,
-- and can prove that it is unused by proving that every
-- previously used name is < than the new name.
Name = ℕ

-- Named inboxes are just an inbox shape and a name.
-- We use this representation to separate the shape of the store and
-- the actual storing of inboxes with messages.
record NamedInbox : Set₁ where
  constructor inbox#_[_]
  field
    name : Name
    shape : InboxShape

-- The store is a list of named inboxes.
-- This only describes the shape of the store and does not contain any messages.
-- Making this separation between the shape and the actual storing makes it less
-- cumbersome to prove that updating an inbox does not invalidate all the pointers into the store.
-- The store is basically just a key-value list.
-- The store does not stop you from inserting duplicate keys,
-- but doing so would invalidate the other pointers with that name,
-- meaning that you can only insert duplicate keys
-- if the value InboxShape is the same as the already stored value.
-- Inserting duplicate keys is thus pointless and is not done anywhere in the code.
Store = List NamedInbox

-- Decidable inequality
¬[_] : ∀ {a b : Name} → Dec (a ≡ b) → Set
¬[ (yes x₁) ] = ⊥
¬[ (no x₁) ] = ⊤

-- Also decidable inequality
_¬≡_ : ( a b : Name) → Set
a ¬≡ b = ¬[ a ≟ b ]

-- A pointer into the store.
-- This is a proof that the name points to an inbox shape in the store.
-- The store is a key-value list that returns the first value matching the key (name).
-- Indexing into the store is done by building the peano-number to the index of the element.
-- To create the successor you have to provide a proof that you're not going past the name
-- you're looking for.
data _↦_∈e_ (n : Name) (S : InboxShape) : Store → Set where
  zero : ∀ {xs}
         → n ↦ S ∈e (inbox# n [ S ] ∷ xs)
  suc  : ∀ {n' : Name} { S' xs} {pr : n ¬≡ n'}
         → n ↦ S ∈e xs
         → n ↦ S ∈e (inbox# n' [ S' ] ∷ xs)


record _comp↦_∈_ (n : Name) (wanted : InboxShape) (store : Store) : Set₁ where
  constructor [p:_][handles:_]
  field
    {actual} : InboxShape
    actual-has-pointer : n ↦ actual ∈e store
    actual-handles-wanted : wanted <: actual

-- An ActorM wrapped up with all of its parameters
-- We use this to be able to store actor monads of different types in the same list.
-- We give each actor a name so that we can find its inbox in the store.
record Actor : Set₂ where
  field
    inbox-shape : InboxShape
    A           : Set₁
    -- The references are just the preconditions with the name of the actor
    -- of that shape added.
    -- The references are used by the runtime to know which inbox corresponds to
    -- which shape, letting us know which inbox to update when a message is sent.
    references  : List NamedInbox
    pre         : TypingContext
    pre-eq-refs : (map NamedInbox.shape references) ≡ pre
    post        : A → TypingContext
    actor-m     : ActorM ∞ inbox-shape A pre post
    name        : Name

named-field-content : MessageField → Set
named-field-content (ValueType A) = A
named-field-content (ReferenceType Fw) = Name

-- We can look up which inbox a reference refers to when a message is sent.
-- We can however not add the reference to the actor immediately,
-- since the reference should only be added when the message is received.
-- By storing the name of the inbox being referenced we can know which inbox
-- is being referenced whenever the message is received.
--
-- The decision to use names for references and pointers, rather than just ∈,
-- makes it possible to prove that a sent message containing a reference
-- does not need to be modified when more actors are added.
data NamedMessage (To : InboxShape): Set₁ where
  NamedM : {MT : MessageType} → MT ∈ To → All named-field-content MT → NamedMessage To

Inbox : InboxShape → Set₁
Inbox is = List (NamedMessage is)

data Inboxes : (store : Store) → Set₁ where
  [] : Inboxes []
  _∷_ : ∀ {store name inbox-shape} → List (NamedMessage inbox-shape) →
    (inboxes : Inboxes store) → Inboxes (inbox# name [ inbox-shape ] ∷ store)

-- Property that there exists an inbox of the right shape in the list of inboxes
-- This is used both for proving that every actor has an inbox,
-- and for proving that every reference known by an actor has an inbox
has-inbox : Store → Actor → Set
has-inbox store actor = Actor.name actor ↦ Actor.inbox-shape actor ∈e store

reference-has-pointer : Store → NamedInbox → Set₁
reference-has-pointer store ni = name ni comp↦ shape ni ∈ store
  where open NamedInbox

-- Property that for every shape, there exists an inbox of that shape.
-- Used for proving that every reference known by an actor has an inbox.
all-references-have-a-pointer : Store → Actor → Set₁
all-references-have-a-pointer store actor = All (reference-has-pointer store) (Actor.references actor)
  where open NamedInbox

-- An actor is valid in the context 'store' iff:
-- There is an inbox of the right shape in 'store'.
-- For every reference in the actor's list of references has an inbox of the right shape in 'store'
record ValidActor (store : Store) (actor : Actor) : Set₂ where
  field
    actor-has-inbox : has-inbox store actor
    references-have-pointer : all-references-have-a-pointer store actor

data FieldsHavePointer (store : Store) : ∀ {MT} → All named-field-content MT → Set₁ where
  [] : FieldsHavePointer store []
  v+_ : ∀ {MT A} {v : A} {nfc : All named-field-content MT} →
    FieldsHavePointer store nfc →
    FieldsHavePointer store {ValueType A ∷ MT} (v ∷ nfc)
  _∷r_ : ∀ {name Fw MT} {nfc : All named-field-content MT} →
    name comp↦ Fw ∈ store →
    FieldsHavePointer store nfc →
    FieldsHavePointer store {ReferenceType Fw ∷ MT} (name ∷ nfc)

-- To limit references to only those that are valid for the current store,
-- we have to prove that name in the message points to an inbox of the same
-- type as the reference.
-- Value messages are not context sensitive.
message-valid : ∀ {IS} → Store → NamedMessage IS → Set₁
message-valid store (NamedM x x₁) = FieldsHavePointer store x₁

-- An inbox is valid in a store if all its messages are valid
all-messages-valid : ∀ {IS} → Store → Inbox IS → Set₁
all-messages-valid store = All (message-valid store)

infixr 5 _∷_

data InboxesValid (store : Store) : ∀ {store'} → Inboxes store' → Set₁ where
  [] : InboxesValid store []
  _∷_ : ∀ {store' name IS} {inboxes : Inboxes store'} {inbox : Inbox IS} →
    all-messages-valid store inbox →
    InboxesValid store inboxes →
    InboxesValid store {inbox# name [ IS ] ∷ store'} (inbox ∷ inboxes)

-- A name is unused in a store if every inbox has a name that is < than the name
NameFresh : Store → ℕ → Set₁
NameFresh store n = All (λ v → name v Data.Nat.< n) store
  where open NamedInbox

-- The environment is a list of actors and inboxes,
-- with a proof that every ector is valid in the context of said list of inboxes
record Env : Set₂ where
  field
    -- The currently active actors
    acts : List Actor
    -- The currently blocked actors, i.e. actors doing receive without any messages in its inbox.
    -- By separating blocked and non-blocked actors we both optimize the simulation to not try to run
    -- actors that won't succed in taking a step, and we get a clear step-condition when there are no
    -- non-blocked actors left.
    blocked : List Actor
    store : Store
    env-inboxes : Inboxes store
    -- The proofs that an actor and a blocked actor is valid is actually the same proof,
    -- but kept in a separate list.
    actors-valid : All (ValidActor store) acts
    blocked-valid : All (ValidActor store) blocked
    messages-valid : InboxesValid store env-inboxes
    -- In each environment we keep track of the next fresh name,
    -- and a proof that the name is not already used in the store.
    fresh-name : Name
    name-is-fresh : NameFresh store fresh-name

-- The empty environment
empty-env : Env
empty-env = record
             { acts = []
             ; blocked = []
             ; env-inboxes = []
             ; store = []
             ; fresh-name = 0
             ; actors-valid = []
             ; blocked-valid = []
             ; messages-valid = []
             ; name-is-fresh = []
             }

-- An environment containing a single actor.
-- The actor can't have any known references
singleton-env : ∀ {IS A post} → ActorM ∞ IS A [] post → Env
singleton-env {IS} {A} {post} actor = record
                       { acts = record
                                  { inbox-shape = IS
                                  ; A = A
                                  ; references = []
                                  ; pre = []
                                  ; pre-eq-refs = refl
                                  ; post = post
                                  ; actor-m = actor
                                  ; name = 0
                                  } ∷ []
                       ; blocked = []
                       ; env-inboxes = [] ∷ []
                       ; store = inbox# 0 [ IS ] ∷ []
                       ; fresh-name = 1
                       ; actors-valid = (record { actor-has-inbox = zero ; references-have-pointer = [] }) ∷ []
                       ; blocked-valid = []
                       ; messages-valid = [] ∷ []
                       ; name-is-fresh = Data.Nat.s≤s Data.Nat.z≤n ∷ []
                       }
