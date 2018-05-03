module SimulationEnvironment where
open import Membership using (_∈_ ; find-∈ ; _⊆_)
open import ActorMonad
open import NatProps

open import Data.List using (List ; _∷_ ; [] ; map)
open import Data.List.All using (All ; _∷_ ; [] ; lookup) renaming (map to ∀map)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; zero ; suc ; s≤s)
open import Data.Nat.Properties using (≤-reflexive ; ≤-step)
open import Data.Unit using (⊤ ; tt)

open import Level using (Lift ; lift)
open import Size using (Size ; Size<_ ; ↑_ ; ∞)

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

-- A pointer into the store.
-- This is a proof that the name points to an inbox shape in the store.
-- The store is a key-value list that returns the first value matching the key (name).
-- Indexing into the store is done by building the peano-number to the index of the element.
-- To create the successor you have to provide a proof that you're not going past the name
-- you're looking for.
data _↦_∈e_ (n : Name) (S : InboxShape) : Store → Set where
  zero : ∀ {xs}
         → n ↦ S ∈e (inbox# n [ S ] ∷ xs)
  suc  : ∀ {n' : Name} { S' xs} {pr : ¬ n ≡ n'}
         → n ↦ S ∈e xs
         → n ↦ S ∈e (inbox# n' [ S' ] ∷ xs)


record _comp↦_∈_ (n : Name) (wanted : InboxShape) (store : Store) : Set₁ where
  constructor [p:_][handles:_]
  field
    {actual} : InboxShape
    actual-has-pointer : n ↦ actual ∈e store
    actual-handles-wanted : wanted <: actual

Cont : ∀ (i : Size) (IS : InboxShape) {A B : Set₁}
            (pre : A → TypingContext)
            (post : B → TypingContext) →
            Set₂
Cont i IS {A} {B} pre post = (x : A) → ∞ActorM i IS B (pre x) post

data ContStack (i : Size) (IS : InboxShape) {A : Set₁} (pre : A → TypingContext) :
     ∀ {B : Set₁} (post : B → TypingContext) → Set₂ where
  []    : ContStack i IS pre pre
  _∷_   : ∀{B C}{mid : B → TypingContext} {post : C → TypingContext}
        → Cont i IS pre mid → ContStack i IS mid post → ContStack i IS pre post

record ActorState (i : Size) (IS : InboxShape) (C : Set₁) (pre : TypingContext) (post : C → TypingContext) : Set₂ where
  constructor _⟶_
  field
    {A}   : Set₁
    {mid} : A → TypingContext
    act   : ActorM i IS A pre mid
    cont  : ContStack i IS mid post

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
    computation : ActorState ∞ inbox-shape A pre post
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

unname-message : ∀ {S} → NamedMessage S → Message S
unname-message (NamedM x fields) = Msg x (do-the-work fields)
  where
    do-the-work : ∀ {MT} → All named-field-content MT → All receive-field-content MT
    do-the-work {[]} nfc = []
    do-the-work {ValueType x₁ ∷ MT} (px ∷ nfc) = px ∷ (do-the-work nfc)
    do-the-work {ReferenceType x₁ ∷ MT} (px ∷ nfc) = _ ∷ do-the-work nfc

Inbox : InboxShape → Set₁
Inbox is = List (NamedMessage is)

data Inboxes : (store : Store) → Set₁ where
  [] : Inboxes []
  _∷_ : ∀ {store name inbox-shape} → Inbox inbox-shape →
    (inboxes : Inboxes store) → Inboxes (inbox# name [ inbox-shape ] ∷ store)

data InboxForPointer {inbox-shape : InboxShape} (inbox : Inbox inbox-shape) {name : Name} : (store : Store) → (Inboxes store) → (name ↦ inbox-shape ∈e store) → Set₁ where
  zero : ∀ {store} {inbs : Inboxes store} →
         InboxForPointer inbox (inbox# name [ inbox-shape ] ∷ store) (inbox ∷ inbs) zero
  suc : ∀ {n' : Name} {S' inb' store} {p : name ↦ inbox-shape ∈e store} {inbs : Inboxes store} {pr : ¬ name ≡ n'} →
        InboxForPointer inbox store inbs p →
        InboxForPointer inbox (inbox# n' [ S' ] ∷ store) (inb' ∷ inbs) (suc {pr = pr} p)

-- Property that there exists an inbox of the right shape in the list of inboxes
-- This is used both for proving that every actor has an inbox,
-- and for proving that every reference known by an actor has an inbox
has-inbox : Store → Actor → Set
has-inbox store actor = Actor.name actor ↦ Actor.inbox-shape actor ∈e store


inbox-for-actor : ∀ {store} (inbs : Inboxes store) (actor : Actor) (p : has-inbox store actor) (inb : Inbox (Actor.inbox-shape actor)) → Set₁
inbox-for-actor {store} inbs actor p inb = InboxForPointer inb store inbs p

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

data FieldHasPointer (store : Store) : ∀ {f} → named-field-content f → Set₁ where
  FhpV : ∀ {A} {v : A} → FieldHasPointer store {ValueType A} v
  FhpR : ∀ {name Fw} → name comp↦ Fw ∈ store → FieldHasPointer store {ReferenceType Fw} name

data FieldsHavePointer (store : Store) : ∀ {MT} → All named-field-content MT → Set₁ where
  [] : FieldsHavePointer store []
  _∷_ : ∀ {F p MT} {nfc : All named-field-content MT} →
    FieldHasPointer store {F} p →
    FieldsHavePointer store nfc →
    FieldsHavePointer store {F ∷ MT} (p ∷ nfc)

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

-- If a name is fresh for a store (i.e. all names in the store are < than the name),
-- then none of the names in the store is equal to the name
Fresh¬≡ : ∀ {store name } → NameFresh store name → (All (λ m → ¬ (NamedInbox.name m) ≡ name) store)
Fresh¬≡ ls = ∀map (λ frsh → <-¬≡ frsh) ls

record NameSupply (store : Store) : Set₁ where
  field
    name : Name
    freshness-carrier : All (λ v → NamedInbox.name v < name) store
    name-is-fresh : {n : Name} {IS : InboxShape} → n ↦ IS ∈e store → ¬ n ≡ name

open NameSupply

record NameSupplyStream (i : Size) (store : Store) : Set₁ where
  coinductive
  field
    supply : NameSupply store
    next : (IS : InboxShape) → {j : Size< i} → NameSupplyStream j (inbox# supply .name [ IS ] ∷ store)


-- helps show that all the names in the store are still valid if we add a new name on top,
-- if the new name is > than all the names already in the store.
suc-helper : ∀ {store name IS n} →
             name ↦ IS ∈e store →
             All (λ v → suc (NamedInbox.name v) Data.Nat.≤ n) store →
             ¬ name ≡ n
suc-helper zero (px ∷ p) = <-¬≡ px
suc-helper (suc q) (px ∷ p) = suc-helper q p

suc-p : ∀ {store name n x shape} → ¬ name ≡ n → name comp↦ shape ∈ store → name comp↦ shape ∈ (inbox# n [ x ] ∷ store)
suc-p pr [p: actual-has-pointer ][handles: actual-handles-wanted ] = [p: (suc {pr = pr} actual-has-pointer) ][handles: actual-handles-wanted ]

open NameSupplyStream

next-name-supply : {store : Store} → (ns : NameSupply store) → (IS : InboxShape) → NameSupply (inbox# (ns .name) [ IS ] ∷ store)
next-name-supply ns IS = record {
  name = suc (ns .name)
  ; freshness-carrier = next-fresh
  ; name-is-fresh = λ p → suc-helper p next-fresh
  }
  where
    next-fresh = (s≤s (≤-reflexive refl)) ∷ ∀map ≤-step (ns .freshness-carrier)

name-supply-singleton : {i : Size} → NameSupplyStream i []
name-supply-singleton .supply = record {
  name = 0
  ; freshness-carrier = []
  ; name-is-fresh = λ { () }
  }
name-supply-singleton .next = stream-builder (name-supply-singleton .supply)
  where
    stream-builder : {i : Size} → {store : Store} → (ns : NameSupply store) → (IS : InboxShape) → {j : Size< i} → NameSupplyStream j (inbox# (ns .name) [ IS ] ∷ store)
    stream-builder ns IS .supply = next-name-supply ns IS
    stream-builder ns IS .next = stream-builder (next-name-supply ns IS)

data ActorConstructor : Set where
  Return : ActorConstructor
  Bind : ActorConstructor
  Spawn : ActorConstructor
  Send : ActorConstructor
  Receive : ActorConstructor
  Self : ActorConstructor
  Strengthen : ActorConstructor

data ActorAtConstructor : ActorConstructor → Actor → Set₂ where
  AtReturn :
    ∀ {IS A B refs mid post name}
    {cont : ContStack ∞ IS mid post}
    {v : A}
    {per} →
    ActorAtConstructor Return (record
      { inbox-shape = IS
      ; A = B
      ; references = refs
      ; pre = mid v
      ; pre-eq-refs = per
      ; post = post
      ; computation = Return v ⟶ cont
      ; name = name
      })
  AtBind :
    ∀ {IS A B C refs pre mid name}
    {m : ∞ActorM ∞ IS A pre mid}
    {post : B → TypingContext}
    {f : (x : A) →
    ∞ActorM ∞ IS B (mid x) post}
    {contpost : C → TypingContext}
    {cont : ContStack ∞ IS post contpost} →
    ∀ {per} →
    ActorAtConstructor Bind (record
      { inbox-shape = IS
      ; A = C
      ; references = refs
      ; pre = pre
      ; pre-eq-refs = per
      ; post = contpost
      ; computation = (m ∞>>= f) ⟶ cont
      ; name = name
      })
  AtSpawn :
    ∀ {IS NewIS A B refs pre post postN name}
    {m : ActorM ∞ NewIS A [] postN}
    {cont : ContStack ∞ IS (λ _ → NewIS ∷ pre) post}
    {per} →
    ActorAtConstructor Spawn (record
      { inbox-shape = IS
      ; A = B
      ; references = refs
      ; pre = pre
      ; pre-eq-refs = per
      ; post = post
      ; computation = Spawn m ⟶ cont
      ; name = name
      })
  AtSend :
    ∀ {IS ToIS A refs pre post name}
    {canSendTo : pre ⊢ ToIS}
    {msg : SendMessage ToIS pre}
    {cont : ContStack ∞ IS (λ _ → pre) post}
    {per} →
    ActorAtConstructor Send (record
      { inbox-shape = IS
      ; A = A
      ; references = refs
      ; pre = pre
      ; pre-eq-refs = per
      ; post = post
      ; computation = (Send canSendTo msg) ⟶ cont
      ; name = name
      })
  AtReceive :
    ∀ {IS A refs pre post name}
    {cont : ContStack ∞ IS (add-references pre) post}
    {per} →
    ActorAtConstructor Receive (record
      { inbox-shape = IS
      ; A = A
      ; references = refs
      ; pre = pre
      ; pre-eq-refs = per
      ; post = post
      ; computation = Receive ⟶ cont
      ; name = name
      })
  AtSelf :
    ∀ {IS A refs pre post name}
    {cont : ContStack ∞ IS (λ _ → IS ∷ pre) post}
    {per} →
    ActorAtConstructor Self (record
      { inbox-shape = IS
      ; A = A
      ; references = refs
      ; pre = pre
      ; pre-eq-refs = per
      ; post = post
      ; computation = Self ⟶ cont
      ; name = name
      })
  AtStrengthen :
    ∀ {IS A refs ys xs post name}
    {inc : ys ⊆ xs}
    {cont : ContStack ∞ IS (λ _ → ys) post}
    {per} →
    ActorAtConstructor Strengthen (record
      { inbox-shape = IS
      ; A = A
      ; references = refs
      ; pre = xs
      ; pre-eq-refs = per
      ; post = post
      ; computation = (Strengthen inc) ⟶ cont
      ; name = name
      })

data ActorHasContinuation : Actor → Set₂ where
  HasContinuation :
    ∀ {IS A B C refs pre mid contmid post name}
    {m : ActorM ∞ IS A pre mid}
    {f : Cont ∞ IS {A} {B} mid contmid}
    {cont : ContStack ∞ IS contmid post}
    {v : A}
    {per} →
    ActorHasContinuation (record
      { inbox-shape = IS
      ; A = C
      ; references = refs
      ; pre = pre
      ; pre-eq-refs = per
      ; post = post
      ; computation = m ⟶ (f ∷ cont)
      ; name = name
      })

data ActorHasNoContinuation : Actor → Set₂ where
  NoContinuation :
    ∀ {IS A refs pre post name}
    {m : ActorM ∞ IS A pre post}
    {v : A}
    {per} →
    ActorHasNoContinuation (record
      { inbox-shape = IS
      ; A = A
      ; references = refs
      ; pre = pre
      ; pre-eq-refs = per
      ; post = post
      ; computation = m ⟶ []
      ; name = name
      })

data IsBlocked (store : Store) (inbs : Inboxes store) (actor : Actor) : Set₂ where
  BlockedReturn :
    ActorAtConstructor Return actor →
    ActorHasNoContinuation actor →
    IsBlocked store inbs actor
  BlockedReceive :
    ActorAtConstructor Receive actor →
    (p : has-inbox store actor) →
    InboxForPointer [] store inbs p →
    IsBlocked store inbs actor

-- The environment is a list of actors and inboxes,
-- with a proof that every ector is valid in the context of said list of inboxes
record Env : Set₂ where
  field
    -- raw
    acts : List Actor
    blocked : List Actor
    store : Store
    env-inboxes : Inboxes store
    name-supply : NameSupplyStream ∞ store
    -- coherence
    actors-valid : All (ValidActor store) acts
    blocked-valid : All (ValidActor store) blocked
    messages-valid : InboxesValid store env-inboxes
    -- weak progress
    blocked-no-progress : All (IsBlocked store env-inboxes) blocked

-- The empty environment
empty-env : Env
empty-env = record
             { acts = []
             ; blocked = []
             ; env-inboxes = []
             ; store = []
             ; actors-valid = []
             ; blocked-valid = []
             ; messages-valid = []
             ; name-supply = name-supply-singleton
             ; blocked-no-progress = []
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
                                  ; computation = record { act = actor ; cont = [] }
                                  ; name = name-supply-singleton .supply .name
                                  } ∷ []
                       ; blocked = []
                       ; env-inboxes = [] ∷ []
                       ; store = inbox# 0 [ IS ] ∷ []
                       ; actors-valid = (record { actor-has-inbox = zero ; references-have-pointer = [] }) ∷ []
                       ; blocked-valid = []
                       ; messages-valid = [] ∷ []
                       ; name-supply = name-supply-singleton .next IS
                       ; blocked-no-progress = []
                       }


data Focus (act : Actor) : Env → Set₂ where
  Focused :
    {rest : List Actor}
    {bl : List Actor}
    {str : Store}
    {inbs : Inboxes str}
    {rv : All (ValidActor str) rest}
    {bv : All (ValidActor str) bl}
    {bib : All (IsBlocked str inbs) bl}
    {mv : InboxesValid str inbs}
    {ns : NameSupplyStream ∞ str}
    {va : ValidActor str act} →
    Focus act (record
      { acts = act ∷ rest
      ; blocked = bl
      ; store = str
      ; env-inboxes = inbs
      ; actors-valid = va ∷ rv
      ; blocked-valid = bv
      ; messages-valid = mv
      ; name-supply = ns
      ; blocked-no-progress = bib
      })

data Done : Env → Set₂ where
  AllBlocked :
    {bl : List Actor}
    {str : Store}
    {inbs : Inboxes str}
    {bv : All (ValidActor str) bl}
    {bib : All (IsBlocked str inbs) bl}
    {mv : InboxesValid str inbs}
    {ns : NameSupplyStream ∞ str} →
    Done (record
            { acts = []
            ; blocked = bl
            ; store = str
            ; env-inboxes = inbs
            ; name-supply = ns
            ; actors-valid = []
            ; blocked-valid = bv
            ; messages-valid = mv
            ; blocked-no-progress = bib
            })
