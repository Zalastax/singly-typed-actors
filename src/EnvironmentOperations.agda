module EnvironmentOperations where
open import ActorMonad
open import SimulationEnvironment
open import Prelude

open import Data.List.All.Properties using (++⁺ ; drop⁺)
open import Data.List.Properties using (map-++-commute)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)

open Actor
open ValidActor
open Env
open NamedInbox
open NameSupplyStream

-- We can create a new Actor from an ActorM if we know its name.
-- This is used when spawning an actor.
new-actor : ∀ {IS A post} → ActorM ∞ IS A [] post → Name → Actor
new-actor {IS} {A} {post} m name = record
                                        { inbox-shape = IS
                                        ; A = A
                                        ; references = []
                                        ; pre = []
                                        ; pre-eq-refs = refl
                                        ; post = post
                                        ; computation = m ⟶ []
                                        ; name = name
                                        }


-- An actor can be lifted to run sub-programs that need less references
lift-actor : (actor : Actor) → {pre : TypingContext} →
             (references : Store) →
             (pre-eq-refs : (map shape references) ≡ pre) →
             ActorState ∞ (inbox-shape actor) (A actor) pre (post actor) →
             Actor
lift-actor actor {pre} references pre-eq-refs m = record
                                              { inbox-shape = inbox-shape actor
                                              ; A = actor .A
                                              ; references = references
                                              ; pre = pre
                                              ; pre-eq-refs = pre-eq-refs
                                              ; post = actor .post
                                              ; computation = m
                                              ; name = actor .name
                                              }

-- Replace the monadic part of an actor
-- Many of the bind-operations don't change anything except what the next step should be.
replace-actorM : (actor : Actor) → ActorState ∞ (inbox-shape actor) (A actor) (pre actor) (post actor) → Actor
replace-actorM actor m = record
                           { inbox-shape = inbox-shape actor
                           ; A = A actor
                           ; references = references actor
                           ; pre = pre actor
                           ; pre-eq-refs = pre-eq-refs actor
                           ; post = post actor
                           ; computation = m
                           ; name = name actor
                           }


-- Add one reference to an actor.
-- Used when receiving a reference, spawn, or self.
-- The precondition and references are equal via the congruence relation on consing the shape of the reference.
add-reference : (actor : Actor) → (nm : NamedInbox) → ActorState ∞ (inbox-shape actor) (A actor) (shape nm ∷ pre actor) (post actor) → Actor
add-reference actor nm m = record
                             { inbox-shape = inbox-shape actor
                             ; A = A actor
                             ; references = nm ∷ references actor
                             ; pre = shape nm ∷ pre actor
                             ; pre-eq-refs = cong (_∷_ (shape nm)) (pre-eq-refs actor)
                             ; post = post actor
                             ; computation = m
                             ; name = name actor
                             }

add-references-to-actor : (actor : Actor) → (nms : List NamedInbox) → ActorState ∞ (inbox-shape actor) (A actor) ((map shape nms) ++ pre actor) (post actor) → Actor
add-references-to-actor actor nms m = record
                                        { inbox-shape = inbox-shape actor
                                        ; A = A actor
                                        ; references = nms ++ references actor
                                        ; pre = map shape nms ++ pre actor
                                        ; pre-eq-refs = trans (map-++-commute shape nms (references actor)) (cong (_++_ (map shape nms)) (pre-eq-refs actor))
                                        ; post = post actor
                                        ; computation = m
                                        ; name = name actor
                                        }
add-references-rewrite : (actor : Actor) → (nms : List NamedInbox) → {x : Message (inbox-shape actor)} →
  map shape nms ++ pre actor ≡ add-references (pre actor) x →
  ActorState ∞ (inbox-shape actor) (A actor) (add-references (pre actor) x) (post actor) →
  Actor
add-references-rewrite actor nms {x} p m = record
                             { inbox-shape = inbox-shape actor
                             ; A = A actor
                             ; references = nms ++ references actor
                             ; pre = add-references (pre actor) x
                             ; pre-eq-refs = trans (trans (map-++-commute shape nms (references actor)) (cong (_++_ (map shape nms)) (pre-eq-refs actor))) p
                             ; post = post actor
                             ; computation = m
                             ; name = name actor
                             }

data SameValidityProof : Actor → Actor → Set₁ where
  AreSame :
    ∀ {A A' pre pre' post post'}
    {IS name references}
    {per per'}
    {computation computation'} →
    SameValidityProof
    (record
    { inbox-shape = IS
    ; A = A
    ; references = references
    ; pre = pre
    ; pre-eq-refs = per
    ; post = post
    ; computation = computation
    ; name = name
    })
    (record
    { inbox-shape = IS
    ; A = A'
    ; references = references
    ; pre = pre'
    ; pre-eq-refs = per'
    ; post = post'
    ; computation = computation'
    ; name = name
    })

-- A proof of an actor being valid is also valid for another actor if
-- * they have the same name
-- * they have the same references
-- * they have the same inbox type
rewrap-valid-actor : {store : Store} → {actorPre : Actor} → {actorPost : Actor} →
                     SameValidityProof actorPre actorPost →
                     ValidActor store actorPre →
                     ValidActor store actorPost
rewrap-valid-actor AreSame va = record { actor-has-inbox = va .actor-has-inbox ; references-have-pointer = va .references-have-pointer }

data ReferenceAdded (ref : NamedInbox) : Actor → Actor → Set₁ where
  RefAdded :
    ∀ {A A' pre pre' post post'}
    {IS name references}
    {per per'}
    {computation computation'} →
    ReferenceAdded ref
    (record
    { inbox-shape = IS
    ; A = A
    ; references = references
    ; pre = pre
    ; pre-eq-refs = per
    ; post = post
    ; computation = computation
    ; name = name
    })
    (record
    { inbox-shape = IS
    ; A = A'
    ; references = ref ∷ references
    ; pre = pre'
    ; pre-eq-refs = per'
    ; post = post'
    ; computation = computation'
    ; name = name
    })

add-reference-valid : {store : Store} → {actorPre : Actor} → {actorPost : Actor} →
                    {ref : NamedInbox} →
                    ReferenceAdded ref actorPre actorPost →
                    ValidActor store actorPre →
                    reference-has-pointer store ref →
                    ValidActor store actorPost
add-reference-valid RefAdded va p = record { actor-has-inbox = va .actor-has-inbox ; references-have-pointer = p ∷ (va .references-have-pointer) }

record ValidMessageList (store : Store) (S : InboxShape) : Set₁ where
  field
    inbox : Inbox S
    valid : All (message-valid store) inbox

InboxUpdater : (store : Store) (IS : InboxShape) → Set₁
InboxUpdater store IS = ValidMessageList store IS → ValidMessageList store IS

record UpdatedInbox (store : Store) {store' : Store} (original : Inboxes store') (name : Name) : Set₂ where
  field
    updated-inboxes : Inboxes store'
    inboxes-valid : InboxesValid store updated-inboxes
    others-unaffected : ∀ {name' IS' inb} → ¬ name ≡ name' → {p' : name' ↦ IS' ∈e store'} → InboxForPointer inb store' original p' → InboxForPointer inb store' updated-inboxes p'


open ValidMessageList
open UpdatedInbox
open NameSupply

-- Update one of the inboxes in a list of inboxes.
-- All the inboxes have been proven to be valid in the context of a store,
-- and the goal is to return a new list of inboxes which are also valid for the same store.
-- We know what inbox to update via an index using the inbox name into the list.
-- The update function receives both a list of messages from the inbox we pointed out,
-- and a proof that all the messages are valid for the store.
-- The update function returns a new list of the same type,
-- and has to provide a proof that this list is also valid for the store
update-inbox : {name : Name} → {IS : InboxShape} →
  (store : Store) →
  {store' : Store} →
  (inboxes : Inboxes store') →
  (InboxesValid store inboxes) →
  (name ↦ IS ∈e store') →
  (f : InboxUpdater store IS) →
  UpdatedInbox store inboxes name
update-inbox _ _ [] () _
update-inbox {name} store {store'} (x ∷ inboxes) (px ∷ proofs) zero f =
  record { updated-inboxes = inbox updated ∷ inboxes ; inboxes-valid = (valid updated) ∷ proofs ; others-unaffected = unaffected }
  where
    updated = (f (record { inbox = x ; valid = px }))
    unaffected : ∀ {name' IS' inb} → ¬ name ≡ name' → {p' : name' ↦ IS' ∈e store'} → InboxForPointer inb store' (x ∷ inboxes) p' → InboxForPointer inb store' (inbox updated ∷ inboxes) p'
    unaffected pr zero = ⊥-elim (pr refl)
    unaffected pr (suc ifp) = suc ifp
update-inbox {name} store {store'} (x ∷ inboxes) (px ∷ proofs) (suc p) f =
  record { updated-inboxes = x ∷ updated-inboxes updated ; inboxes-valid = px ∷ inboxes-valid updated ; others-unaffected = unaffected }
  where
    updated = (update-inbox store inboxes proofs p f)
    unaffected : ∀ {name' IS' inb} → ¬ name ≡ name' → {p' : name' ↦ IS' ∈e store'} → InboxForPointer inb store' (x ∷ inboxes) p' → InboxForPointer inb store' (x ∷ updated-inboxes updated) p'
    unaffected pr  zero = zero
    unaffected pr (suc ifp) = suc (others-unaffected updated pr ifp)

-- Move the actor that is at the top of the list, to the back of the list
-- This is done to create a round-robin system for the actors, since run-env always picks the actor at the top
-- Uses the insight that the order of the inboxes soes not correspond to the order of the Actors,
-- and that moving an actor to the back doesn't change any of the proofs about actors being valid.
top-actor-to-back : Env → Env
top-actor-to-back env with (acts env) | (actors-valid env)
top-actor-to-back env | [] | _ = env
top-actor-to-back env | x ∷ acts | (y ∷ prfs) = record
                             { acts = acts ++  [ x ]ˡ
                             ; blocked = blocked env
                             ; env-inboxes = env-inboxes env
                             ; store = store env
                             ; actors-valid = ++⁺ prfs [ y ]ᵃ
                             ; blocked-valid = blocked-valid env
                             ; messages-valid = messages-valid env
                             ; name-supply = name-supply env
                             ; blocked-no-progress = blocked-no-progress env
                             }

-- An actor is still valid if we add a new inbox to the store, as long as that name is not used in the store before
valid-actor-suc : ∀ {store actor IS} → (ns : NameSupply store) → ValidActor store actor → ValidActor (inbox# ns .name [ IS ] ∷ store) actor
valid-actor-suc ns va =
  let open ValidActor
      open _comp↦_∈_
  in record {
    actor-has-inbox = suc {pr = ns .name-is-fresh (actor-has-inbox va)} (actor-has-inbox va)
    ; references-have-pointer = ∀map (λ p → suc-p (ns .name-is-fresh (actual-has-pointer p)) p) (references-have-pointer va)
    }

valid-references-suc : ∀ {store references IS} →
                     (ns : NameSupply store) →
                     All (reference-has-pointer store) references →
                     All (reference-has-pointer (inbox# (ns .name) [ IS ] ∷ store)) references
valid-references-suc ns pointers =
  let open _comp↦_∈_
  in ∀map (λ p → suc-p (ns .name-is-fresh (actual-has-pointer p)) p) pointers

-- All the messages in an inbox are still valid if we add a new inbox to the store, as long as that name is not used in the store before
messages-valid-suc : ∀ {store IS x} {inb : Inbox IS} → (ns : NameSupply store) → all-messages-valid store inb → all-messages-valid (inbox# ns .name [ x ] ∷ store) inb
messages-valid-suc {store} {IS} {x} ns [] = []
messages-valid-suc {store} {IS} {x} {nx ∷ _} ns (px ∷ vi) = message-valid-suc nx px ∷ (messages-valid-suc ns vi)
  where
    open _comp↦_∈_
    fields-valid-suc : ∀ {MT} {fields : All named-field-content MT} →
      FieldsHavePointer store fields →
      FieldsHavePointer (inbox# ns .name [ x ] ∷ store) fields
    fields-valid-suc [] = []
    fields-valid-suc (FhpV ∷ valid) = FhpV ∷ fields-valid-suc valid
    fields-valid-suc (FhpR x ∷ valid) = FhpR (suc-p (ns .name-is-fresh (actual-has-pointer x)) x) ∷ (fields-valid-suc valid)
    message-valid-suc : (nx : NamedMessage IS) → message-valid store nx → message-valid (inbox# ns .name [ x ] ∷ store) nx
    message-valid-suc (NamedM x₁ x₂) px = fields-valid-suc px

is-blocked-suc : ∀ {store actor IS} {inbs : Inboxes store} {inb : Inbox IS} → (ns : NameSupply store) → IsBlocked store inbs actor → IsBlocked (inbox# ns .name [ IS ] ∷ store) (inb ∷ inbs) actor
is-blocked-suc ns (BlockedReturn at-return no-cont) = BlockedReturn at-return no-cont
is-blocked-suc ns (BlockedReceive at-receive p inbox-for-pointer) = BlockedReceive at-receive (suc {pr = ns .name-is-fresh p} p) (suc inbox-for-pointer)

-- Add a new actor to the environment.
-- The actor is added to the top of the list of actors.
add-top : ∀ {IS A post} → ActorState ∞ IS A [] post → Env → Env
add-top {IS} {A} {post} m env = record
                 { acts = record
                        { inbox-shape = IS
                        ; A = A
                        ; references = []
                        ; pre = []
                        ; pre-eq-refs = refl
                        ; post = post
                        ; computation = m
                        ; name = env .name-supply .supply .name
                        } ∷ acts env
                   ; blocked = blocked env
                   ; env-inboxes = [] ∷ env-inboxes env
                   ; store = inbox# env .name-supply .supply .name [ IS ] ∷ store env
                   ; actors-valid = record { actor-has-inbox = zero ; references-have-pointer = [] } ∷ ∀map (valid-actor-suc (env .name-supply .supply)) (actors-valid env)
                   ; blocked-valid = ∀map (valid-actor-suc (env .name-supply .supply)) (blocked-valid env)
                   ; messages-valid = [] ∷ map-suc (store env) (messages-valid env) (env .name-supply .supply)
                   ; name-supply = env .name-supply .next IS
                   ; blocked-no-progress = ∀map (is-blocked-suc (env .name-supply .supply)) (env .blocked-no-progress)
                   }
  where
    -- ad-hoc ∀map, because we are not using All here
    map-suc : (store : Store) → {store' : Store} → {inbs : Inboxes store'} → InboxesValid store inbs → (ns : NameSupply store) → InboxesValid (inbox# ns .name [ IS ] ∷ store) inbs
    map-suc store [] _ = []
    map-suc store (x ∷ valid) ns = messages-valid-suc ns x ∷ (map-suc store valid ns)



record GetInbox (store : Store) {store' : Store} (inboxes : Inboxes store') {name : Name} {S : InboxShape} (p : name ↦ S ∈e store') : Set₂ where
  field
    messages : Inbox S
    valid : all-messages-valid store messages
    right-inbox : InboxForPointer messages store' inboxes p

data InboxState : Set where
  Empty NonEmpty : InboxState

data InboxInState {S : InboxShape} : InboxState → Inbox S → Set₁ where
  IsEmpty : InboxInState Empty []
  HasMessage : {nm : NamedMessage S} {rest : Inbox S} → InboxInState NonEmpty (nm ∷ rest)

-- Get the messages of an inbox pointed to in the environment.
-- This is just a simple lookup into the list of inboxes.
get-inbox : ∀ {name IS} → (env : Env) → (p : name ↦ IS ∈e (store env)) → GetInbox (env .store) (env .env-inboxes) p
get-inbox env point = loop (env-inboxes env) (messages-valid env) point
  where
    loop : {store store' : Store} → (inbs : Inboxes store') → InboxesValid store inbs → ∀ {name IS} → (p : name ↦ IS ∈e store') → GetInbox store inbs p
    loop _ [] ()
    loop (x ∷ _) (px ∷ _) zero = record { messages = x ; valid = px ; right-inbox = zero }
    loop (_ ∷ inbs) (_ ∷ inb-valid) (suc point) =
      let rec = loop inbs inb-valid point
          open GetInbox
      in record { messages = rec .messages ; valid = rec .valid ; right-inbox = suc (rec .right-inbox) }

open GetInbox

record UnblockedActors {store store' : Store} {original : Inboxes store'} {n : Name} (updated : UpdatedInbox store original n) : Set₂ where
  field
    unblocked : List Actor
    unblocked-updated : All (λ act → n ≡ name act) unblocked
    unblocked-valid : All (ValidActor store) unblocked
    still-blocked : List Actor
    blocked-no-prog : All (IsBlocked store' (updated-inboxes updated)) still-blocked
    blocked-valid : All (ValidActor store) still-blocked

open UnblockedActors

unblock-actors :
  {store : Store} →
  {original : Inboxes store} →
  {n : Name} →
  (updated : UpdatedInbox store original n) →
  (blocked : List Actor) →
  All (ValidActor store) blocked →
  All (IsBlocked store original) blocked →
  UnblockedActors updated
unblock-actors updated [] [] [] = record
                                            { unblocked = []
                                            ; unblocked-updated = []
                                            ; unblocked-valid = []
                                            ; still-blocked = []
                                            ; blocked-no-prog = []
                                            ; blocked-valid = []
                                            }
unblock-actors {store} {original} {n} updated (x ∷ blckd) (v ∷ blckd-valid) (ib ∷ is-blocked) with (n ≟ (name x))
... | yes p =
  let rec = unblock-actors updated blckd blckd-valid is-blocked
  in record
       { unblocked = x ∷ rec .unblocked
       ; unblocked-updated = p ∷ rec .unblocked-updated
       ; unblocked-valid = v ∷ rec .unblocked-valid
       ; still-blocked = rec .still-blocked
       ; blocked-no-prog = rec .blocked-no-prog
       ; blocked-valid = rec .blocked-valid
       }
... | no ¬p =
  let rec = unblock-actors updated blckd blckd-valid is-blocked
  in record
       { unblocked = rec .unblocked
       ; unblocked-updated = rec .unblocked-updated
       ; unblocked-valid = rec .unblocked-valid
       ; still-blocked = x ∷ rec .still-blocked
       ; blocked-no-prog = blocked-unaffected ib ∷ rec .blocked-no-prog
       ; blocked-valid = v ∷ rec .blocked-valid
       }
    where
      blocked-unaffected : IsBlocked store original x → IsBlocked store (updated-inboxes updated) x
      blocked-unaffected (BlockedReturn x y) = BlockedReturn x y
      blocked-unaffected (BlockedReceive x p y) = BlockedReceive x p (others-unaffected updated ¬p y)

update-inbox-env : ∀ {name IS} → (env : Env) → name ↦ IS ∈e (store env) →
                 (f : ValidMessageList (store env) IS → ValidMessageList (store env) IS) → Env
update-inbox-env {name} {IS} env p f =
  let
    updated = update-inbox (store env) (env-inboxes env) (messages-valid env) p f
    unblock-split = unblock-actors updated (blocked env) (blocked-valid env) (blocked-no-progress env)
  in record {
    acts = (unblocked unblock-split) ++ acts env
    ; blocked = still-blocked unblock-split
    ; env-inboxes = updated-inboxes updated
    ; store = store env
    ; actors-valid = ++⁺ (unblock-split .unblocked-valid) (env .actors-valid)
    ; blocked-valid = unblock-split .blocked-valid
    ; messages-valid = inboxes-valid updated
    ; name-supply = env .name-supply
    ; blocked-no-progress = unblock-split .blocked-no-prog
    }

record FoundReference (store : Store) (S : InboxShape) : Set₂ where
  field
    name : Name
    reference : name comp↦ S ∈ store

lookup-reference : ∀ {store ToIS} → (pre : TypingContext) → (refs : List NamedInbox) → All (reference-has-pointer store) refs → map shape refs ≡ pre → ToIS ∈ pre → FoundReference store ToIS
lookup-reference [] refs prfs eq ()
lookup-reference (x ∷ pre₁) [] prfs () Z
lookup-reference (x ∷ pre₁) [] prfs () (S px)
lookup-reference _ (inbox# name [ shape ] ∷ refs) (reference ∷ prfs) refl Z = record { name = name ; reference = reference }
lookup-reference _ (_ ∷ refs) (_ ∷ prfs) refl (S px) = lookup-reference _ refs prfs refl px

-- looks up the pointer for one of the references known by an actor
lookup-reference-act : ∀ {store actor ToIS} → ValidActor store actor → ToIS ∈ (pre actor) → FoundReference store ToIS
lookup-reference-act {store} {actor} {ToIS} va ref = lookup-reference (pre actor) (Actor.references actor) (ValidActor.references-have-pointer va) (pre-eq-refs actor) ref



open _comp↦_∈_
open FoundReference

-- Extract the found pointer
underlying-pointer : ∀ {IS store} → (ref : FoundReference store IS) → (name ref ↦ actual (reference ref) ∈e store )
underlying-pointer ref = actual-has-pointer (reference ref)

translate-message-pointer : ∀ {ToIS A store} →
  (w : FoundReference store ToIS) →
  A ∈ ToIS →
  A ∈ (actual (reference w))
translate-message-pointer w x = translate-⊆ (actual-handles-wanted (reference w)) x

record LiftedReferences (lss gss : TypingContext) (references : List NamedInbox) : Set₂ where
  field
    subset-inbox : lss ⊆ gss
    contained : List NamedInbox
    subset : contained ⊆ references
    contained-eq-inboxes : map shape contained ≡ lss

open LiftedReferences

-- Convert a subset for preconditions to a subset for references
lift-references : ∀ {lss gss} → lss ⊆ gss → (references : List NamedInbox) → map shape references ≡ gss → LiftedReferences lss gss references
lift-references [] refs refl = record {
  subset-inbox = []
  ; contained = []
  ; subset = []
  ; contained-eq-inboxes = refl
  }
lift-references (_∷_ {y} {xs} x₁ subs) refs refl with (lift-references subs refs refl)
... | q  = record {
  subset-inbox = x₁ ∷ subs
  ; contained = contained-el ∷ contained q
  ; subset = (translate-∈ x₁ refs shape refl) ∷ (subset q)
  ; contained-eq-inboxes = combine contained-el-shape y (map shape (contained q)) xs (sym contained-el-ok) (contained-eq-inboxes q)
  }
  where
    contained-el : NamedInbox
    contained-el = lookup-parallel x₁ refs shape refl
    contained-el-shape = shape contained-el
    contained-el-ok : y ≡ contained-el-shape
    contained-el-ok = lookup-parallel-≡ x₁ refs shape refl
    combine : (a b : InboxShape) → (as bs : TypingContext) → (a ≡ b) → (as ≡ bs) → (a ∷ as ≡ b ∷ bs)
    combine a .a as .as refl refl = refl

data LiftActor : Actor → Actor → Set₂ where
  CanBeLifted :
    ∀ {A A' post post'}
    {IS name references}
    {lss gss}
    {per}
    {computation computation'} →
    (lr : LiftedReferences lss gss references) →
    LiftActor
    (record
    { inbox-shape = IS
    ; A = A
    ; references = references
    ; pre = gss
    ; pre-eq-refs = per
    ; post = post
    ; computation = computation
    ; name = name
    })
    (record
    { inbox-shape = IS
    ; A = A'
    ; references = lr .contained
    ; pre = lss
    ; pre-eq-refs = lr .contained-eq-inboxes
    ; post = post'
    ; computation = computation'
    ; name = name
    })

lift-valid-actor : ∀ {store} {act act' : Actor} →
                   LiftActor act act' →
                   ValidActor store act →
                   ValidActor store act'
lift-valid-actor (CanBeLifted lr) va =
  record {
    actor-has-inbox = va .actor-has-inbox
    ; references-have-pointer = All-⊆ (lr .subset) (va .references-have-pointer)
    }



-- We can replace the actors in an environment if they all are valid for the current store.
replace-actors : (env : Env) → (actors : List Actor) → All (ValidActor (store env)) actors → Env
replace-actors env actors actorsValid = record {
  acts = actors
  ; blocked = env .blocked
  ; env-inboxes = env .env-inboxes
  ; store = env .store
  ; actors-valid = actorsValid
  ; blocked-valid = env .blocked-valid
  ; messages-valid = env .messages-valid
  ; name-supply = env .name-supply
  ; blocked-no-progress = env .blocked-no-progress
  }

replace-focused : {act : Actor} → (env : Env) → Focus act env →
                  (act' : Actor) →
                  (valid' : ValidActor (env .store) act') →
                  Env
replace-focused env@record {
  acts = _ ∷ rest
  ; actors-valid = _ ∷ rest-valid
  } Focused act' valid' =
  replace-actors env (act' ∷ rest) (valid' ∷ rest-valid)

block-focused : {act : Actor} → (env : Env) → Focus act env → IsBlocked (env .store) (env .env-inboxes) act → Env
block-focused env@record {
  acts = actor ∷ rest
  ; blocked = blocked
  ; actors-valid = actor-valid ∷ rest-valid
  ; blocked-valid = blocked-valid
  } Focused blckd = record {
  acts = rest
  ; blocked = actor ∷ blocked
  ; store = env .store
  ; env-inboxes = env .env-inboxes
  ; name-supply = env .name-supply
  ; actors-valid = rest-valid
  ; blocked-valid = actor-valid ∷ blocked-valid
  ; messages-valid = env .messages-valid
  ; blocked-no-progress = blckd ∷ env .blocked-no-progress
  }

-- Takes a named message and a proof that the named message is valid for the store.
-- Values are valid for any store and references need a proof that the pointer is valid.
add-message : {S : InboxShape} → {store : Store} → (message : NamedMessage S) → message-valid store message → (ValidMessageList store S → ValidMessageList store S)
add-message message valid vml = record {
  inbox = inbox vml ++ [ message ]ˡ
  ; valid = ++⁺ (ValidMessageList.valid vml) [ valid ]ᵃ
  }

-- Removes the next message from an inbox.
-- This is a no-op if there are no messages in the inbox.
remove-message : {S : InboxShape} → {store : Store} → (ValidMessageList store S → ValidMessageList store S)
remove-message vml = record { inbox = drop 1 (inbox vml) ; valid = drop⁺ 1 (ValidMessageList.valid vml) }

name-fields : ∀ {MT store} → (pre : TypingContext) →
               (refs : List NamedInbox) →
               All (reference-has-pointer store) refs →
               All (send-field-content pre) MT →
               map shape refs ≡ pre →
               All named-field-content MT
name-fields pre refs rhp [] eq = []
name-fields _ refs rhp (_∷_ {ValueType x} (lift lower) sfc) refl = lower ∷ (name-fields _ refs rhp sfc refl)
name-fields {store = store} _ refs rhp (_∷_ {ReferenceType x} px sfc) refl = name (lookup-reference _ refs rhp refl (_⊢>:_.actual-is-sendable px)) ∷ (name-fields _ refs rhp sfc refl)

name-fields-act : ∀ {MT} store → ∀ actor →
              All (send-field-content (pre actor)) MT →
              ValidActor store actor → All named-field-content MT
name-fields-act store actor sfc valid = name-fields (pre actor) (Actor.references actor) (references-have-pointer valid) sfc (pre-eq-refs actor)

unname-field : ∀ {x} → named-field-content x → receive-field-content x
unname-field {ValueType x₁} nfc = nfc
unname-field {ReferenceType x₁} nfc = _

extract-inboxes : ∀ {MT} → All named-field-content MT → List NamedInbox
extract-inboxes [] = []
extract-inboxes (_∷_ {ValueType _} _ ps) = extract-inboxes ps
extract-inboxes (_∷_ {ReferenceType x} name ps) = inbox# name [ x ] ∷ extract-inboxes ps

named-inboxes : ∀ {S} → (nm : NamedMessage S) → List NamedInbox
named-inboxes (NamedM x x₁) = extract-inboxes x₁

reference-names : {MT : MessageType} → All named-field-content MT → List Name
reference-names [] = []
reference-names (_∷_ {ValueType x} px ps) = reference-names ps
reference-names (_∷_ {ReferenceType x} name ps) = name ∷ reference-names ps

++-diff : (a b c : List InboxShape) → a ≡ b → a ++ c ≡ b ++ c
++-diff [] .[] c refl = refl
++-diff (x ∷ a) .(x ∷ a) c refl = refl

add-references++ : ∀ {S store} → (nm : NamedMessage S) → message-valid store nm → ∀ w → map shape (named-inboxes nm) ++ w ≡ add-references w (unname-message nm)
add-references++ msg@(NamedM {MT} x x₁) p w = halp (add-fields++ MT x₁)
  where
    halp : map shape (extract-inboxes x₁) ≡ extract-references MT → map shape (extract-inboxes x₁) ++ w ≡ extract-references MT ++ w
    halp p = ++-diff (map shape (extract-inboxes x₁)) (extract-references MT) w p
    add-fields++ : ∀ MT → (x₁ : All named-field-content MT) → map shape (extract-inboxes x₁) ≡ extract-references MT
    add-fields++ [] [] = refl
    add-fields++ (ValueType x ∷ MT) (px ∷ x₁) = add-fields++ MT x₁
    add-fields++ (ReferenceType x ∷ MT) (px ∷ x₁) = cong (_∷_ x) (add-fields++ MT x₁)

valid++ : ∀ {S store} → (nm : NamedMessage S) → message-valid store nm → ∀ {w} →
        All (reference-has-pointer store) w →
        All (reference-has-pointer store) (named-inboxes nm ++ w)
valid++ (NamedM x x₁) v = valid-fields v
  where
    valid-fields : ∀ {MT store} →
                   {fields : All named-field-content MT} →
                   FieldsHavePointer store fields → ∀ {p} →
                   All (reference-has-pointer store) p →
                   All (reference-has-pointer store) (extract-inboxes fields ++ p)
    valid-fields [] ps = ps
    valid-fields (FhpV ∷ fhp) ps = valid-fields fhp ps
    valid-fields (FhpR px ∷ fhp) ps = px ∷ (valid-fields fhp ps)

open _⊢>:_

compatible-handles : ∀ store x refs
                     (px : (map shape refs) ⊢>: x)
                     (w : FoundReference store (actual px)) →
                     x ⊆ actual (reference w)
compatible-handles store x refs px w =
  let a = actual-handles-requested px
      b = actual-handles-wanted (reference w)
  in ⊆-trans a b

make-pointer-compatible : ∀ store x refs
                       (px : (map shape refs) ⊢>: x) →
                       (All (reference-has-pointer store) refs) →
                       (w : FoundReference store (actual px)) →
                       name w comp↦ x ∈ store
make-pointer-compatible store x refs px rhp w = [p: actual-has-pointer (reference w) ][handles: compatible-handles store x refs px w ]

open FieldsHavePointer

make-pointers-compatible : ∀ {MT} store pre refs (eq : map shape refs ≡ pre)
                           (fields : All (send-field-content pre) MT)
                           (rhp : All (reference-has-pointer store) refs) →
                         FieldsHavePointer store (name-fields pre refs rhp fields eq)
make-pointers-compatible store pre refs eq [] rhp = []
make-pointers-compatible store _ refs refl (_∷_ {ValueType x} px fields) rhp = FhpV ∷ make-pointers-compatible store _ refs refl fields rhp
make-pointers-compatible store _ refs refl (_∷_ {ReferenceType x} px fields) rhp =
  let foundFw = lookup-reference _ refs rhp refl (actual-is-sendable px)
  in FhpR (make-pointer-compatible store x refs px rhp foundFw) ∷ (make-pointers-compatible store _ refs refl fields rhp)
