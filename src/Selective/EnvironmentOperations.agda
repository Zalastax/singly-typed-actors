module Selective.EnvironmentOperations where
open import Selective.ActorMonad
open import Selective.SimulationEnvironment
open import Membership using (_∈_ ; _⊆_ ; [] ; _∷_ ; Z ; S ; lookup-parallel ; lookup-parallel-≡ ; translate-∈ ; x∈[]-⊥ ; translate-⊆ ; ⊆-trans ; find-∈)

open import Data.List using (List ; _∷_ ; [] ; map ; _++_ ; drop)
open import Data.List.All using (All ; _∷_ ; []; lookup) renaming (map to ∀map)
open import Data.List.All.Properties using (++⁺ ; drop⁺)
open import Data.List.Properties using (map-++-commute)
open import Data.List.Any using (Any ; here ; there)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Bool using (Bool ; true ; false)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; cong₂ ; trans ; inspect ; [_])
open import Relation.Nullary using (Dec ; yes ; no)

open import Level using (Level ; Lift ; lift) renaming (suc to lsuc)
open import Size using (∞)

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
                                              ; A = A actor
                                              ; references = references
                                              ; pre = pre
                                              ; pre-eq-refs = pre-eq-refs
                                              ; post = post actor
                                              ; computation = m
                                              ; name = name actor
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

-- A proof of an actor being valid is also valid for another actor if
-- * they have the same name
-- * they have the same references
-- * they have the same inbox type
rewrap-valid-actor : {store : Store} → {actorPre : Actor} → {actorPost : Actor} →
                     ValidActor store actorPre →
                     (name actorPre) ≡ (name actorPost) →
                     (references actorPre) ≡ (references actorPost) →
                     (inbox-shape actorPre) ≡ (inbox-shape actorPost) →
                     ValidActor store actorPost
rewrap-valid-actor va refl refl refl = record { actor-has-inbox = actor-has-inbox va
                                                         ; references-have-pointer = references-have-pointer va }

record ValidMessageList (store : Store) (S : InboxShape) : Set₁ where
  field
    inbox : Inbox S
    valid : All (message-valid store) inbox

record UpdatedInboxes (store : Store)  {store' : Store} (original : Inboxes store') : Set₂ where
  field
    updated-inboxes : Inboxes store'
    inboxes-valid : InboxesValid store updated-inboxes

open ValidMessageList
open UpdatedInboxes
open NameSupply

-- Update one of the inboxes in a list of inboxes.
-- All the inboxes have been proven to be valid in the context of a store,
-- and the goal is to return a new list of inboxes which are also valid for the same store.
-- We know what inbox to update via an index using the inbox name into the list.
-- The update function receives both a list of messages from the inbox we pointed out,
-- and a proof that all the messages are valid for the store.
-- The update function returns a new list of the same type,
-- and has to provide a proof that this list is also valid for the store
update-inboxes : {name : Name} → {IS : InboxShape} →
  (store : Store) →
  {store' : Store} → (inboxes : Inboxes store') →
  (InboxesValid store inboxes) →
  (name ↦ IS ∈e store') →
  (f : ValidMessageList store IS → ValidMessageList store IS) →
  UpdatedInboxes store inboxes
update-inboxes _ _ [] () _
update-inboxes store (x ∷ inboxes) (px ∷ proofs) zero f with (f (record { inbox = x ; valid = px }))
... | updated = record { updated-inboxes = (inbox updated) ∷ inboxes ; inboxes-valid = (valid updated) ∷ proofs }
update-inboxes store (x ∷ inboxes) (px ∷ proofs) (suc p) f with (update-inboxes store inboxes proofs p f)
... | updated = record { updated-inboxes = x ∷ updated-inboxes updated ; inboxes-valid = px ∷ (inboxes-valid updated) }

-- Move the actor that is at the top of the list, to the back of the list
-- This is done to create a round-robin system for the actors, since run-env always picks the actor at the top
-- Uses the insight that the order of the inboxes soes not correspond to the order of the Actors,
-- and that moving an actor to the back doesn't change any of the proofs about actors being valid.
top-actor-to-back : Env → Env
top-actor-to-back env with (acts env) | (actors-valid env)
top-actor-to-back env | [] | _ = env
top-actor-to-back env | x ∷ acts | (y ∷ prfs) = record
                             { acts = acts Data.List.++ x ∷ []
                             ; blocked = blocked env
                             ; env-inboxes = env-inboxes env
                             ; store = store env
                             ; actors-valid = ++⁺ prfs (y ∷ [])
                             ; blocked-valid = blocked-valid env
                             ; messages-valid = messages-valid env
                             ; name-supply = name-supply env
                             }

-- Drop the actor that is at the top of the list completely.
-- This is used when handling some monadic operations, when there is no following bind.
-- The dropped actor is not put in the blocked list.
drop-top-actor : Env → Env
drop-top-actor env with (acts env) | (actors-valid env)
drop-top-actor env | [] | prfs = env
drop-top-actor env | _ ∷ rest | _ ∷ prfs = record
                                  { acts = rest
                                  ; blocked = blocked env
                                  ; env-inboxes = env-inboxes env
                                  ; store = store env
                                  ; actors-valid = prfs
                                  ; blocked-valid = blocked-valid env
                                  ; messages-valid = messages-valid env
                                  ; name-supply = name-supply env
                                  }

-- An actor is still valid if we add a new inbox to the store, as long as that name is not used in the store before
valid-actor-suc : ∀ {store actor IS} → (ns : NameSupply store) → ValidActor store actor → ValidActor (inbox# ns .name [ IS ] ∷ store) actor
valid-actor-suc ns va = record {
  actor-has-inbox = suc {pr = ns .name-is-fresh (actor-has-inbox va)} (actor-has-inbox va)
  ; references-have-pointer = ∀map (λ p → suc-p (ns .name-is-fresh (actual-has-pointer p)) p) (references-have-pointer va)
  }
  where
    open ValidActor
    open _comp↦_∈_

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
                   }
  where
    map-suc : (store : Store) → {store' : Store} → {inbs : Inboxes store'} → InboxesValid store inbs → (ns : NameSupply store) → InboxesValid (inbox# ns .name [ IS ] ∷ store) inbs
    map-suc store [] _ = []
    map-suc store (x ∷ valid) ns = messages-valid-suc ns x ∷ (map-suc store valid ns)

record GetInbox (store : Store) (S : InboxShape) : Set₂ where
  field
    messages : Inbox S
    valid : all-messages-valid store messages

-- Get the messages of an inbox pointed to in the environment.
-- This is just a simple lookup into the list of inboxes.
get-inbox : ∀ {name IS} → (env : Env) → name ↦ IS ∈e (store env) → GetInbox (store env) IS
get-inbox env point = loop (env-inboxes env) (messages-valid env) point
  where
    loop : {store store' : Store} → (inbs : Inboxes store') → InboxesValid store inbs → ∀ {name IS} → name ↦ IS ∈e store' → GetInbox store IS
    loop _ [] ()
    loop (x ∷ _) (px ∷ _) zero = record { messages = x ; valid = px }
    loop (_ ∷ inbs) (_ ∷ valid) (suc point) = loop inbs valid point

-- Updates an inbox in the environment
-- Just a wrapper arround 'updateInboxes'
update-inbox-env : ∀ {name IS} → (env : Env) → name ↦ IS ∈e (store env) →
                 (f : ValidMessageList (store env) IS → ValidMessageList (store env) IS) → Env
update-inbox-env {name} {IS} env p f = record
                           { acts = acts env
                           ; blocked = blocked env
                           ; env-inboxes = updated-inboxes updated
                           ; store = store env
                           ; actors-valid = actors-valid env
                           ; blocked-valid = blocked-valid env
                           ; messages-valid = inboxes-valid updated
                           ; name-supply = env .name-supply
                           }
  where
    updated = update-inboxes (store env) (env-inboxes env) (messages-valid env) p f

-- Move an actor from the blocked list to the actors list.
-- Simply looks through the names of all blocked actors and moves those (should be just 1 or 0) with the same name.
-- IF an actor still doesn't have a way to progress (should never happen),
-- it will just get added back to the blocked list the next time it is processed.
unblock-actor : Env → Name → Env
unblock-actor env name = newEnv (loop (blocked env) (blocked-valid env))
  where
    loop : (blocked : List Actor) → (blockedValid : All (ValidActor (store env)) blocked) →
           (Σ[ blockedAfter ∈ List Actor ] All (ValidActor (store env)) blockedAfter) × (Σ[ unblocked ∈ List Actor ] All (ValidActor (store env)) unblocked)
    loop [] [] = ([] , []) , ([] , [])
    loop (x ∷ blocked) (px ∷ blockedValid) with (loop blocked blockedValid)
    ... | (blockedAfter , baValid) , unblocked , unblockedValid with (Actor.name x ≟ name)
    ... | yes p = (blockedAfter , baValid) , ((x ∷ unblocked) , px ∷ unblockedValid)
    ... | no ¬p = ((x ∷ blockedAfter) , (px ∷ baValid)) , unblocked , unblockedValid
    newEnv : Σ (Σ (List Actor) (All (ValidActor (store env))))
               (λ _ → Σ (List Actor) (All (ValidActor (store env)))) → Env
    newEnv ((ba , baValid) , unblocked , unblockedValid) = record
                                                             { acts = acts env ++ unblocked
                                                             ; blocked = ba
                                                             ; env-inboxes = env-inboxes env
                                                             ; store = store env
                                                             ; actors-valid = ++⁺ (actors-valid env) unblockedValid
                                                             ; blocked-valid = baValid
                                                             ; messages-valid = messages-valid env
                                                             ; name-supply = env .name-supply
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
    contained-eq-inboxes : lss ≡ map shape contained

open LiftedReferences

-- Convert a subset for preconditions to a subset for references
lift-references : ∀ {lss gss} → lss ⊆ gss → (references : List NamedInbox) → map shape references ≡ gss → LiftedReferences lss gss references
lift-references [] refs refl = record
                                     { subset-inbox = []
                                     ; contained = []
                                     ; subset = []
                                     ; contained-eq-inboxes = refl
                                     }
lift-references (_∷_ {y} {xs} x₁ subs) refs refl with (lift-references subs refs refl)
... | q  = record
                                             { subset-inbox = x₁ ∷ subs
                                             ; contained = (lookup-parallel x₁ refs shape refl) ∷ contained q
                                             ; subset = (translate-∈ x₁ refs shape refl) ∷ (subset q)
                                             ; contained-eq-inboxes = combine y (shape (lookup-parallel x₁ refs shape refl)) xs (map shape (contained q)) contained-el-ok (contained-eq-inboxes q)
                                             }
  where
    contained-el : NamedInbox
    contained-el = lookup-parallel x₁ refs shape refl
    contained-el-shape = shape contained-el
    contained-el-ok : y ≡ contained-el-shape
    contained-el-ok = lookup-parallel-≡ x₁ refs shape refl
    combine : (a b : InboxShape) → (as bs : TypingContext) → (a ≡ b) → (as ≡ bs) → (a ∷ as ≡ b ∷ bs)
    combine a .a as .as refl refl = refl

-- We can replace the actors in an environment if they all are valid for the current store.
replace-actors : (env : Env) → (actors : List Actor) → All (ValidActor (store env)) actors → Env
replace-actors env actors actorsValid = record {
  acts = actors
  ; blocked = blocked env
  ; env-inboxes = env-inboxes env
  ; store = store env
  ; actors-valid = actorsValid
  ; blocked-valid = blocked-valid env
  ; messages-valid = messages-valid env
  ; name-supply = env .name-supply
  }

-- We can replace both the running and blocked actors in an environment if they all are valid for the current store.
replace-actors+blocked : (env : Env) →
                          (actors : List Actor) → All (ValidActor (store env)) actors →
                          (blocked : List Actor) → All (ValidActor (store env)) blocked → Env
replace-actors+blocked env actors actorsValid blocked blockedValid = record {
  acts = actors
  ; blocked = blocked
  ; env-inboxes = env-inboxes env
  ; store = store env
  ; actors-valid = actorsValid
  ; blocked-valid = blockedValid
  ; messages-valid = messages-valid env
  ; name-supply = env .name-supply
  }

-- Takes a named message and a proof that the named message is valid for the store.
-- Values are valid for any store and references need a proof that the pointer is valid.
add-message : {S : InboxShape} → {store : Store} → (message : NamedMessage S) → message-valid store message → (ValidMessageList store S → ValidMessageList store S)
add-message message valid vml = record { inbox = inbox vml ++ (message ∷ []) ; valid = ++⁺ (ValidMessageList.valid vml) (valid ∷ []) }

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

unname-message : ∀ {S} → NamedMessage S → Message S
unname-message (NamedM x fields) = Msg x (do-the-work fields)
  where
    do-the-work : ∀ {MT} → All named-field-content MT → All receive-field-content MT
    do-the-work {[]} nfc = []
    do-the-work {ValueType x₁ ∷ MT} (px ∷ nfc) = px ∷ (do-the-work nfc)
    do-the-work {ReferenceType x₁ ∷ MT} (px ∷ nfc) = _ ∷ do-the-work nfc

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
compatible-handles store x refs px w with (actual-handles-requested px)
... | a with (actual-handles-wanted (reference w))
... | b = ⊆-trans a b

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
make-pointers-compatible store _ refs refl (_∷_ {ReferenceType x} px fields) rhp = FhpR (make-pointer-compatible store x refs px rhp foundFw) ∷ (make-pointers-compatible store _ refs refl fields rhp)
  where
    foundFw : FoundReference store (actual px)
    foundFw = lookup-reference _ refs rhp refl (actual-is-sendable px)

record SplitList {a : Level} {A : Set a} (ls : List A) : Set (lsuc a) where
  field
    heads : List A
    el : A
    tails : List A
    is-ls : (heads) ++ (el ∷ tails) ≡ ls

data FoundInList {a : Level} {A : Set a} (ls : List A) (f : A → Bool) : Set (lsuc a) where
  Found : (split : SplitList ls) → (f (SplitList.el split) ≡ true) → FoundInList ls f
  Nothing : FoundInList ls f

find-split : {a : Level} {A : Set a} (ls : List A) (f : A → Bool) → FoundInList ls f
find-split [] f = Nothing
find-split (x ∷ ls) f with (f x) | (inspect f x)
... | false | p = add-x (find-split ls f)
  where
    add-x : FoundInList ls f → FoundInList (x ∷ ls) f
    add-x (Found split x₁) = Found (record { heads = x ∷ heads split ; el = el split ; tails = tails split ; is-ls = cong (_∷_ x) (is-ls split) }) x₁
      where open SplitList
    add-x Nothing = Nothing
... | true | [ eq ] = Found (record { heads = [] ; el = x ; tails = ls ; is-ls = refl }) eq

-- Removes the next message from an inbox.
-- This is a no-op if there are no messages in the inbox.
remove-found-message : {S : InboxShape} → {store : Store} → (filter : MessageFilter S) → (ValidMessageList store S → ValidMessageList store S)
remove-found-message f record { inbox = [] ; valid = [] } = record { inbox = [] ; valid = [] }
remove-found-message {s} {store} f record { inbox = (x ∷ inbox₁) ; valid = vx ∷ valid₁ } with (f (unname-message x))
... | false = add-x (remove-found-message f (record { inbox = inbox₁ ; valid = valid₁ }))
  where
    add-x : ValidMessageList store s → ValidMessageList store s
    add-x record { inbox = inbox ; valid = valid } = record { inbox = x ∷ inbox ; valid = vx ∷ valid }
... | true = record { inbox = inbox₁ ; valid = valid₁ }

split-all-el : ∀ {a p} {A : Set a} {P : A → Set p} (ls : List A) → All P ls → (sl : SplitList ls) → (P (SplitList.el sl))
split-all-el [] ps record { heads = [] ; el = el ; tails = tails ; is-ls = () }
split-all-el [] ps record { heads = (x ∷ heads) ; el = el ; tails = tails ; is-ls = () }
split-all-el (x ∷ ls) (px ∷ ps) record { heads = [] ; el = .x ; tails = .ls ; is-ls = refl } = px
split-all-el (x ∷ ls) (px ∷ ps) record { heads = (x₁ ∷ heads) ; el = el ; tails = tails ; is-ls = refl } =
  split-all-el ls ps (record { heads = heads ; el = el ; tails = tails ; is-ls = refl })
