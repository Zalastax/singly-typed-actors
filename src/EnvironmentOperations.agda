{-# OPTIONS --allow-unsolved-metas #-}
module EnvironmentOperations where
open import ActorMonad
open import SimulationEnvironment
open import Membership using (_∈_ ; _⊆_)

open import Data.List using (List ; _∷_ ; [] ; map ; _++_ ; drop)
open import Data.List.All using (All ; _∷_ ; []; lookup) renaming (map to ∀map)
open import Data.List.All.Properties using (++⁺ ; drop⁺)
open import Data.List.Any using (here ; there)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Unit using (⊤ ; tt)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; trans)
open import Relation.Nullary using (Dec ; yes ; no)

open import Level using (Lift ; lift)

open Actor
open ValidActor
open Env
open NamedInbox

-- We can create a new Actor from an ActorM if we know its name.
-- This is used when spawning an actor.
new-actor : ∀ {IS A post} → ActorM IS A [] post → Name → Actor
new-actor {IS} {A} {post} m name = record
                                        { inbox-shape = IS
                                        ; A = A
                                        ; references = []
                                        ; pre = []
                                        ; pre-eq-refs = refl
                                        ; post = post
                                        ; actor-m = m
                                        ; name = name
                                        }

-- An actor can be lifted to run sub-programs that need less references
lift-actor : (actor : Actor) → {pre : List InboxShape} → (references : List NamedInbox) →
              (pre-eq-refs : (map shape references) ≡ pre) →
              ActorM (inbox-shape actor) (A actor) pre (post actor) → Actor
lift-actor actor {pre} references pre-eq-refs m = record
                                              { inbox-shape = inbox-shape actor
                                              ; A = A actor
                                              ; references = references
                                              ; pre = pre
                                              ; pre-eq-refs = pre-eq-refs
                                              ; post = post actor
                                              ; actor-m = m
                                              ; name = name actor
                                              }

-- Replace the monadic part of an actor
-- Many of the bind-operations don't change anything except what the next step should be.
replace-actorM : (actor : Actor) → ActorM (inbox-shape actor) (A actor) (pre actor) (post actor) → Actor
replace-actorM actor m = record
                           { inbox-shape = inbox-shape actor
                           ; A = A actor
                           ; references = references actor
                           ; pre = pre actor
                           ; pre-eq-refs = pre-eq-refs actor
                           ; post = post actor
                           ; actor-m = m
                           ; name = name actor
                           }

-- Add one reference to an actor.
-- Used when receiving a reference, spawn, or self.
-- The precondition and references are equal via the congruence relation on consing the shape of the reference.
add-reference : (actor : Actor) → (nm : NamedInbox) → ActorM (inbox-shape actor) (A actor) (shape nm ∷ pre actor) (post actor) → Actor
add-reference actor nm m = record
                             { inbox-shape = inbox-shape actor
                             ; A = A actor
                             ; references = nm ∷ references actor
                             ; pre = shape nm ∷ pre actor
                             ; pre-eq-refs = cong (_∷_ (shape nm)) (pre-eq-refs actor)
                             ; post = post actor
                             ; actor-m = m
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
    inbox : List (NamedMessage S)
    valid : All (message-valid store) inbox

record UpdatedInboxes (store : Store) (original : List Inbox) : Set₂ where
  field
    updated-inboxes : List Inbox
    inboxes-valid : All (all-messages-valid store) updated-inboxes
    same-store : inboxes-to-store original ≡ inboxes-to-store updated-inboxes

open ValidMessageList
open UpdatedInboxes

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
  (inboxes : List Inbox) →
  (All (all-messages-valid store) inboxes) →
  (name ↦ IS ∈e (inboxes-to-store inboxes)) →
  (f : ValidMessageList store IS → ValidMessageList store IS) →
  UpdatedInboxes store inboxes
update-inboxes store [] [] () f
update-inboxes store (x ∷ inboxes) (px ∷ proofs) zero f with (f (record { inbox = Inbox.inbox-messages x ; valid = px }))
... | updated = record {
  updated-inboxes = updatedInbox ∷ inboxes
  ; inboxes-valid = (valid updated) ∷ proofs
  ; same-store = refl }
  where
    updatedInbox : Inbox
    updatedInbox = record { inbox-shape = Inbox.inbox-shape x ; inbox-messages = inbox updated ; name = Inbox.name x }
update-inboxes store (x ∷ inboxes) (px ∷ proofs) (suc reference) f with (update-inboxes store inboxes proofs reference f)
... | updatedInboxes = record {
  updated-inboxes = x ∷ updated-inboxes updatedInboxes
  ; inboxes-valid = px ∷ inboxes-valid updatedInboxes
  ; same-store = cong (_∷_ inbox# (Inbox.name x) [ Inbox.inbox-shape x ]) (same-store updatedInboxes) }

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
                             ; inbs=store = inbs=store env
                             ; fresh-name = fresh-name env
                             ; actors-valid = ++⁺ prfs (y ∷ [])
                             ; blocked-valid = blocked-valid env
                             ; messages-valid = messages-valid env
                             ; name-is-fresh = name-is-fresh env
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
                                  ; inbs=store = inbs=store env
                                  ; fresh-name = fresh-name env
                                  ; actors-valid = prfs
                                  ; blocked-valid = blocked-valid env
                                  ; messages-valid = messages-valid env
                                  ; name-is-fresh = name-is-fresh env
                                  }

-- convert < to ¬≡
<-¬≡ : ∀ {n m} → n < m → n ¬≡ m
<-¬≡ {zero} {zero} ()
<-¬≡ {zero} {suc m} p = _
<-¬≡ {suc n} {zero} ()
<-¬≡ {suc n} {suc m} (Data.Nat.s≤s p) with (<-¬≡ p)
... | q with (n ≟ m)
<-¬≡ {suc n} {suc m} (Data.Nat.s≤s p) | () | yes p₁
<-¬≡ {suc n} {suc m} (Data.Nat.s≤s p) | q | no ¬p = _

-- If a name is fresh for a store (i.e. all names in the store are < than the name),
-- then none of the names in the store is equal to the name
Fresh¬≡ : ∀ {store name } → NameFresh store name → (All (λ m → (NamedInbox.name m) ¬≡ name) store)
Fresh¬≡ ls = ∀map (λ frsh → <-¬≡ frsh) ls

-- helps show that all the names in the store are still valid if we add a new name on top,
-- if the new name is > than all the names already in the store.
suc-helper : ∀ {store name IS n} →
            name ↦ IS ∈e store →
            All (λ v → suc (NamedInbox.name v) Data.Nat.≤ n) store →
            ¬[ name ≟ n ]
suc-helper zero (px ∷ p) = <-¬≡ px
suc-helper (suc q) (px ∷ p) = suc-helper q p

-- An actor is still valid if we add a new inbox to the store, as long as that name is not used in the store before
valid-actor-suc : ∀ {store actor n x} → (NameFresh store n) → ValidActor store actor → ValidActor (inbox# n [ x ] ∷ store) actor
valid-actor-suc frsh va = record { actor-has-inbox = suc {pr = suc-helper (ValidActor.actor-has-inbox va) frsh} (ValidActor.actor-has-inbox va) ; references-have-pointer = ∀map (λ p → suc {pr = suc-helper p frsh} p) (ValidActor.references-have-pointer va) }

-- All the messages in an inbox are still valid if we add a new inbox to the store, as long as that name is not used in the store before
messages-valid-suc : ∀ {store inb n x} → (NameFresh store n) → all-messages-valid store inb → all-messages-valid (inbox# n [ x ] ∷ store) inb
messages-valid-suc {store} {inb} {n} {x} frsh vi = ∀map msgValidSuc vi
  where
    msgValidSuc : {x₁ : NamedMessage (Inbox.inbox-shape inb)} →
                  message-valid store x₁ → message-valid (inbox# n [ x ] ∷ store) x₁
    msgValidSuc {x₁ = Value _ _} mv = tt
    msgValidSuc {x₁ = Reference _ _} mv = suc {pr = suc-helper mv frsh} mv

-- Add a new actor to the environment.
-- The actor is added to the top of the list of actors.
add-top : ∀ {IS A post} → ActorM IS A [] post → Env → Env
add-top {IS} {A} {post} actor-m env = record
                                 { acts = record
                                            { inbox-shape = IS
                                            ; A = A
                                            ; references = []
                                            ; pre = []
                                            ; pre-eq-refs = refl
                                            ; post = post
                                            ; actor-m = actor-m
                                            ; name = fresh-name env
                                            } ∷ acts env
                                 ; blocked = blocked env
                                 ; env-inboxes = record { inbox-shape = IS ; inbox-messages = [] ; name = fresh-name env } ∷ env-inboxes env
                                 ; store = inbox# fresh-name env [ IS ] ∷ store env
                                 ; inbs=store = cong (_∷_ inbox# fresh-name env [ IS ]) (inbs=store env)
                                 ; fresh-name = suc (fresh-name env)
                                 ; actors-valid = record { actor-has-inbox = zero ; references-have-pointer = [] } ∷ ∀map (valid-actor-suc (name-is-fresh env)) (actors-valid env)
                                 ; blocked-valid = ∀map (valid-actor-suc (name-is-fresh env)) (blocked-valid env)
                                 ; messages-valid = [] ∷ ∀map (λ {x} vi → messages-valid-suc {_} {x} (name-is-fresh env) vi) (messages-valid env)
                                 ; name-is-fresh = Data.Nat.s≤s (≤-reflexive refl) ∷ ∀map  Data.Nat.Properties.≤-step (name-is-fresh env)
                                 }

record GetInbox (store : Store) (S : InboxShape) : Set₂ where
  field
    messages : List (NamedMessage S)
    valid : All (message-valid store) messages

-- Get the messages of an inbox pointed to in the environment.
-- This is just a simple lookup into the list of inboxes.
get-inbox : ∀ {name IS} → (env : Env) → name ↦ IS ∈e (store env) → GetInbox (store env) IS
get-inbox env point = loop (env-inboxes env) (messages-valid env) (fix-the-point point (inbs=store env))
  where
    fix-the-point : ∀ {name IS} → name ↦ IS ∈e store env → store env ≡ inboxes-to-store (env-inboxes env) → name ↦ IS ∈e inboxes-to-store (env-inboxes env)
    fix-the-point p refl = p
    loop : ∀ {name IS} → (inboxes : List Inbox) → All (all-messages-valid (store env)) inboxes → name ↦ IS ∈e (inboxes-to-store inboxes) → GetInbox (store env) IS
    loop [] [] ()
    loop (x ∷ _) (px ∷ prfs) zero = record { messages = Inbox.inbox-messages x ; valid = px }
    loop (_ ∷ inboxes) (_ ∷ prfs) (suc point) = loop inboxes prfs point

-- Updates an inbox in the environment
-- Just a wrapper arround 'updateInboxes'
update-inbox-env : ∀ {name IS} → (env : Env) → name ↦ IS ∈e (store env) →
                 (f : ValidMessageList (store env) IS → ValidMessageList (store env) IS) → Env
update-inbox-env {name} {IS} env p f = record
                           { acts = acts env
                           ; blocked = blocked env
                           ; env-inboxes = updated-inboxes updatedInboxes
                           ; store = store env
                           ; inbs=store = trans (inbs=store env) (same-store updatedInboxes)
                           ; fresh-name = fresh-name env
                           ; actors-valid = actors-valid env
                           ; blocked-valid = blocked-valid env
                           ; messages-valid = inboxes-valid updatedInboxes
                           ; name-is-fresh = name-is-fresh env
                           }
  where
    -- Just some helpers to align the types
    pp : name ↦ IS ∈e (inboxes-to-store (env-inboxes env))
    pp rewrite (inbs=store env) = p
    updatedInboxes = update-inboxes (store env) (env-inboxes env) (messages-valid env) pp f

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
                                                             ; inbs=store = inbs=store env
                                                             ; fresh-name = fresh-name env
                                                             ; actors-valid = ++⁺ (actors-valid env) unblockedValid
                                                             ; blocked-valid = baValid
                                                             ; messages-valid = messages-valid env
                                                             ; name-is-fresh = name-is-fresh env
                                                             }

record FoundReference (store : Store) (S : InboxShape) : Set₂ where
  field
    name : Name
    reference : name ↦ S ∈e store

-- looks up the pointer for one of the references known by an actor
lookup-reference : ∀ {store actor ToIS} → ValidActor store actor → ToIS ∈ (pre actor) → FoundReference store ToIS
lookup-reference {store} {actor} {ToIS} va ref = loop (pre actor) (Actor.references actor) (ValidActor.references-have-pointer va) (pre-eq-refs actor) ref
  where
    loop : (pre : List InboxShape) → (refs : List NamedInbox) → (All (λ ni → name ni ↦ shape ni ∈e store) refs) → (map shape refs ≡ pre) → ToIS ∈ pre → FoundReference store ToIS
    loop .[] [] prfs refl ()
    loop _ (inbox# name [ IS ] ∷ refs) (reference ∷ prfs) refl (here refl) = record { name = name ; reference = reference }
    loop _ (x ∷ refs) (px ∷ prfs) refl (there ref) = loop _ refs prfs refl ref

record LiftedReferences (lss gss : List InboxShape) (references : List NamedInbox) : Set₂ where
  field
    subset-inbox : lss ⊆ gss
    contained : List NamedInbox
    subset : contained ⊆ references
    contained-eq-inboxes : lss ≡ map shape contained

open LiftedReferences

-- Convert a subset for preconditions to a subset for references
lift-references : ∀ {lss gss} → lss ⊆ gss → (references : List NamedInbox) → map shape references ≡ gss → LiftedReferences lss gss references
lift-references = {!!}
{- lift-references [] [] refl = record
                               { subset-inbox = []
                               ; contained = []
                               ; subset = []
                               ; contained-eq-inboxes = refl
                               }
lift-references (keep subs) [] ()
lift-references (skip subs) [] ()
lift-references [] (x ∷ references₁) refl = record
                                              { subset-inbox = []
                                              ; contained = []
                                              ; subset = []
                                              ; contained-eq-inboxes = refl
                                              }
lift-references (keep subs) (x ∷ references) refl with (lift-references subs references refl)
... | lifted = record
                 { subset-inbox = keep subs
                 ; contained = x ∷ contained lifted
                 ; subset = keep (subset lifted)
                 ; contained-eq-inboxes = cong (_∷_ (shape x)) (contained-eq-inboxes lifted)
                 }
lift-references (skip subs) (x ∷ references) refl with (lift-references subs references refl)
... | lifted = record
                 { subset-inbox = skip subs
                 ; contained = contained lifted
                 ; subset = skip (subset lifted)
                 ; contained-eq-inboxes = contained-eq-inboxes lifted
                 }-}

-- We can replace the actors in an environment if they all are valid for the current store.
replace-actors : (env : Env) → (actors : List Actor) → All (ValidActor (store env)) actors → Env
replace-actors env actors actorsValid = record {
  acts = actors
  ; blocked = blocked env
  ; env-inboxes = env-inboxes env
  ; store = store env
  ; inbs=store = inbs=store env
  ; fresh-name = fresh-name env
  ; actors-valid = actorsValid
  ; blocked-valid = blocked-valid env
  ; messages-valid = messages-valid env
  ; name-is-fresh = name-is-fresh env
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
  ; inbs=store = inbs=store env
  ; fresh-name = fresh-name env
  ; actors-valid = actorsValid
  ; blocked-valid = blockedValid
  ; messages-valid = messages-valid env
  ; name-is-fresh = name-is-fresh env
  }

-- Takes a named message and a proof that the named message is valid for the store.
-- Values are valid for any store and references need a proof that the pointer is valid.
add-message : {S : InboxShape} → {store : Store} → (message : NamedMessage S) → message-valid store message → (ValidMessageList store S → ValidMessageList store S)
add-message message valid vml = record { inbox = inbox vml ++ (message ∷ []) ; valid = ++⁺ (ValidMessageList.valid vml) (valid ∷ []) }

-- Removes the next message from an inbox.
-- This is a no-op if there are no messages in the inbox.
remove-message : {S : InboxShape} → {store : Store} → (ValidMessageList store S → ValidMessageList store S)
remove-message vml = record { inbox = drop 1 (inbox vml) ; valid = drop⁺ 1 (ValidMessageList.valid vml) }
