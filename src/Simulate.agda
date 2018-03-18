module Simulate where

open import Membership using (_∈_ ; _⊆_ ; All-⊆ ; translate-⊆ ; ⊆-refl)
open import ActorMonad public
open import SimulationEnvironment
open import EnvironmentOperations

open import Data.Colist using (Colist ; [] ; _∷_)
open import Data.List using (List ; _∷_ ; [] ; map ; _++_)
open import Data.List.All using (All ; _∷_ ; [] ; lookup) renaming (map to ∀map)
open import Data.List.All.Properties using (++⁺)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_ ; s≤s)
open import Data.Nat.Properties using (≤-reflexive ; ≤-step)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; trans)

open import Level using (Lift ; lift) renaming (suc to lsuc ; zero to lzero)
open import Coinduction using (∞ ; ♯_ ; ♭)

data ReceiveKind : Set where
  Nothing : ReceiveKind
  Value : List Name → ReceiveKind
  Dropped : ReceiveKind

data Trace : Set where
  Return : Name → Trace
  Bind : Trace → Trace
  BindDouble : Name → Trace -- If we encounter a bind and then a bind again...
  Spawn : (spawner : Name) → (spawned : Name) → Trace
  Send : (sender : Name) → (receiver : Name) → (references : List Name) → Trace
  Receive : Name → ReceiveKind → Trace
  TLift : Name → Trace
  Self : Name → Trace

-- A step in the simulation is the next environment paired up with what step was taken
record EnvStep : Set₂ where
  field
    env : Env
    trace : Trace

private
  keep-simulating : Trace → Env → Colist EnvStep

open Actor
open ValidActor
open Env
open FoundReference
open LiftedReferences
open UpdatedInboxes
open ValidMessageList
open NamedInbox
open _comp↦_∈_

-- Simulates the actors running in parallel by making one step of one actor at a time.
-- The actor that was run is put in the back of the queue unless it became blocked.
-- A simulation can possibly be infinite, and is thus modelled as an infinite list.
--
-- The simulation function is structured by pattern matching on every constructor of ActorM
-- for the top-most actor.
-- The behaviour of one step depends on whether there is a step coming after or if this is the
-- last step for the actor, so for every constructor we need to handle the case of when the
-- constructor is used in a bind or separately.
simulate : Env → Colist EnvStep
simulate env with (acts env) | (actors-valid env)
-- ===== OUT OF ACTORS =====
simulate env | [] | _ = []
simulate env | actor ∷ rest | _ with (actor-m actor)
-- ===== Return =====
-- If an actor returns a value but there is nothing that follows,
-- then the actor is done and we can drop it from the list of actors.
simulate env | actor ∷ rest | _ |
  Return val = keep-simulating (Return (name actor)) (drop-top-actor env)
-- ===== Bind =====
simulate env | actor ∷ rest | _ | m >>= f with (♭ m)
-- ===== Bind Value =====
-- return v >>= f ≡ f v, via the left identity monad law
-- We keep simulating, with the monadic part of the actor replaced by the value of f applied to v.
-- Recall that the precondition of a return is the same as the postcondition,
-- so the available references does not change.
simulate env | actor@(_) ∷ rest | valid ∷ restValid | m >>= f |
  Return val = keep-simulating (Bind (Return (name actor))) env'
  where
    bindAct : Actor
    bindAct = replace-actorM actor (♭ (f val))
    env' : Env
    env' = replace-actors env (bindAct ∷ rest) (rewrap-valid-actor valid refl refl refl ∷ restValid)
-- ===== Bind Bind =====
-- (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g) via the associativity monad law.
-- We need to use the associativity law to 'free' the left-most part so that
-- it can be run just one step.
-- The simulation will keep shifting parantheses until it eventually reaches
-- a part that is not a bind inside a bind.
simulate env | actor@(_) ∷ rest | valid ∷ restValid | m >>= g |
  mm >>= f = keep-simulating (Bind (BindDouble (name actor))) env'
  where
    bindAct : Actor
    bindAct = replace-actorM actor (mm >>= λ x → ♯ (f x >>= g))
    env' : Env
    env' = replace-actors env (bindAct ∷ rest) (rewrap-valid-actor valid refl refl refl ∷ restValid)
-- ===== Bind Spawn =====
-- Spawns a new actor and continues with (f tt).
-- Both the spawned actor and (f tt) are put at the back of the round-robin queue.
--
-- The new actor gets the next fresh name and the next env stores the fresh name that comes after that.
-- We prove that the next fresh env is unused via (m ≤ n → m ≤ 1 + n).
--
-- The new actor is added to the top of the store,
-- so we need to update every proof that states that a pointer into the store is valid.
-- Updating the proofs is an easy application of suc for _↦_∈e_ and <-¬≡.
--
-- In conclusion, the spawned actor is first added to the top of the round-robin queue
-- and then moved to the back.
simulate env | actor@(_) ∷ rest | valid ∷ restValid | m >>= f |
  Spawn {NewIS} {B} {_} {postN} bm = keep-simulating (Spawn (name actor) (fresh-name env)) (top-actor-to-back env')
  where
    newStoreEntry : NamedInbox
    newStoreEntry = inbox# fresh-name env [ NewIS ]
    newStore : Store
    newStore = newStoreEntry ∷ store env
    newInb : Inbox
    newInb = record { inbox-shape = NewIS ; inbox-messages = [] ; name = fresh-name env }
    newAct : Actor
    newAct = new-actor bm (fresh-name env)
    newActValid : ValidActor newStore newAct
    newActValid = record { actor-has-inbox = zero ; references-have-pointer = [] }
    newIsFresh : NameFresh newStore (suc (fresh-name env))
    newIsFresh = s≤s (≤-reflexive refl) ∷ ∀map ≤-step (name-is-fresh env)
    newInbs=newStore : store env ≡ inboxes-to-store (env-inboxes env) → newStore ≡ inboxes-to-store (newInb ∷ env-inboxes env)
    newInbs=newStore refl = refl
    bindAct : Actor
    bindAct = add-reference actor newStoreEntry (♭ (f _))
    bindActValid : ValidActor newStore bindAct
    bindActValid = record {
      actor-has-inbox = suc {pr =
        suc-helper (actor-has-inbox valid) (name-is-fresh env)
        } (actor-has-inbox valid)
      ; references-have-pointer = [p: zero ][handles: ⊆-refl ] ∷ ∀map
                                      (λ p → suc-p (suc-helper (actual-has-pointer p) (name-is-fresh env)) p)
                                      (references-have-pointer valid) }
    env' : Env
    env' = record
             { acts = newAct ∷ bindAct ∷ rest
             ; blocked = blocked env
             ; env-inboxes = newInb ∷ env-inboxes env
             ; store = newStore
             ; inbs=store = newInbs=newStore (inbs=store env)
             ; fresh-name = suc (fresh-name env)
             ; actors-valid = newActValid ∷ bindActValid ∷ ∀map (valid-actor-suc (name-is-fresh env)) restValid
             ; blocked-valid = ∀map (valid-actor-suc (name-is-fresh env)) (blocked-valid env)
             ; messages-valid = [] ∷ ∀map (λ {inb} mv → messages-valid-suc {_} {inb} (name-is-fresh env) mv) (messages-valid env)
             ; name-is-fresh = newIsFresh
             }
-- ===== Bind send reference =====
-- Spawns a reference message and continues with (f tt).
--
-- We find where to send the mesage using lookup-reference,
-- which just traverses the index into 'pre' to find which name / pointer
-- to use from 'references'.
-- We find which name / pointer is being forwarded in the same manner
-- and stores the name together with the message.
-- The found pointer is kept as a proof that we can find the referenced inbox
-- in the store, and the pointer proof is updated whenever the store is updated.
-- Updating the proof is not doing any actual useful work,
-- but we still can't make the proof irrelevant, since we would then need to use a
-- lookup function whenever we dereference a pointer.
--
-- add-message takes a named message and a proof that the named message is valid.
--
-- Sending a message to an actor that is blocked,
-- unblocks it and moves it to the actor queue.
-- The unblocked actor is put in the back of the round-robin queue.
simulate env | actor@(_) ∷ rest | valid ∷ restValid | m >>= f |
  Send {ToIS = ToIS} canSendTo (SendM p fields) = keep-simulating (Bind (Send (name actor) (name foundTo) (reference-names namedFields))) withUnblocked
  where
    foundTo : FoundReference (store env) ToIS
    foundTo = lookup-reference-act valid canSendTo
    namedFields = name-fields-act (store env) actor fields valid
    bindAct : Actor
    bindAct = replace-actorM actor (♭ (f _))
    withM : Env
    withM = replace-actors env (bindAct ∷ rest) (rewrap-valid-actor valid refl refl refl ∷ restValid)
    withUpdatedInbox : Env
    withUpdatedInbox = update-inbox-env withM (underlying-pointer foundTo) (
      add-message (NamedM (translate-message-pointer foundTo p) namedFields)
                          (make-pointers-compatible (store env) (pre actor) (references actor) (pre-eq-refs actor) fields (references-have-pointer valid)))
    withUnblocked : Env
    withUnblocked = unblock-actor withUpdatedInbox (name foundTo)
-- ===== Bind receive =====
-- Receives a message and continues with (f (receivedMessage)) if there is a message in the inbox.
-- The actor is put into the blocked list if the inbox is empty.
--
-- We find the pointer to the actors inbox in the store via (actor-has-inbox valid).
-- We always remove the received message from the inbox (and do nothing if there is no message),
-- but also pattern match on what the next message is, to figure out the right behaviour:
-- * An empty inbox just moves the actor to the blocked list,
--   where it will stay until a message is sent to it.
-- * If the next message is a value, just continue with (f message)
-- * If the next message is a reference,
--   take the proof that the message is valid and use that to prove that the added reference is valid.
simulate env | actor@(_) ∷ rest | valid ∷ restValid | m >>= f |
  Receive = keep-simulating (Bind (Receive (name actor) (receiveKind (GetInbox.messages actorsInbox)))) (env' actorsInbox)
  where
    actorsInbox : GetInbox (store env) (inbox-shape actor)
    actorsInbox = get-inbox env (actor-has-inbox valid)
    actorsPointer : (inboxes-to-store (env-inboxes env) ≡ store env) → (name actor) ↦ (inbox-shape actor) ∈e inboxes-to-store (env-inboxes env)
    actorsPointer refl = actor-has-inbox valid
    inboxesAfter = update-inboxes (store env) (env-inboxes env) (messages-valid env) (actorsPointer (sym (inbs=store env))) remove-message
    receiveKind : List (NamedMessage (inbox-shape actor)) → ReceiveKind
    receiveKind [] = Nothing
    receiveKind (NamedM _ ps ∷ xs) = Value (reference-names ps)
    env' : GetInbox (store env) (inbox-shape actor) → Env
    env' record { messages = [] ; valid = _ } = replace-actors+blocked env
                                                rest restValid
                                                (actor ∷ blocked env) (valid ∷ blocked-valid env)
    env' record { messages = (nm ∷ messages) ; valid = nmv ∷ vmsg } = record
                                                                   { acts = add-references-rewrite actor (named-inboxes nm) {unname-message nm} (add-references++ nm nmv (pre actor) ) (♭ (f (unname-message nm))) ∷ rest
                                                                   ; blocked = blocked env
                                                                   ; env-inboxes = updated-inboxes inboxesAfter
                                                                   ; store = store env
                                                                   ; inbs=store = trans (inbs=store env) (same-store inboxesAfter)
                                                                   ; actors-valid = record {
                                                                     actor-has-inbox = actor-has-inbox valid
                                                                     ; references-have-pointer = valid++ nm nmv (references actor) (references-have-pointer valid) } ∷ restValid
                                                                   ; blocked-valid = blocked-valid env
                                                                   ; messages-valid = inboxes-valid inboxesAfter
                                                                   ; fresh-name = fresh-name env
                                                                   ; name-is-fresh = name-is-fresh env
                                                                   }
-- ===== Bind lift =====
-- To bind a lift we just perform the lifting of the actor and rewrap it in the same bind, like so:
-- ((Lift x) >>= f) ⇒ liftedX >>= f
simulate env | actor@(_) ∷ rest | valid ∷ restValid | m >>= f |
  ALift {B} {esX} {postX} inc x with (♭ x)
... | bx = keep-simulating (Bind (TLift (name actor))) env'
  where
    liftedRefs = lift-references inc (references actor) (pre-eq-refs actor)
    liftedBx : ActorM (inbox-shape actor) B (map shape (contained liftedRefs)) postX
    liftedBx rewrite (sym (contained-eq-inboxes liftedRefs)) = bx
    bindAct : Actor
    bindAct = lift-actor actor (contained liftedRefs) refl (♯ liftedBx >>= f)
    bindActValid : ValidActor (store env) bindAct
    bindActValid = record { actor-has-inbox = actor-has-inbox valid
                          ; references-have-pointer = All-⊆ (subset liftedRefs) (references-have-pointer valid) }
    env' : Env
    env' = replace-actors env (bindAct ∷ rest) (bindActValid ∷ restValid)
-- ===== Bind self =====
-- To bind 'self' we just need to add the actors name and type to its references / precondition.
-- We get the proof that the added reference is valid via (actor-has-inbox valid).
-- countinues with (f tt)
simulate env | actor@(_) ∷ rest | valid ∷ restValid | m >>= f |
  Self = keep-simulating (Bind (Self (name actor))) env'
  where
    bindAct : Actor
    bindAct = add-reference actor (inbox# name actor [ inbox-shape actor ]) (♭ (f _))
    bindActValid : ValidActor (store env) bindAct
    bindActValid = record { actor-has-inbox = actor-has-inbox valid
                          ; references-have-pointer = [p: (actor-has-inbox valid) ][handles: ⊆-refl ] ∷ references-have-pointer valid }
    env' : Env
    env' = replace-actors env (bindAct ∷ rest) (bindActValid ∷ restValid)
-- ===== Spawn =====
-- Spawn without a following bind.
-- The current actor is finished, so we drop it using drop-top-actor.
-- The new actor is added to the top and will be moved to the bottom of the
-- round-robin queue by keep-simulating
simulate env | actor@(_) ∷ rest | valid ∷ restValid |
  Spawn act₁ = keep-simulating (Spawn (name actor) (fresh-name env)) (add-top act₁ (drop-top-actor env))
-- ===== Send reference =====
-- Send reference without a following bind.
-- Very similar to send reference with a following bind,
-- but we also drop the actor that sent the value.
simulate env | actor@(_) ∷ rest | valid ∷ restValid |
  Send {ToIS = ToIS} canSendTo (SendM p fields) = keep-simulating (Send (name actor) (name foundTo) (reference-names namedFields)) withUnblocked
  where
    foundTo : FoundReference (store env) ToIS
    foundTo = lookup-reference-act valid canSendTo
    namedFields = name-fields-act (store env) actor fields valid
    withUpdatedInbox : Env
    withUpdatedInbox = update-inbox-env env
                       (underlying-pointer foundTo)
                       (add-message (NamedM (translate-message-pointer foundTo p) namedFields)
                       (make-pointers-compatible (store env) (pre actor) (references actor) (pre-eq-refs actor) fields (references-have-pointer valid)))
    withTopDropped : Env
    withTopDropped = drop-top-actor withUpdatedInbox
    withUnblocked : Env
    withUnblocked = unblock-actor withTopDropped (name foundTo)
-- ===== Receive =====
-- Receive without a following bind is like return,
-- so just drop the actor.
-- We could remve the message in the inbox,
-- but there is currently no proofs that care about doing so.
simulate env | actor@(_) ∷ rest | valid ∷ restValid |
  Receive = keep-simulating (Receive (name actor) Dropped) (drop-top-actor env)
-- ===== Lift =====
-- Just performs the lifting by translating a subset for preconditions
-- to a subset for references.
simulate env | actor@(_) ∷ rest | valid ∷ restValid |
  ALift inc x with (♭ x)
... | bx = keep-simulating (TLift (name actor)) env'
  where
    liftedRefs = lift-references inc (references actor) (pre-eq-refs actor)
    bxLifted : Actor
    bxLifted = lift-actor actor (contained liftedRefs) (sym (contained-eq-inboxes liftedRefs)) bx
    bxValid : ValidActor (store env) bxLifted
    bxValid = record {
      actor-has-inbox = actor-has-inbox valid
      ; references-have-pointer = All-⊆ (subset liftedRefs) (references-have-pointer valid)
      }
    env' : Env
    env' = replace-actors env (bxLifted ∷ rest) (bxValid ∷ restValid)
-- Self without a following bind is like return,
-- so just drop the actor.
simulate env | actor@(_) ∷ rest | valid ∷ restValid |
  Self = keep-simulating (Self (name actor)) (drop-top-actor env)


keep-simulating trace env = record { env = env ; trace = trace } ∷ ♯ simulate (top-actor-to-back env)
