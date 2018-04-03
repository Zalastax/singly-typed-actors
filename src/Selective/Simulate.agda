module Selective.Simulate where

open import Membership using (_∈_ ; _⊆_ ; All-⊆ ; translate-⊆ ; ⊆-refl)
open import Selective.ActorMonad public
open import Selective.SimulationEnvironment
open import Selective.EnvironmentOperations
open import Colist

open import Data.List using (List ; _∷_ ; [] ; map ; _++_)
open import Data.List.All using (All ; _∷_ ; [] ; lookup) renaming (map to ∀map)
open import Data.List.All.Properties using (++⁺)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_ ; s≤s)
open import Data.Nat.Properties using (≤-reflexive ; ≤-step)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; trans)

open import Level using (Lift ; lift) renaming (suc to lsuc ; zero to lzero)
open import Size using (∞)

data ReceiveKind : Set where
  Nothing : ReceiveKind
  Value : List Name → ReceiveKind
  Dropped : ReceiveKind

data Trace : Set where
  Return : Name → Trace
  Bind : Name → Trace
  Spawn : (spawner : Name) → (spawned : Name) → Trace
  Send : (sender : Name) → (receiver : Name) → (references : List Name) → Trace
  Receive : Name → ReceiveKind → Trace
  Selective : Name → ReceiveKind → Trace
  Strengthen  : Name → Trace
  Self : Name → Trace

-- A step in the simulation is the next environment paired up with what step was taken
record EnvStep : Set₂ where
  field
    env : Env
    trace : Trace

private
  keep-simulating : Trace → Env → ∞Colist ∞ EnvStep

open Actor
open ValidActor
open Env
open FoundReference
open LiftedReferences
open UpdatedInboxes
open ValidMessageList
open NamedInbox
open _comp↦_∈_
open ∞Colist

-- Simulates the actors running in parallel by making one step of one actor at a time.
-- The actor that was run is put in the back of the queue unless it became blocked.
-- A simulation can possibly be infinite, and is thus modelled as an infinite list.
--
-- The simulation function is structured by pattern matching on every constructor of ActorM
-- for the top-most actor.
simulate : Env → ∞Colist ∞ EnvStep
simulate env with (acts env) | (actors-valid env)
simulate env | [] | _ = delay []
simulate env | actor ∷ rest | _ with (computation actor)
simulate env | actor ∷ rest | _ | Return val ⟶ [] = keep-simulating (Return (name actor)) (drop-top-actor env)
simulate env | actor ∷ rest | valid ∷ restValid | Return val ⟶ (f ∷ cont) = keep-simulating (Return (name actor)) env'
  where
    actor' : Actor
    actor' = replace-actorM actor ((f val) .force ⟶ cont)
    env' : Env
    env' = replace-actors
             env
             (actor' ∷ rest)
             (rewrap-valid-actor valid refl refl refl ∷ restValid)
simulate env | actor ∷ rest | valid ∷ restValid | (m ∞>>= f) ⟶ cont = keep-simulating (Bind (name actor)) env'
  where
    actor' : Actor
    actor' = replace-actorM actor (m .force ⟶ (f ∷ cont))
    env' : Env
    env' = replace-actors
             env
             (actor' ∷ rest)
             (rewrap-valid-actor valid refl refl refl ∷ restValid)
simulate env | actor ∷ rest | valid ∷ restValid | Spawn {NewIS} {B} act ⟶ cont = keep-simulating (Spawn (name actor) (fresh-name env)) env'
  where
    newStoreEntry : NamedInbox
    newStoreEntry = inbox# (fresh-name env) [ NewIS ]
    newStore : Store
    newStore = newStoreEntry ∷ store env
    newAct : Actor
    newAct = new-actor act (fresh-name env)
    newActValid : ValidActor newStore newAct
    newActValid = record { actor-has-inbox = zero ; references-have-pointer = [] }
    newIsFresh : NameFresh newStore (suc (fresh-name env))
    newIsFresh = s≤s (≤-reflexive refl) ∷ ∀map ≤-step (name-is-fresh env)
    actor' : Actor
    actor' = add-reference actor newStoreEntry (Return _ ⟶ cont)
    valid' : ValidActor newStore actor'
    valid' = record {
      actor-has-inbox = suc {pr = suc-helper (actor-has-inbox valid) (name-is-fresh env)} (actor-has-inbox valid)
      ; references-have-pointer = [p: zero ][handles: ⊆-refl ] ∷ ∀map
                                      (λ p → suc-p (suc-helper (actual-has-pointer p) (name-is-fresh env)) p)
                                      (references-have-pointer valid) }
    env' : Env
    env' = record
             { acts = newAct ∷ actor' ∷ rest
             ; blocked = blocked env
             ; store = newStore
             ; env-inboxes = [] ∷ env-inboxes env
             ; actors-valid = newActValid ∷ valid' ∷ ∀map (valid-actor-suc (name-is-fresh env)) restValid
             ; blocked-valid = ∀map (valid-actor-suc (name-is-fresh env)) (blocked-valid env)
             ; messages-valid = [] ∷ map-suc (store env) (messages-valid env) (name-is-fresh env)
             ; fresh-name = suc (fresh-name env)
             ; name-is-fresh = newIsFresh
             }
         where
           map-suc : (store : Store) → {store' : Store} {inbs : Inboxes store'} → InboxesValid store inbs → ∀ {n} → NameFresh store n → InboxesValid (inbox# n [ NewIS ] ∷ store) inbs
           map-suc store [] frsh = []
           map-suc store (x ∷ valid) frsh = messages-valid-suc frsh x ∷ map-suc store valid frsh
simulate env | actor ∷ rest | valid ∷ restValid | Send {ToIS = ToIS} canSendTo (SendM tag fields) ⟶ cont =
  keep-simulating (Send (name actor) (name foundTo) (reference-names namedFields)) withUnblocked
  where
    foundTo : FoundReference (store env) ToIS
    foundTo = lookup-reference-act valid canSendTo
    namedFields = name-fields-act (store env) actor fields valid
    actor' : Actor
    actor' = replace-actorM actor (Return _ ⟶ cont)
    withM : Env
    withM = replace-actors
              env
              (actor' ∷ rest)
              ((rewrap-valid-actor valid refl refl refl) ∷ restValid)
    withUpdatedInbox : Env
    withUpdatedInbox = update-inbox-env
                         withM
                         (underlying-pointer foundTo)
                         (add-message
                           (NamedM
                             (translate-message-pointer foundTo tag)
                             namedFields)
                           (make-pointers-compatible
                             (store env)
                             (pre actor)
                             (references actor)
                             (pre-eq-refs actor)
                             fields
                             (references-have-pointer valid)))
    withUnblocked : Env
    withUnblocked = unblock-actor withUpdatedInbox (name foundTo)
simulate env | actor ∷ rest | valid ∷ restValid | Receive ⟶ cont = keep-simulating (Receive (name actor) (receiveKind (GetInbox.messages actorsInbox))) (env' actorsInbox)
  where
    actorsInbox : GetInbox (store env) (inbox-shape actor)
    actorsInbox = get-inbox env (actor-has-inbox valid)
    inboxesAfter = update-inboxes (store env) (env-inboxes env) (messages-valid env) (actor-has-inbox valid) remove-message
    receiveKind : List (NamedMessage (inbox-shape actor)) → ReceiveKind
    receiveKind [] = Nothing
    receiveKind (NamedM _ ps ∷ xs) = Value (reference-names ps)
    env' : GetInbox (store env) (inbox-shape actor) → Env
    env' record { messages = [] } = replace-actors+blocked
                                      env
                                      rest
                                      restValid
                                      (actor ∷ blocked env)
                                      (valid ∷ blocked-valid env)
    env' record { messages = (nm ∷ messages) ; valid = nmv ∷ vms } = record
                                             { acts = add-references-rewrite
                                                        actor
                                                        (named-inboxes nm)
                                                        {unname-message nm}
                                                        (add-references++
                                                          nm
                                                          nmv
                                                          (pre actor))
                                                        (Return (unname-message nm) ⟶ cont)
                                                        ∷ rest
                                             ; blocked = blocked env
                                             ; store = store env
                                             ; env-inboxes = updated-inboxes inboxesAfter
                                             ; actors-valid = record {
                                               actor-has-inbox = actor-has-inbox valid
                                               ; references-have-pointer = valid++
                                                                             nm
                                                                             nmv
                                                                             (references-have-pointer valid) }
                                               ∷ restValid
                                             ; blocked-valid = blocked-valid env
                                             ; messages-valid = inboxes-valid inboxesAfter
                                             ; fresh-name = fresh-name env
                                             ; name-is-fresh = name-is-fresh env
                                             }
simulate env | actor ∷ rest | valid ∷ restValid | SelectiveReceive filter ⟶ cont = keep-simulating (Selective (name actor) (receiveKind selectedMessage)) (env' selectedMessage)
  where
    actorsInbox : GetInbox (store env) (inbox-shape actor)
    actorsInbox = get-inbox env (actor-has-inbox valid)
    selectedMessage : FoundInList (GetInbox.messages actorsInbox) (λ x → filter (unname-message x))
    selectedMessage = find-split (GetInbox.messages actorsInbox) (λ x → filter (unname-message x))
    inboxesAfter = update-inboxes (store env) (env-inboxes env)
                                  (messages-valid env) (actor-has-inbox valid)
                                  (remove-found-message filter)
    receiveKind : FoundInList (GetInbox.messages actorsInbox) (λ x → filter (unname-message x)) → ReceiveKind
    receiveKind (Found split x) = Value (reference-names (Σ.proj₂ (named-message-fields (el split))))
      where open SplitList
    receiveKind Nothing = Nothing
    env' : FoundInList (GetInbox.messages actorsInbox) (λ x → filter (unname-message x)) → Env
    env' Nothing = replace-actors+blocked env
                   rest restValid
                   (actor ∷ blocked env) (valid ∷ blocked-valid env)
    env' (Found split x) = record
                             { acts = add-references-rewrite actor (named-inboxes (SplitList.el split))
                                      {unname-message (SplitList.el split)}
                                      (add-references++ (SplitList.el split)
                                        (split-all-el
                                          (GetInbox.messages actorsInbox)
                                          (GetInbox.valid actorsInbox)
                                          split)
                                        (pre actor))
                                      (Return (record { msg = unname-message (SplitList.el split) ; msg-ok = x }) ⟶ cont) ∷ rest
                             ; blocked = blocked env
                             ; store = store env
                             ; env-inboxes = updated-inboxes inboxesAfter
                             ; actors-valid = (record {
                               actor-has-inbox = actor-has-inbox valid
                               ; references-have-pointer = valid++ (SplitList.el split)
                                 (split-all-el (GetInbox.messages actorsInbox)
                                   (GetInbox.valid actorsInbox)
                                   split)
                                 (references-have-pointer valid)
                               }) ∷ restValid
                             ; blocked-valid = blocked-valid env
                             ; messages-valid = inboxes-valid inboxesAfter
                             ; fresh-name = fresh-name env
                             ; name-is-fresh = name-is-fresh env
                             }
simulate env | actor ∷ rest | valid ∷ restValid | Self ⟶ cont = keep-simulating (Self (name actor)) env'
  where
    actor' : Actor
    actor' = add-reference actor inbox# (name actor) [ (inbox-shape actor) ] (Return _ ⟶ cont)
    valid' : ValidActor (store env) actor'
    valid' = record {
                  actor-has-inbox = actor-has-inbox valid
                  ; references-have-pointer = [p: (actor-has-inbox valid) ][handles: ⊆-refl ] ∷ references-have-pointer valid }
    env' : Env
    env' = replace-actors env (actor' ∷ rest) (valid' ∷ restValid)
simulate env | actor ∷ rest | valid ∷ restValid | Strengthen {ys} inc ⟶ cont = keep-simulating (Strengthen (name actor)) env'
  where
    liftedRefs = lift-references inc (references actor) (pre-eq-refs actor)
    strengthenedM : ActorM ∞ (inbox-shape actor) ⊤₁ (map shape (contained liftedRefs)) (λ _ → ys)
    strengthenedM rewrite (sym (contained-eq-inboxes liftedRefs))= Return _
    actor' : Actor
    actor' = lift-actor actor (contained liftedRefs) refl (strengthenedM ⟶ cont)
    valid' : ValidActor (store env) actor'
    valid' = record {
      actor-has-inbox = actor-has-inbox valid
      ; references-have-pointer = All-⊆ (subset liftedRefs) (references-have-pointer valid) }
    env' : Env
    env' = replace-actors env (actor' ∷ rest) (valid' ∷ restValid)


keep-simulating trace env .force = record { env = env ; trace = trace } ∷ simulate (top-actor-to-back env)
