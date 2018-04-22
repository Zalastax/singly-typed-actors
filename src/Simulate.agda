module Simulate where

open import Membership using (_∈_ ; _⊆_ ; All-⊆ ; translate-⊆ ; ⊆-refl)
open import ActorMonad public
open import SimulationEnvironment
open import EnvironmentOperations
open import Colist

open import Data.List using (List ; _∷_ ; [] ; map ; _++_)
open import Data.List.All using (All ; _∷_ ; [] ; lookup) renaming (map to ∀map)
open import Data.List.All.Properties using (++⁺)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_ ; s≤s)
open import Data.Nat.Properties using (≤-reflexive ; ≤-step)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; trans ; inspect ; [_])

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
  Strengthen  : Name → Trace
  Self : Name → Trace

-- A step in the simulation is the next environment paired up with what step was taken
record EnvStep : Set₂ where
  field
    env : Env
    trace : Trace

-- private
--   keep-simulating : Trace → Env → ∞Colist ∞ EnvStep

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
open NameSupply
open NameSupplyStream

reduce-unbound-return : {act : Actor} → (env : Env) → Focus act env →
                        ActorAtConstructor Return act →
                        ActorHasNoContinuation act →
                        Env
reduce-unbound-return env Focused AtReturn NoContinuation = block-focused env Focused

reduce-bound-return : {act : Actor} → (env : Env) → Focus act env →
                      ActorAtConstructor Return act →
                      ActorHasContinuation act →
                      Env
reduce-bound-return env@record {
  acts = actor@record { computation = Return v ⟶ (f ∷ cont) } ∷ rest
  ; actors-valid = actor-valid ∷ rest-valid
  } Focused AtReturn HasContinuation = env'
  where
    actor' : Actor
    actor' = replace-actorM actor ((f v .force) ⟶ cont)
    env' : Env
    env' = replace-focused
             env
             Focused
             actor'
             (rewrap-valid-actor AreSame actor-valid)

reduce-bind : {act : Actor} → (env : Env) → Focus act env →
              ActorAtConstructor Bind act →
              Env
reduce-bind env@record { acts = actor@record { computation = (m ∞>>= f) ⟶ cont } ∷ rest ; actors-valid = actor-valid ∷ rest-valid } Focused AtBind = env'
  where
    actor' : Actor
    actor' = replace-actorM actor ((m .force) ⟶ (f ∷ cont))
    env' : Env
    env' = replace-focused
             env
             Focused
             actor'
             (rewrap-valid-actor AreSame actor-valid)

reduce-spawn : {act : Actor} → (env : Env) → Focus act env →
               ActorAtConstructor Spawn act →
               Env
reduce-spawn env@record {
  acts = actor@record { computation = Spawn {NewIS} {B} act ⟶ cont } ∷ rest
  ; actors-valid = actor-valid ∷ rest-valid
  } Focused AtSpawn = env'''
  where
    new-name : Name
    new-name = env .name-supply .supply .name
    new-store-entry : NamedInbox
    new-store-entry = inbox# new-name [ NewIS ]
    env' : Env
    env' = add-top (act ⟶ []) env
    valid' : ValidActor (env' .store) actor
    valid' = valid-actor-suc (env .name-supply .supply) actor-valid
    env'' : Env
    env'' = top-actor-to-back env'
    actor' : Actor
    actor' = add-reference actor new-store-entry (Return _ ⟶ cont)
    valid'' : ValidActor (env'' .store) actor'
    valid'' = add-reference-valid RefAdded valid' [p: zero ][handles: ⊆-refl ]
    env''' : Env
    env''' = replace-focused env'' Focused actor' valid''

reduce-send : {act : Actor} → (env : Env) → Focus act env →
              ActorAtConstructor Send act →
              Env
reduce-send env@record {
  acts = actor@record { computation = Send {ToIS = ToIS} canSendTo (SendM tag fields) ⟶ cont } ∷ rest
  ; actors-valid = actor-valid ∷ rest-valid
  } Focused AtSend = withUnblocked
  where
    to-reference : FoundReference (store env) ToIS
    to-reference = lookup-reference-act actor-valid canSendTo
    namedFields = name-fields-act (store env) actor fields actor-valid
    actor' : Actor
    actor' = replace-actorM actor (Return _ ⟶ cont)
    withM : Env
    withM = replace-focused
              env
              Focused
              actor'
              (rewrap-valid-actor AreSame actor-valid)
    message = NamedM
                (translate-message-pointer to-reference tag)
                namedFields
    message-is-valid : message-valid (env .store) message
    message-is-valid = make-pointers-compatible
                         (env .store)
                         (actor .pre)
                         (actor .references)
                         (actor .pre-eq-refs)
                         fields
                         (actor-valid .references-have-pointer)
    updater = add-message message message-is-valid
    withUpdatedInbox : Env
    withUpdatedInbox = update-inbox-env
                         withM
                         (underlying-pointer to-reference)
                         updater
    withUnblocked : Env
    withUnblocked = unblock-actor withUpdatedInbox (name to-reference)


reduce-receive-without-message : {act : Actor} → (env : Env) → Focus act env →
                              ActorAtConstructor Receive act →
                              ∀ inbox →
                              InboxInState Empty inbox →
                              ActorsInbox env act inbox →
                              Env
reduce-receive-without-message env Focused AtReceive _ _ _ = block-focused env Focused

reduce-receive-with-message : {act : Actor} → (env : Env) → Focus act env →
                              ActorAtConstructor Receive act →
                              ∀ inbox →
                              all-messages-valid (env .store) inbox →
                              InboxInState NonEmpty inbox →
                              ActorsInbox env act inbox →
                              Env
reduce-receive-with-message env@record {
  acts = actor@record { computation = (Receive ⟶ cont) } ∷ rest
  ; actors-valid = actor-valid ∷ rest-valid
  } Focused AtReceive (nm ∷ messages) (nmv ∷ vms) HasMessage _ = env''
  where
    inboxesAfter = update-inboxes
                     (env .store)
                     (env .env-inboxes)
                     (env .messages-valid)
                     (actor-valid .actor-has-inbox)
                     remove-message
    env' : Env
    env' = update-inbox-env env (actor-valid .actor-has-inbox) remove-message
    actor' : Actor
    actor' = add-references-rewrite
               actor
               (named-inboxes nm)
               {unname-message nm}
               (add-references++
                 nm
                 nmv
                 (pre actor))
               (Return (unname-message nm) ⟶ cont)
    actor-valid' : ValidActor (env' .store) actor'
    actor-valid' = record {
      actor-has-inbox = actor-valid .actor-has-inbox
      ; references-have-pointer = valid++ nm nmv (actor-valid .references-have-pointer)
      }
    env'' : Env
    env'' = replace-focused env'
              Focused
              actor'
              actor-valid'


reduce-receive : {act : Actor} → (env : Env) → Focus act env →
                 ActorAtConstructor Receive act →
                 Env
reduce-receive env@record { acts = actor ∷ rest ; actors-valid = actor-valid ∷ _ } Focused AtReceive = choose-reduction (get-inbox env (actor-valid .actor-has-inbox)) ActInb
  where
    open GetInbox
    choose-reduction : (gi : GetInbox (env .store) (actor .inbox-shape)) → ActorsInbox env actor (gi .messages) → Env
    choose-reduction record { messages = [] } p = reduce-receive-without-message env Focused AtReceive [] IsEmpty p
    choose-reduction record { messages = inbox@(_ ∷ _) ; valid = valid } p = reduce-receive-with-message env Focused AtReceive inbox valid HasMessage p

reduce-self : {act : Actor} → (env : Env) → Focus act env →
              ActorAtConstructor Self act →
              Env
reduce-self env@record { acts = actor@record {
  computation = Self ⟶ cont } ∷ _
  ; actors-valid = actor-valid ∷ _
  } Focused AtSelf = env'
  where
    actor' : Actor
    actor' = add-reference actor inbox# (actor .name) [ (actor .inbox-shape) ] ((Return _) ⟶ cont)
    actor-valid' : ValidActor (env .store) actor'
    actor-valid' = add-reference-valid RefAdded actor-valid [p: (actor-valid .actor-has-inbox) ][handles: ⊆-refl ]
    env' : Env
    env' = replace-focused
             env
             Focused
             actor'
             actor-valid'

reduce-strengthen : {act : Actor} → (env : Env) → Focus act env →
                    ActorAtConstructor Strengthen act →
                    Env
reduce-strengthen env@record {
  acts = actor@record { computation = Strengthen {ys} inc ⟶ cont } ∷ _
  ; actors-valid = actor-valid ∷ _
  } Focused AtStrengthen = env'
  where
    lifted-references = lift-references inc (references actor) (pre-eq-refs actor)
    actor' : Actor
    actor' = lift-actor actor (lifted-references .contained) (lifted-references .contained-eq-inboxes) (Return _ ⟶ cont)
    actor-valid' : ValidActor (env .store) actor'
    actor-valid' = lift-valid-actor (CanBeLifted lifted-references) actor-valid
    env' : Env
    env' = replace-focused
             env
             Focused
             actor'
             actor-valid'

reduce : {act : Actor} → (env : Env) → Focus act env → Env
reduce env@record { acts = record { computation = (Return val ⟶ []) } ∷ _ } Focused =
  reduce-unbound-return env Focused AtReturn (NoContinuation {v = val})
reduce env@record { acts = record { computation = (Return val ⟶ (_ ∷ _)) } ∷ _ } Focused =
  reduce-bound-return env Focused AtReturn (HasContinuation {v = val})
reduce env@record { acts = record { computation = ((m ∞>>= f) ⟶ _)} ∷ _ } Focused =
  reduce-bind env Focused AtBind
reduce env@record { acts = record { computation = (Spawn act ⟶ cont) } ∷ _ } Focused =
  reduce-spawn env Focused AtSpawn
reduce env@record { acts = record { computation = (Send canSendTo msg ⟶ cont) } ∷ _ } Focused =
  reduce-send env Focused AtSend
reduce env@record { acts = record { computation = (Receive ⟶ cont) } ∷ _ } Focused =
  reduce-receive env Focused AtReceive
reduce env@record { acts = record { computation = (Self ⟶ cont) } ∷ _ } Focused =
  reduce-self env Focused AtSelf
reduce env@record { acts = record { computation = (Strengthen inc ⟶ cont) } ∷ _ } Focused =
  reduce-strengthen env Focused AtStrengthen

simulate2 : Env → ∞Colist ∞ Env
simulate2 record { acts = [] } = delay []
simulate2 env@record { acts = _ ∷ _ ; actors-valid = _ ∷ _ } = keep-stepping (reduce env Focused)
  where
    keep-stepping : Env → ∞Colist ∞ Env
    keep-stepping env .force = env ∷ simulate2 env


-- Simulates the actors running in parallel by making one step of one actor at a time.
-- The actor that was run is put in the back of the queue unless it became blocked.
-- A simulation can possibly be infinite, and is thus modelled as an infinite list.
--
-- The simulation function is structured by pattern matching on every constructor of ActorM
-- for the top-most actor.
{-
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
simulate env | actor ∷ rest | valid ∷ restValid | Spawn {NewIS} {B} act ⟶ cont = keep-simulating (Spawn (name actor) (env .name-supply .supply .name)) env'
  where
    newStoreEntry : NamedInbox
    newStoreEntry = inbox# (env .name-supply .supply .name) [ NewIS ]
    newStore : Store
    newStore = newStoreEntry ∷ store env
    newAct : Actor
    newAct = new-actor act (env .name-supply .supply .name)
    newActValid : ValidActor newStore newAct
    newActValid = record { actor-has-inbox = zero ; references-have-pointer = [] }
    actor' : Actor
    actor' = add-reference actor newStoreEntry (Return _ ⟶ cont)
    valid' : ValidActor newStore actor'
    valid' = record {
      actor-has-inbox = suc {pr = env .name-supply .supply .name-is-fresh (actor-has-inbox valid)} (actor-has-inbox valid)
      ; references-have-pointer = [p: zero ][handles: ⊆-refl ] ∷ ∀map
                                      (λ p → suc-p (env .name-supply .supply .name-is-fresh (actual-has-pointer p)) p)
                                      (references-have-pointer valid) }
    env' : Env
    env' = record
             { acts = newAct ∷ actor' ∷ rest
             ; blocked = blocked env
             ; store = newStore
             ; env-inboxes = [] ∷ env-inboxes env
             ; actors-valid = newActValid ∷ valid' ∷ ∀map (valid-actor-suc (env .name-supply .supply)) restValid
             ; blocked-valid = ∀map (valid-actor-suc (env .name-supply .supply)) (blocked-valid env)
             ; messages-valid = [] ∷ map-suc (store env) (messages-valid env) (env .name-supply .supply)
             ; name-supply = env .name-supply .next NewIS
             }
         where
           map-suc : (store : Store) → {store' : Store} {inbs : Inboxes store'} → InboxesValid store inbs → (ns : NameSupply store) → InboxesValid (inbox# ns .name [ NewIS ] ∷ store) inbs
           map-suc store [] ns = []
           map-suc store (x ∷ valid) ns = messages-valid-suc ns x ∷ map-suc store valid ns
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
                                             ; name-supply = env .name-supply
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
-}
