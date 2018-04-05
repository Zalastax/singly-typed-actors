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
open import Data.Maybe using (Maybe ; just ; nothing)

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
  constructor _traces_
  field
    trace : Trace
    env : Env

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

reduce-return-to-nothing : ∀ {IS A mid} {v : A} → (env : Env) → Focus {IS} {post = mid} {cont = []} (Return v) env → Env
reduce-return-to-nothing env (Foc va) = drop-top-actor env

reduce-return-to-f : ∀ {IS A B C mid} {v : A} {post : B → TypingContext} {post' : C → TypingContext} {f : Cont ∞ IS mid post} {cont : ContStack ∞ IS post post'} → (env : Env) → Focus {IS} {A} {mid v} {mid} {cont = f ∷ cont} (Return v) env → Env
reduce-return-to-f {v = v} {f = f} {cont = cont} env (Foc {rest = rest} {rv = restValid} {per = per} va) = env'
  where
    actor' : Actor
    actor' = replace-actorM record { inbox-shape = _ ; A = _ ; references = _ ; pre = _ ; pre-eq-refs = per ; post = _ ; computation = Return v ⟶ (f ∷ cont) ; name = _ } ((f v) .force ⟶ cont)
    env' : Env
    env' = replace-actors
             env
             (actor' ∷ rest)
             (rewrap-valid-actor va refl refl refl ∷ restValid)

reduce : Env → Maybe EnvStep
reduce record { acts = [] } = nothing
reduce env@(record { acts = actor@(record { computation = (Return val ⟶ [])}) ∷ rest ; actors-valid = (valid ∷ restValid)}) = just (Return (name actor) traces reduce-return-to-nothing env (Foc valid))
reduce env@(record { acts = actor@(record { computation = (Return val ⟶ (f ∷ cont))}) ∷ rest ; actors-valid = (valid ∷ restValid)}) = just (Return (name actor) traces reduce-return-to-f env (Foc valid))
reduce record { acts = actor@(record { computation = ((m ∞>>= f) ⟶ cont) }) ∷ rest ; actors-valid = valid ∷ restValid } = {!!}
reduce record { acts = (record { inbox-shape = inbox-shape ; A = A ; references = references ; pre = pre ; pre-eq-refs = pre-eq-refs ; post = post ; computation = (Spawn act ⟶ cont) ; name = name } ∷ acts₁) ; blocked = _ ; store = _ ; env-inboxes = _ ; actors-valid = (px ∷ actors-valid₁) ; blocked-valid = _ ; messages-valid = _ ; name-supply = _ } = {!!}
reduce record { acts = (record { inbox-shape = inbox-shape ; A = A ; references = references ; pre = pre ; pre-eq-refs = pre-eq-refs ; post = post ; computation = (Send canSendTo msg ⟶ cont) ; name = name } ∷ acts₁) ; blocked = _ ; store = _ ; env-inboxes = _ ; actors-valid = (px ∷ actors-valid₁) ; blocked-valid = _ ; messages-valid = _ ; name-supply = _ } = {!!}
reduce record { acts = (record { inbox-shape = inbox-shape ; A = A ; references = references ; pre = pre ; pre-eq-refs = pre-eq-refs ; post = post ; computation = (Receive ⟶ cont) ; name = name } ∷ acts₁) ; blocked = _ ; store = _ ; env-inboxes = _ ; actors-valid = (px ∷ actors-valid₁) ; blocked-valid = _ ; messages-valid = _ ; name-supply = _ } = {!!}
reduce record { acts = (record { inbox-shape = inbox-shape ; A = A ; references = references ; pre = pre ; pre-eq-refs = pre-eq-refs ; post = post ; computation = (Self ⟶ cont) ; name = name } ∷ acts₁) ; blocked = _ ; store = _ ; env-inboxes = _ ; actors-valid = (px ∷ actors-valid₁) ; blocked-valid = _ ; messages-valid = _ ; name-supply = _ } = {!!}
reduce record { acts = (record { inbox-shape = inbox-shape ; A = A ; references = references ; pre = pre ; pre-eq-refs = pre-eq-refs ; post = post ; computation = (Strengthen inc ⟶ cont) ; name = name } ∷ acts₁) ; blocked = _ ; store = _ ; env-inboxes = _ ; actors-valid = (px ∷ actors-valid₁) ; blocked-valid = _ ; messages-valid = _ ; name-supply = _ } = {!!}

{- reduce env with (acts env) | (actors-valid env)
reduce env | [] | _ = nothing
reduce env | actor ∷ rest | _ with (computation actor) | inspect computation actor
reduce env | actor ∷ rest | valid ∷ _ | Return val ⟶ [] | [ refl ] = just ((Return (name actor)) traces reduce-return-to-nothing env (Foc valid))
reduce env | actor ∷ rest | valid ∷ restValid | Return val ⟶ (f ∷ cont) | p = just ((Return (name actor)) traces env')
  where
    actor' : Actor
    actor' = replace-actorM actor ((f val) .force ⟶ cont)
    env' : Env
    env' = replace-actors
             env
             (actor' ∷ rest)
             (rewrap-valid-actor valid refl refl refl ∷ restValid)
reduce env | actor ∷ rest | valid ∷ restValid | (m ∞>>= f) ⟶ cont | p = just ((Bind (name actor)) traces env')
  where
    actor' : Actor
    actor' = replace-actorM actor (m .force ⟶ (f ∷ cont))
    env' : Env
    env' = replace-actors
             env
             (actor' ∷ rest)
             (rewrap-valid-actor valid refl refl refl ∷ restValid)
reduce env | actor ∷ rest | valid ∷ restValid | Spawn {NewIS} {B} act ⟶ cont | p = just ((Spawn (name actor) (env .name-supply .supply .name)) traces env')
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
reduce env | actor ∷ rest | valid ∷ restValid | Send {ToIS = ToIS} canSendTo (SendM tag fields) ⟶ cont | p =
  just ((Send (name actor) (name foundTo) (reference-names namedFields)) traces withUnblocked)
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
reduce env | actor ∷ rest | valid ∷ restValid | Receive ⟶ cont | p = just ((Receive (name actor) (receiveKind (GetInbox.messages actorsInbox))) traces (env' actorsInbox))
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
reduce env | actor ∷ rest | valid ∷ restValid | Self ⟶ cont | p = just ((Self (name actor)) traces env')
  where
    actor' : Actor
    actor' = add-reference actor inbox# (name actor) [ (inbox-shape actor) ] (Return _ ⟶ cont)
    valid' : ValidActor (store env) actor'
    valid' = record {
                  actor-has-inbox = actor-has-inbox valid
                  ; references-have-pointer = [p: (actor-has-inbox valid) ][handles: ⊆-refl ] ∷ references-have-pointer valid }
    env' : Env
    env' = replace-actors env (actor' ∷ rest) (valid' ∷ restValid)
reduce env | actor ∷ rest | valid ∷ restValid | Strengthen {ys} inc ⟶ cont | p = just ((Strengthen (name actor)) traces env')
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
-}

simulate : Env → ∞Colist ∞ EnvStep
simulate env .force = loop (reduce env)
  where
    loop : Maybe EnvStep → Colist ∞ EnvStep
    loop (just x) = x ∷ simulate (top-actor-to-back (EnvStep.env x))
    loop nothing = []
