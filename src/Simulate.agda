module Simulate where

open import ActorMonad public
open import SimulationEnvironment
open import EnvironmentOperations
open import Prelude

open import Data.List.All.Properties
  using (++⁺)
open import Data.Nat.Properties
  using (≤-reflexive ; ≤-step)
open import Data.Product
  using (Σ ; _,_ ; _×_ ; Σ-syntax)

open Actor
open ValidActor
open Env
open FoundReference
open LiftedReferences
open UpdatedInbox
open ValidMessageList
open NamedInbox
open _comp↦_∈_
open NameSupply
open NameSupplyStream

data Trace (i : Size) : Set₂

record ∞Trace (i : Size) : Set₂ where
  coinductive
  constructor delay_
  field force : {j : Size< i} → Trace j

data Trace (i : Size) where
  TraceStop : (env : Env) → Done env → Trace i
  _∷_ : (x : Env) (xs : ∞Trace i) → Trace i

reduce-unbound-return : {act : Actor} → (env : Env) → Focus act env →
                        ActorAtConstructor Return act →
                        ActorHasNoContinuation act →
                        Env
reduce-unbound-return env Focused AtReturn no-cont = block-focused env Focused (BlockedReturn AtReturn no-cont)

reduce-bound-return : {act : Actor} → (env : Env) → Focus act env →
                      ActorAtConstructor Return act →
                      ActorHasContinuation act →
                      Env
reduce-bound-return env@record {
  acts = actor@record { computation = Return v ⟶ (f ∷ cont) } ∷ rest
  ; actors-valid = actor-valid ∷ rest-valid
  } Focused AtReturn HasContinuation =
    let
      actor' : Actor
      actor' = replace-actorM actor ((f v .force) ⟶ cont)
      env' : Env
      env' = replace-focused
               env
               Focused
               actor'
               (rewrap-valid-actor AreSame actor-valid)
    in env'

reduce-bind : {act : Actor} → (env : Env) → Focus act env →
              ActorAtConstructor Bind act →
              Env
reduce-bind env@record { acts = actor@record { computation = (m ∞>>= f) ⟶ cont } ∷ rest ; actors-valid = actor-valid ∷ rest-valid } Focused AtBind =
  let
    actor' : Actor
    actor' = replace-actorM actor ((m .force) ⟶ (f ∷ cont))
    env' : Env
    env' = replace-focused
             env
             Focused
             actor'
             (rewrap-valid-actor AreSame actor-valid)
  in env'

reduce-spawn : {act : Actor} → (env : Env) → Focus act env →
               ActorAtConstructor Spawn act →
               Env
reduce-spawn env@record {
  acts = actor@record { computation = Spawn {NewIS} {B} act ⟶ cont } ∷ rest
  ; actors-valid = actor-valid ∷ rest-valid
  } Focused AtSpawn =
  let
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
  in env'''

reduce-send : {act : Actor} → (env : Env) → Focus act env →
              ActorAtConstructor Send act →
              Env
reduce-send env@record {
  acts = actor@record { computation = Send {ToIS = ToIS} canSendTo (SendM tag fields) ⟶ cont } ∷ rest
  ; actors-valid = actor-valid ∷ rest-valid
  } Focused AtSend =
  let
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
  in withUpdatedInbox


reduce-receive-without-message : {act : Actor} → (env : Env) → Focus act env →
                              ActorAtConstructor Receive act →
                              (p : has-inbox (env .store) act) →
                              inbox-for-actor (env .env-inboxes) act p [] →
                              Env
reduce-receive-without-message env Focused AtReceive  p ifa = block-focused env Focused (BlockedReceive AtReceive p ifa)

reduce-receive-with-message : {act : Actor} → (env : Env) → Focus act env →
                              ActorAtConstructor Receive act →
                              (p : has-inbox (env .store) act) →
                              ∀ inbox →
                              all-messages-valid (env .store) inbox →
                              InboxInState NonEmpty inbox →
                              inbox-for-actor (env .env-inboxes) act p inbox →
                              Env
reduce-receive-with-message env@record {
  acts = actor@record { computation = (Receive ⟶ cont) } ∷ rest
  ; actors-valid = actor-valid ∷ rest-valid
  } Focused AtReceive p (nm ∷ messages) (nmv ∷ vms) HasMessage ifa =
  let
    inboxesAfter = update-inbox
                     (env .store)
                     (env .env-inboxes)
                     (env .messages-valid)
                     (actor-valid .actor-has-inbox)
                     remove-message
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
    actor-valid' : ValidActor (env .store) actor'
    actor-valid' = record {
      actor-has-inbox = actor-valid .actor-has-inbox
      ; references-have-pointer = valid++ nm nmv (actor-valid .references-have-pointer)
      }
    env' : Env
    env' = let
      updated = update-inbox (env .store) (env .env-inboxes) (env .messages-valid) (actor-valid .actor-has-inbox) remove-message
      unblock-split = unblock-actors updated (env .blocked) (env .blocked-valid) (env .blocked-no-progress)
      open UnblockedActors
        in record
             { acts = actor' ∷ unblock-split .unblocked ++ rest
             ; blocked = unblock-split .still-blocked
             ; store = env .store
             ; env-inboxes = updated .updated-inboxes
             ; name-supply = env .name-supply
             ; actors-valid = actor-valid' ∷ ++⁺ (unblock-split .unblocked-valid) rest-valid
             ; blocked-valid = unblock-split .blocked-valid
             ; messages-valid = updated .inboxes-valid
             ; blocked-no-progress = unblock-split .blocked-no-prog
             }
  in env'


reduce-receive : {act : Actor} → (env : Env) → Focus act env →
                 ActorAtConstructor Receive act →
                 Env
reduce-receive env@record { acts = actor ∷ rest ; actors-valid = actor-valid ∷ _ } Focused AtReceive = choose-reduction (get-inbox env (actor-valid .actor-has-inbox))
  where
    open GetInbox
    choose-reduction : (gi : GetInbox (env .store) (env .env-inboxes) (actor-valid .actor-has-inbox)) → Env
    choose-reduction gi@record { messages = [] } =
      reduce-receive-without-message env Focused AtReceive _ (gi .right-inbox)
    choose-reduction gi@record { messages = _ ∷ _ } =
      reduce-receive-with-message env Focused AtReceive _ (gi .messages) (gi .valid) HasMessage (gi .right-inbox)

reduce-self : {act : Actor} → (env : Env) → Focus act env →
              ActorAtConstructor Self act →
              Env
reduce-self env@record { acts = actor@record {
  computation = Self ⟶ cont } ∷ _
  ; actors-valid = actor-valid ∷ _
  } Focused AtSelf =
  let
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
  in env'

reduce-strengthen : {act : Actor} → (env : Env) → Focus act env →
                    ActorAtConstructor Strengthen act →
                    Env
reduce-strengthen env@record {
  acts = actor@record { computation = Strengthen {ys} inc ⟶ cont } ∷ _
  ; actors-valid = actor-valid ∷ _
  } Focused AtStrengthen =
  let
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
  in env'

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

simulate : Env → ∞Trace ∞
simulate env@record { acts = [] ; actors-valid = [] } = delay TraceStop env AllBlocked
simulate env@record { acts = _ ∷ _ ; actors-valid = _ ∷ _ } = keep-stepping (reduce env Focused)
  where
    open ∞Trace
    keep-stepping : Env → ∞Trace ∞
    keep-stepping env .force = env ∷ simulate env
