module Selective.Examples.ActiveObjects where

open import Selective.ActorMonad
open import Selective.Examples.Channel
open import Selective.Examples.Call2
open import Prelude
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)

open ChannelType
open ChannelInitiation


active-request-type : ChannelInitiation → InboxShape
active-request-type record { request = .[] ; response = response ; request-tagged = [] } = []
active-request-type record { request = .(_ ∷ _) ; response = response ; request-tagged = (px ∷ pxs) } =
  let rec = active-request-type (record { request = _ ; response = response ; request-tagged = pxs })
  in extra-fields-shape px ∷ rec

state-vars : ∀ {ci} {st : Set₁} → (st → TypingContext) → Message ci → InboxShape → st → TypingContext
state-vars f input caller state = caller ∷ add-references (f state) input


active-reply-needed-fields : ∀ mt → IsChannelMessage mt → MessageType
active-reply-needed-fields _ (HasTag MT) = MT

active-reply-type : ChannelType → InboxShape
active-reply-type record { channel-shape = [] } = []
active-reply-type record { channel-shape = (x ∷ xs) ; all-tagged = (px ∷ pxs) } =
  let rec = active-reply-type (record { channel-shape = xs ; all-tagged = pxs })
  in active-reply-needed-fields x px ∷ rec

record ActiveReply (ci : ChannelInitiation) (state-type : Set₁) (var-f : state-type → TypingContext) (input : Message (active-request-type ci)) (caller : InboxShape) : Set₁ where
  field
    new-state : state-type
    reply : SendMessage (active-reply-type (ci .response)) (state-vars var-f input caller new-state)

reply-vars : ∀ {st ci var-f input} → (st → TypingContext) → Message (active-request-type ci) → (caller : InboxShape) → ActiveReply ci st var-f input caller → TypingContext
reply-vars f input caller ar = state-vars f input caller (ActiveReply.new-state ar)

active-method : InboxShape → (state-type : Set₁) → (state-type → TypingContext) → ChannelInitiation → Set₂
active-method IS st var-f ci =
  let input-type = Message (active-request-type ci)
  in {i : Size} →
     {caller : InboxShape} →
     (input : input-type) →
     (state : st) →
     ∞ActorM i IS
       (ActiveReply ci st var-f input caller)
       (caller ∷ add-references (var-f state) input)
       (reply-vars var-f input caller)

active-inbox-shape : List ChannelInitiation → InboxShape
active-inbox-shape [] = []
active-inbox-shape (x ∷ lci) =
  let rec = active-inbox-shape lci
  in x .request ++ rec

record ActiveObject : Set₂ where
  field
    state-type : Set₁
    vars : state-type → TypingContext
    methods : List ChannelInitiation
    handlers : All (active-method (active-inbox-shape methods) state-type vars) methods

open ActiveObject

active-caller : (methods : List ChannelInitiation) →
                Message (active-inbox-shape methods) →
                InboxShape
active-caller methods (Msg x f) = active-caller' methods x
  where
    active-caller' : {MT : MessageType} →
                     (methods : List ChannelInitiation) →
                     MT ∈ active-inbox-shape methods →
                     InboxShape
    active-caller' [] ()
    active-caller' (record { request = [] } ∷ methods) p = active-caller' methods p
    active-caller' (record { request = x ∷ _ ; response = response } ∷ _) Z = response .channel-shape
    active-caller' (record { request = _ ∷ xs ; response = response ; request-tagged = _ ∷ pxs } ∷ methods) (S p) =
      active-caller' (record { request = xs ; response = response ; request-tagged = pxs } ∷ methods) p

forget-message : ∀ {i Γ} →
                 {IS IS' : InboxShape} →
                 (m : Message IS) →
                 ∞ActorM i IS' ⊤₁ (add-references Γ m) (λ _ → Γ)
forget-message (Msg x x₁) = strengthen (⊆++-l-refl _ _)

data InEither {a} {A : Set a} (v : A) (xs ys : List A) : Set a where
  Left : (v ∈ xs) → InEither v xs ys
  Right : (v ∈ ys) → InEither v xs ys

∈++ : ∀ {a} {A : Set a} {v : A} → (xs ys : List A) → (v ∈ (xs ++ ys)) → InEither v xs ys
∈++ [] ys p = Right p
∈++ (x ∷ xs) ys Z = Left Z
∈++ (x ∷ xs) ys (S p) with (∈++ xs ys p)
... | Left q = Left (S q)
... | Right q = Right q

invoke-active-method : {i : Size} →
                       (ac : ActiveObject) →
                       (input : Message (active-inbox-shape (ac .methods))) →
                       (state : ac .state-type) →
                       ∞ActorM i (active-inbox-shape (ac .methods))
                         (ac .state-type) (add-references (ac .vars state) input) (λ x → add-references (ac .vars x) input)
invoke-active-method ac (Msg x f) state = invoke f (ac .methods) (ac .handlers) x
  where
    translate-invoke-pointer : {ci : ChannelInitiation} →
                               {MT : MessageType} →
                               (ValueType UniqueTag ∷ ReferenceType (ci .response .channel-shape) ∷ MT) ∈ ci .request →
                               MT ∈ active-request-type ci
    translate-invoke-pointer {record { request-tagged = HasTag+Ref MT ∷ _ }} Z = Z
    translate-invoke-pointer {record { response = response ; request-tagged = _ ∷ rt }} (S p) =
      let rec = translate-invoke-pointer {record { request = _ ; response = response ; request-tagged = rt }} p
      in S rec
    translate-send-pointer : ∀ {ct MT} →
                               MT ∈ active-reply-type ct →
                               (TagField ∷ MT) ∈ ct .channel-shape
    translate-send-pointer {record { channel-shape = [] }} ()
    translate-send-pointer {record { all-tagged = HasTag MT ∷ _ }} Z = Z
    translate-send-pointer {record { channel-shape = x ∷ xs ; all-tagged = px ∷ pxs }} (S p) = S (translate-send-pointer p)
    invoke' : {i : Size} {MT : MessageType} →
              All receive-field-content MT →
              (ci : ChannelInitiation) →
              active-method (active-inbox-shape (ac .methods)) (ac .state-type) (ac .vars) ci →
              MT ∈ (ci .request) →
              IsRequestMessage (ci .response .channel-shape) MT →
              ∞ActorM i (active-inbox-shape (ac .methods)) (ac .state-type) (extract-references MT ++ ac .vars state) (λ st → extract-references MT ++ ac .vars st)
    invoke' (tag ∷ _ ∷ f) ci handler p (HasTag+Ref MT) =
      let
        active-message : Message (active-request-type ci)
        active-message = Msg (translate-invoke-pointer p) f
      in do
        record { new-state = new-state ; reply = SendM which fields } ← handler active-message state
        send Z (SendM (translate-send-pointer which) (lift tag ∷ fields))
        return₁ new-state
    invoke : {i : Size} {MT : MessageType} →
             All receive-field-content MT →
             (cis : List ChannelInitiation) →
             All (active-method (active-inbox-shape (ac .methods)) (ac .state-type) (ac .vars)) cis →
             MT ∈ active-inbox-shape cis →
             ∞ActorM i (active-inbox-shape (ac .methods)) (ac .state-type) (add-references-static (ac .vars state) MT) (λ st → add-references-static (ac .vars st) MT)
    invoke _ _ [] ()
    invoke f (ci ∷ _) (_ ∷ _) x with (∈++ (ci .request) _ x)
    invoke f (ci ∷ _) (handler ∷ _) x | Left q =
      let irm = lookup-all q (ci .request-tagged)
      in invoke' f ci handler q irm
    invoke f (_ ∷ cis) (_ ∷ handlers) x | Right q = invoke f cis handlers q

handle-active-method : {i : Size} →
                       (ac : ActiveObject) →
                       (input : Message (active-inbox-shape (ac .methods))) →
                       (state : ac .state-type) →
                       ∞ActorM i (active-inbox-shape (ac .methods))
                         (ac .state-type) (add-references (ac .vars state) input) (ac .vars)
handle-active-method ac input state =
  do
    state' ← (invoke-active-method ac input state)
    forget-message input
    return₁ state'

run-active-object : {i : Size} →
                    (ac : ActiveObject) →
                    (state : ac .state-type) →
                    ∞ActorM i (active-inbox-shape (ac .methods)) (ac .state-type) ((ac .vars) state) (ac .vars)
run-active-object ac state .force =
  receive ∞>>= λ m →
  handle-active-method ac m state >>= λ state' →
  run-active-object ac state'
