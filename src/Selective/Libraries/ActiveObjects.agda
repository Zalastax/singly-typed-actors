module Selective.Libraries.ActiveObjects where

open import Selective.Libraries.Channel public
open import Prelude

open ChannelType
open ChannelInitiation

data ActiveMethod : Set₁ where
  VoidMethod : InboxShape → ActiveMethod
  ResponseMethod : ChannelInitiation → ActiveMethod

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

active-method : InboxShape → (state-type : Set₁) → (state-type → TypingContext) → ActiveMethod → Set₂
active-method IS st var-f (VoidMethod IS') =
  let input-type = Message IS'
  in (i : Size) →
     (input : input-type) →
     (state : st) →
     ∞ActorM i IS
       st
       (add-references (var-f state) input)
       (λ state' → add-references (var-f state') input)
active-method IS st var-f (ResponseMethod ci) =
  let input-type = Message (active-request-type ci)
  in (i : Size) →
     (caller : InboxShape) →
     (input : input-type) →
     (state : st) →
     ∞ActorM i IS
       (ActiveReply ci st var-f input caller)
       (caller ∷ add-references (var-f state) input)
       (reply-vars var-f input caller)

active-method-request : ActiveMethod → InboxShape
active-method-request (VoidMethod x) = x
active-method-request (ResponseMethod x) = x .request

methods-shape : List ActiveMethod → InboxShape
methods-shape [] = []
methods-shape (am ∷ lci) =
  let rec = methods-shape lci
      am-shape = active-method-request am
  in am-shape ++ rec

record ActiveObject : Set₂ where
  field
    state-type : Set₁
    vars : state-type → TypingContext
    methods : List ActiveMethod
    extra-messages : InboxShape
    handlers : All (active-method (methods-shape methods ++ extra-messages) state-type vars) methods

active-inbox-shape : ActiveObject → InboxShape
active-inbox-shape ac =
  let open ActiveObject
  in methods-shape (ac .methods) ++ (ac .extra-messages)

open ActiveObject

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
                       (input : Message (methods-shape (ac .methods))) →
                       (state : ac .state-type) →
                       ∞ActorM i (active-inbox-shape ac)
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

    invoke-void-method : {i : Size} {MT : MessageType} →
             All receive-field-content MT →
             (IS : InboxShape) →
             active-method (active-inbox-shape ac) (ac .state-type) (ac .vars) (VoidMethod IS) →
             MT ∈ IS →
             ∞ActorM i (active-inbox-shape ac) (ac .state-type) (extract-references MT ++ ac .vars state) (λ st → extract-references MT ++ ac .vars st)
    invoke-void-method f IS handler p =
      let
        active-message : Message IS
        active-message = Msg p f
      in do
        new-state ← handler _ active-message state
        return₁ new-state
    invoke-reply-method : {i : Size} {MT : MessageType} →
              All receive-field-content MT →
              (ci : ChannelInitiation) →
              active-method (active-inbox-shape ac) (ac .state-type) (ac .vars) (ResponseMethod ci) →
              MT ∈ (ci .request) →
              IsRequestMessage (ci .response .channel-shape) MT →
              ∞ActorM i (active-inbox-shape ac) (ac .state-type) (extract-references MT ++ ac .vars state) (λ st → extract-references MT ++ ac .vars st)
    invoke-reply-method (tag ∷ _ ∷ f) ci handler p (HasTag+Ref MT) =
      let
        active-message : Message (active-request-type ci)
        active-message = Msg (translate-invoke-pointer p) f
      in do
        record { new-state = new-state ; reply = SendM which fields } ← handler _ _ active-message state
        send Z (SendM (translate-send-pointer which) (lift tag ∷ fields))
        return₁ new-state
    invoke : {i : Size} {MT : MessageType} →
             All receive-field-content MT →
             (ams : List ActiveMethod) →
             All (active-method (active-inbox-shape ac) (ac .state-type) (ac .vars)) ams →
             MT ∈ methods-shape ams →
             ∞ActorM i (active-inbox-shape ac)
                       (ac .state-type)
                       (add-references-static (ac .vars state) MT)
                       (λ st → add-references-static (ac .vars st) MT)
    invoke _ _ [] ()
    invoke f (am ∷ _) (_ ∷ _) x with (∈++ (active-method-request am) _ x)
    invoke f (VoidMethod IS ∷ _) (handler ∷ _) x | Left q = invoke-void-method f IS handler q
    invoke f (ResponseMethod ci ∷ _) (handler ∷ _) x | Left q =
      let irm = lookup-all q (ci .request-tagged)
      in invoke-reply-method f ci handler q irm
    invoke f (_ ∷ cis) (_ ∷ handlers) x | Right q = invoke f cis handlers q


handle-active-method : {i : Size} →
                       (ac : ActiveObject) →
                       (input : Message (methods-shape (ac .methods))) →
                       (state : ac .state-type) →
                       ∞ActorM i (active-inbox-shape ac)
                         (ac .state-type) (add-references (ac .vars state) input) (ac .vars)
handle-active-method ac input state =
  do
    state' ← (invoke-active-method ac input state)
    forget-message input
    return₁ state'

accept-sublist-unwrapped : (xs ys zs : InboxShape) → ∀{MT} → MT ∈ (xs ++ ys ++ zs) → Bool
accept-sublist-unwrapped [] [] zs p = false
accept-sublist-unwrapped [] (y ∷ ys) zs Z = true
accept-sublist-unwrapped [] (y ∷ ys) zs (S p) = accept-sublist-unwrapped [] ys zs p
accept-sublist-unwrapped (x ∷ xs) ys zs Z = false
accept-sublist-unwrapped (x ∷ xs) ys zs (S p) = accept-sublist-unwrapped xs ys zs p


accept-sublist : (xs ys zs : InboxShape) → MessageFilter (xs ++ ys ++ zs)
accept-sublist xs ys zs (Msg received-message-type received-fields) = accept-sublist-unwrapped xs ys zs received-message-type

record AcceptSublistDependent (IS : InboxShape) (accepted-type : MessageType) : Set₁ where
  field
    accepted-which : accepted-type ∈ IS
    fields : All receive-field-content accepted-type

receive-active-method : {i : Size} →
                        {Γ : TypingContext} →
                        (ac : ActiveObject) →
                        ∞ActorM i (active-inbox-shape ac) (Message (methods-shape (ac .methods))) Γ (add-references Γ)
receive-active-method ac = do
    record { msg = Msg {MT} p f ; msg-ok = msg-ok } ← selective-receive (accept-sublist [] (methods-shape (ac .methods)) (ac .extra-messages))
    let record {accepted-which = aw ; fields = fields } = rewrap-message (methods-shape (ac .methods)) (ac .extra-messages) p f msg-ok
    return₁ (Msg {MT = MT} aw fields)
  where
    rewrap-message : ∀{MT} → (ys zs : InboxShape) → (p : MT ∈ (ys ++ zs)) → All receive-field-content MT → (accept-sublist-unwrapped [] ys zs p) ≡ true → AcceptSublistDependent ys MT
    rewrap-message [] zs which f ()
    rewrap-message (x ∷ ys) zs Z f p = record { accepted-which = Z ; fields = f }
    rewrap-message (x ∷ ys) zs (S which) f p =
      let
        rec = rewrap-message ys zs which f p
        open AcceptSublistDependent
      in record { accepted-which = S (rec .accepted-which) ; fields = rec .fields }

run-active-object : {i : Size} →
                    (ac : ActiveObject) →
                    (state : ac .state-type) →
                    ∞ActorM (↑ i) (active-inbox-shape ac) (ac .state-type) ((ac .vars) state) (ac .vars)
run-active-object ac state .force =
  receive-active-method ac ∞>>= λ { m .force →
  handle-active-method ac m state ∞>>= λ state' →
  run-active-object ac state'
  }
