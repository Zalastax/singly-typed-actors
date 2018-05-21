module Selective.Libraries.Channel where

open import Selective.ActorMonad public
open import Prelude

UniqueTag = ℕ
TagField = ValueType UniqueTag

data IsChannelMessage : MessageType → Set₁ where
  HasTag : ∀ MT → IsChannelMessage (TagField ∷ MT)

record ChannelType : Set₁ where
  field
    channel-shape : InboxShape
    all-tagged : All IsChannelMessage channel-shape

open ChannelType

record ChannelSession (channel : ChannelType) (receiver : InboxShape): Set₁ where
  field
    can-receive : (channel .channel-shape) <: receiver
    tag : UniqueTag

record ChannelCandidate (channel-shape receiver : InboxShape) : Set₁ where
  field
    MT : MessageType
    channel-pointer : MT ∈ channel-shape
    receiver-pointer : MT ∈ receiver
    MT-tagged : IsChannelMessage MT

candidates-suc : ∀ {channel-shape x xs} → List (ChannelCandidate channel-shape xs) → List (ChannelCandidate (x ∷ channel-shape) xs)
candidates-suc [] = []
candidates-suc (x ∷ candidates) =
  let rec = candidates-suc candidates
      open ChannelCandidate
  in record
       { MT = x .MT
       ; channel-pointer = S (x .channel-pointer)
       ; receiver-pointer = x .receiver-pointer
       ; MT-tagged = x .MT-tagged
       } ∷ rec

channel-candidates : {channel-shape receiver : InboxShape} → All IsChannelMessage channel-shape → channel-shape <: receiver → List (ChannelCandidate channel-shape receiver)
channel-candidates [] sub = []
channel-candidates (px ∷ icm) (p ∷ sub) =
  let rec = channel-candidates icm sub
      candidate = record
                    { MT = _
                    ; channel-pointer = Z
                    ; receiver-pointer = p
                    ; MT-tagged = px
                    }
  in candidate ∷ candidates-suc rec

data DecideAccept : {MT CT : MessageType} {caller : InboxShape} →
                      UniqueTag →
                      MT ∈ caller →
                      CT ∈ caller →
                      IsChannelMessage CT →
                      All receive-field-content MT →
                      Set₁ where
     Acceptable : ∀ {MT caller tag}
                    {rest : All receive-field-content MT}
                    {p : (TagField ∷ MT) ∈ caller} →
                    DecideAccept tag p p (HasTag MT) (tag ∷ rest)
     Unacceptable : ∀ {MT CT caller tag}
                      {p : MT ∈ caller}
                      {q : CT ∈ caller}
                      {irp : IsChannelMessage CT}
                      {fields : All receive-field-content MT} →
                      DecideAccept tag p q irp fields

accept-response-candidate : {MT CT : MessageType} {receiver : InboxShape} →
                            (tag : UniqueTag) →
                            (p : MT ∈ receiver) →
                            (q : CT ∈ receiver) →
                            (irp : IsChannelMessage CT) →
                            (fields : All receive-field-content MT) →
                            DecideAccept tag p q irp fields
accept-response-candidate tag Z Z (HasTag MT) (tag' ∷ fields) with (tag ≟ tag')
... | (yes refl) = Acceptable
... | (no _) = Unacceptable
accept-response-candidate tag Z (S q) irm fields = Unacceptable
accept-response-candidate tag (S p) Z irm fields = Unacceptable
accept-response-candidate tag (S p) (S q) irm fields with (accept-response-candidate tag p q irm fields)
... | Acceptable = Acceptable
... | Unacceptable = Unacceptable

open ChannelCandidate

accept-response-unwrapped : {MT : MessageType} {channel-shape receiver : InboxShape} →
                            UniqueTag →
                            MT ∈ receiver →
                            All receive-field-content MT →
                            List (ChannelCandidate channel-shape receiver) →
                            Bool
accept-response-unwrapped tag p fields [] = false
accept-response-unwrapped tag p fields (candidate ∷ candidates) with (accept-response-candidate tag p (candidate .receiver-pointer) (candidate .MT-tagged) fields)
... | Acceptable = true
... | Unaceptable = accept-response-unwrapped tag p fields candidates


accept-response : ∀ {ct receiver} → ChannelSession ct receiver → MessageFilter receiver
accept-response {ct} {receiver} session (Msg x fields) =
  let
  open ChannelType
  open ChannelSession
  candidates = channel-candidates (ct .all-tagged) (session .can-receive)
    in accept-response-unwrapped (session .tag) x fields candidates

record ChannelMessageDependent (channel-shape : InboxShape) (accepted-type : MessageType) : Set₁ where
  field
    accepted-which : accepted-type ∈ channel-shape
    fields : All receive-field-content accepted-type

convert-response-unwrapped : {MT : MessageType} {channel-shape receiver : InboxShape} →
                           (tag : UniqueTag) →
                           (x : MT ∈ receiver) →
                           (fields : All receive-field-content MT) →
                           (candidates : List (ChannelCandidate channel-shape receiver)) →
                           (ok : accept-response-unwrapped tag x fields candidates ≡ true) →
                           ChannelMessageDependent channel-shape MT
convert-response-unwrapped tag x fields [] ()
convert-response-unwrapped tag x fields (candidate ∷ candidates) ok  with (accept-response-candidate tag x (candidate .receiver-pointer) (candidate .MT-tagged) fields)
... | Acceptable = record { accepted-which = candidate .channel-pointer ; fields = fields }
... | Unacceptable = convert-response-unwrapped tag x fields candidates ok


convert-response : ∀ {ct receiver} {session : ChannelSession ct receiver} →
                     (sm : SelectedMessage (accept-response session)) →
                     ChannelMessageDependent (ct .channel-shape) (selected-type sm)
convert-response {ct} {session = session} record { msg = (Msg x fields) ; msg-ok = msg-ok } =
  let
  open ChannelType
  open ChannelSession
  candidates = channel-candidates (ct .all-tagged) (session .can-receive)
    in convert-response-unwrapped (session .tag) x fields candidates msg-ok

from-channel : ∀ {Γ i receiver} →
               ∀ ct →
               ChannelSession ct receiver →
               ∞ActorM i receiver (Message (ct .channel-shape)) Γ (add-references Γ)
from-channel ct cs =
  let
    open ChannelType
    open ChannelSession
    open Message
  in do
    m@record { msg = msg ; msg-ok = msg-ok } ← selective-receive (accept-response cs)
    let record { accepted-which = aw ; fields = fields } = convert-response {session = cs} m
    return₁ (Msg {MT = msg .MT} aw fields)


data IsRequestMessage (IS : InboxShape) : MessageType → Set₁ where
  HasTag+Ref : ∀ MT → IsRequestMessage IS (TagField ∷ ReferenceType IS ∷ MT)

record ChannelInitiation : Set₁ where
  field
    request : InboxShape
    response : ChannelType
    request-tagged : All (IsRequestMessage (response .channel-shape)) request

open ChannelInitiation

record ChannelInitiationSession (ci : ChannelInitiation) (caller callee : InboxShape): Set₁ where
  field
    can-request : (ci .request) <: callee
    response-session : ChannelSession (ci .response) caller

extra-fields-shape : ∀ {IS Mt} → IsRequestMessage IS Mt → MessageType
extra-fields-shape (HasTag+Ref Mt) = Mt

extra-fields : ∀ {IS Mt} → (Γ : TypingContext) → IsRequestMessage IS Mt → Set₁
extra-fields Γ irm = All (send-field-content Γ) (extra-fields-shape irm)

record Request (Γ : TypingContext) (caller : InboxShape) (ci : ChannelInitiation) : Set₁ where
  field
    {callee} : InboxShape
    var : Γ ⊢ callee
    {MtTo} : MessageType
    chosen-field : MtTo ∈ (ci .request)
    fields : extra-fields Γ (lookup-all chosen-field (ci .request-tagged))
    session : ChannelInitiationSession ci caller callee

suc-send-field-content : ∀ {Γ IS F} → send-field-content Γ F → send-field-content (IS ∷ Γ) F
suc-send-field-content {F = ValueType x} sfc = sfc
suc-send-field-content {F = ReferenceType x} ([ actual-is-sendable ]>: actual-handles-requested) = [ S actual-is-sendable ]>: actual-handles-requested

initiate-channel-fields :
  ∀ {Γ caller ci} →
  (request : Request Γ caller ci) →
  All (send-field-content (caller ∷ Γ)) (Request.MtTo request)
initiate-channel-fields {ci = ci} record {
  chosen-field = chosen-field
  ; fields = fields
  ; session = session
  } with (lookup-all chosen-field (ci .request-tagged))
... | HasTag+Ref _ =
  let open ChannelSession
      open ChannelInitiationSession
      channel = session .response-session
  in (lift (channel .tag)) ∷ (([ Z ]>: (channel .can-receive)) ∷ ∀map suc-send-field-content fields)

initiate-channel : ∀ {Γ i receiver} →
                   ∀ ci →
                   Request Γ receiver ci →
                   ∞ActorM i receiver ⊤₁ Γ (λ _ → Γ)
initiate-channel ci request =
  let
    open Request
    open ChannelInitiationSession
  in do
    self
    let protocol-to-callee = translate-⊆ (request .session .can-request)
    S (request .var) ![t: protocol-to-callee (request .chosen-field) ] initiate-channel-fields request
    strengthen (⊆-suc ⊆-refl)
