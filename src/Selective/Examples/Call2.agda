module Selective.Examples.Call2 where

open import Selective.ActorMonad public
open import Data.List using (List ; _∷_ ; [] ; _++_ ; map)
open import Data.List.All using (All ; _∷_ ; [])
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _≟_ )
open import Size
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality
            using (_≡_ ; refl ; cong ; sym ; inspect ; [_] ; trans)
open import Membership using (
              _∈_ ; _⊆_ ; S ; Z ; _∷_ ; []
              ; ⊆-refl ; ⊆-trans ; ⊆-suc ; translate-⊆
              )
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)

open SelectedMessage

UniqueTag = ℕ
TagField = ValueType UniqueTag

data IsRequestMessage (IS : InboxShape) : MessageType → Set₁ where
  HasTag+Ref : ∀ MT → IsRequestMessage IS (TagField ∷ ReferenceType IS ∷ MT)

data IsReplyMessage : MessageType → Set₁ where
  HasTag : ∀ MT → IsReplyMessage (TagField ∷ MT)

record CallProtocol : Set₁ where
  field
    request response : InboxShape
    request-tagged : All (IsRequestMessage response) request
    response-tagged : All IsReplyMessage response

open CallProtocol

record CallSession (protocol : CallProtocol) (caller callee : InboxShape): Set₁ where
  field
    can-request : (protocol .request) <: callee
    can-respond : (protocol .response) <: caller

pad-pointer : ∀ {a} {A : Set a} → (l r : List A) → {v : A} → v ∈ r → v ∈ (l ++ r)
pad-pointer [] r p = p
pad-pointer (x ∷ l) r p = S (pad-pointer l r p)

tabulate-suc : ∀ {a} {A : Set a} → {ls : List A} → {x : A} → List (Σ[ v ∈ A ] v ∈ ls) → List (Σ[ v ∈ A ] v ∈ (x ∷ ls))
tabulate-suc [] = []
tabulate-suc ((v , p) ∷ tabs) =
  let rec = tabulate-suc tabs
  in (v , (S p)) ∷ rec

tabulate-∈ : ∀ {a} {A : Set a} → (ls : List A) → List (Σ[ v ∈ A ] v ∈ ls)
tabulate-∈ [] = []
tabulate-∈ (x ∷ ls) =
  let rec = tabulate-∈ ls
  in (x , Z) ∷ tabulate-suc rec


record ReplyCandidate (caller response : InboxShape) : Set₁ where
  field
    MT : MessageType
    original-pointer : MT ∈ response
    reply-pointer : MT ∈ caller
    MT-tagged : IsReplyMessage MT

translate-response : ∀ {resp caller} → resp <: caller → Σ[ v ∈ MessageType ] v ∈ resp → Σ[ v ∈ MessageType ] v ∈ caller
translate-response sub (v , p) = v , (translate-⊆ sub p)

candidates-suc : ∀ {caller x xs} → List (ReplyCandidate caller xs) → List (ReplyCandidate caller (x ∷ xs))
candidates-suc [] = []
candidates-suc (x ∷ candidates) =
  let rec = candidates-suc candidates
      open ReplyCandidate
  in record
       { MT = x .MT
       ; original-pointer = S (x .original-pointer)
       ; reply-pointer = x .reply-pointer
       ; MT-tagged = x .MT-tagged
       } ∷ rec

reply-candidates : {response caller : InboxShape} → All IsReplyMessage response → response <: caller → List (ReplyCandidate caller response)
reply-candidates [] sub = []
reply-candidates (px ∷ irp) (p ∷ sub) =
  let rec = reply-candidates irp sub
      candidate = record { MT = _ ; original-pointer = Z ; reply-pointer = p ; MT-tagged = px }
  in candidate ∷ candidates-suc rec

data DecideAccept : {MT CT : MessageType} {caller : InboxShape} →
                      UniqueTag →
                      MT ∈ caller →
                      CT ∈ caller →
                      IsReplyMessage CT →
                      All receive-field-content MT →
                      Set₁ where
     Acceptable : ∀ {MT caller tag} {rest : All receive-field-content MT} {p : (TagField ∷ MT) ∈ caller} → DecideAccept tag p p (HasTag MT) (tag ∷ rest)
     Unacceptable : ∀ {MT CT caller tag} {p : MT ∈ caller} {q : CT ∈ caller} {irp : IsReplyMessage CT} {fields : All receive-field-content MT} → DecideAccept tag p q irp fields

accept-response-candidate : {MT CT : MessageType} {caller : InboxShape} →
                            (tag : UniqueTag) →
                            (p : MT ∈ caller) →
                            (q : CT ∈ caller) →
                            (irp : IsReplyMessage CT) →
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
open ReplyCandidate

accept-response-unwrapped : {MT : MessageType} {caller response : InboxShape} →
                            UniqueTag →
                            MT ∈ caller →
                            All receive-field-content MT →
                            List (ReplyCandidate caller response) →
                            Bool
accept-response-unwrapped tag p fields [] = false
accept-response-unwrapped tag p fields (candidate ∷ candidates) with (accept-response-candidate tag p (candidate .reply-pointer) (candidate .MT-tagged) fields)
... | Acceptable = true
... | Unaceptable = accept-response-unwrapped tag p fields candidates

accept-response : ∀ {protocol caller callee} → UniqueTag → CallSession protocol caller callee → MessageFilter caller
accept-response {protocol} {caller} tag session (Msg x fields) =
  let
  open CallProtocol
  open CallSession
  candidates = reply-candidates (protocol .response-tagged) (session .can-respond)
    in accept-response-unwrapped tag x fields candidates

record CallResponse (response : InboxShape) (accepted-type : MessageType) : Set₁ where
  field
    accepted-which : accepted-type ∈ response
    fields : All receive-field-content accepted-type


record CallResponse2 (response : InboxShape) : Set₁ where
  field
    accepted-type : MessageType
    vals : CallResponse response accepted-type

convert-response-unwrapped : {MT : MessageType} {caller response : InboxShape} →
                           (tag : UniqueTag) →
                           (x : MT ∈ caller) →
                           (fields : All receive-field-content MT) →
                           (candidates : List (ReplyCandidate caller response)) →
                           (ok : accept-response-unwrapped tag x fields (candidates) ≡ true) →
                           CallResponse response MT
convert-response-unwrapped tag x fields [] ()
convert-response-unwrapped tag x fields (candidate ∷ candidates) ok  with (accept-response-candidate tag x (candidate .reply-pointer) (candidate .MT-tagged) fields)
... | Acceptable = record { accepted-which = candidate .original-pointer ; fields = fields }
... | Unacceptable = convert-response-unwrapped tag x fields candidates ok


convert-response : ∀ {protocol caller callee tag} {session : CallSession protocol caller callee} → (sm : SelectedMessage (accept-response tag session)) → CallResponse (protocol .response) (selected-type sm)
convert-response {protocol = protocol} {tag = tag} {session = session} record { msg = (Msg x fields) ; msg-ok = msg-ok } =
  let
  open CallProtocol
  open CallSession
  candidates = reply-candidates (protocol .response-tagged) (session .can-respond)
    in convert-response-unwrapped tag x fields candidates msg-ok

add-accepted-fields : ∀ {response} → TypingContext → CallResponse2 response → TypingContext
add-accepted-fields Γ response = add-references-static Γ (CallResponse2.accepted-type response)

call : {Γ : TypingContext} {i : Size}
       {caller callee : InboxShape} →
       {MtTo : MessageType} →
       Γ ⊢ callee →
       (protocol : CallProtocol) →
       (TagField ∷ ReferenceType (protocol .response) ∷ MtTo) ∈ (protocol .request) →
       (session : CallSession protocol caller callee) →
       UniqueTag →
       All (send-field-content Γ) MtTo →
       ∞ActorM i caller (CallResponse2 (protocol .response)) Γ (add-accepted-fields Γ)
call {Γ} {caller = caller} {callee = callee} var protocol which session tag fields =
  let
    open CallSession
  in do
    self
    (S var ![t: translate-⊆ (session .can-request) which ] (lift tag ∷ ([ Z ]>: (session .can-respond)) ∷ translate-fields fields) )
    (strengthen (⊆-suc ⊆-refl))
    m@record { msg = Msg {MT} x f ; msg-ok = msg-ok } ← (selective-receive (accept-response tag session))
    let val = (convert-response {protocol} {caller} {callee} {tag} {session} m)
    return₁ (record { accepted-type = MT ; vals = val })
  where
    translate-fields : ∀ {MT} →
                         All (send-field-content Γ) MT →
                         All (send-field-content (caller ∷ Γ)) MT
    translate-fields [] = []
    translate-fields {ValueType x ∷ MT} (px ∷ vals) =
      px ∷ (translate-fields vals)
    translate-fields {ReferenceType x ∷ MT} (([ p ]>: v) ∷ vals) =
      ([ (S p) ]>: v) ∷ (translate-fields vals)

CalculatorResponse : InboxShape
CalculatorResponse = (
  ValueType UniqueTag ∷
  ValueType ℕ ∷ []) ∷ []

Calculator : InboxShape
Calculator = (
  ValueType UniqueTag ∷
  ReferenceType CalculatorResponse ∷
  ValueType ℕ ∷
  ValueType ℕ ∷ []
  ) ∷ []

CalculatorProtocol : CallProtocol
CalculatorProtocol = record
                       { request = Calculator
                       ; response = CalculatorResponse
                       ; request-tagged = (HasTag+Ref (ValueType ℕ ∷ ValueType ℕ ∷ [])) ∷ []
                       ; response-tagged = (HasTag (ValueType ℕ ∷ [])) ∷ []
                       }

calculatorActor : ∀ {i} → ∞ActorM (↑ i) Calculator (Lift ⊤) [] (λ _ → [])
calculatorActor .force = receive ∞>>= λ {
  (Msg Z (tag ∷ _ ∷ n ∷ m ∷ [])) .force →
    (Z ![t: Z ] ((lift tag) ∷ (lift (n + m)) ∷ [])) ∞>> (do
    strengthen []
    calculatorActor)
  ; (Msg (S ()) _)
  }

TestBox : InboxShape
TestBox = (
  ValueType UniqueTag ∷
  ValueType ℕ ∷ []) ∷
  [] ∷ []

calltestActor : ∀{i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
calltestActor = do
  (spawn∞ calculatorActor)
  record { vals = record { accepted-which = Z ; fields = tag ∷ n ∷ []} } ← (call Z CalculatorProtocol Z (record { can-request = ⊆-refl ; can-respond = Z ∷ [] }) 0 ((lift 32) ∷ ((lift 10) ∷ [])))
    where
      record { vals = record { accepted-which = S () }}
  (strengthen [])
  (return n)
