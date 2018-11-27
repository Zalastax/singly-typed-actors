module Selective.Examples.TestCall where

open import Selective.Libraries.Call
open import Prelude

AddReplyMessage : MessageType
AddReplyMessage = ValueType UniqueTag ∷ [ ValueType ℕ ]ˡ

AddReply : InboxShape
AddReply = [ AddReplyMessage ]ˡ

AddMessage : MessageType
AddMessage = ValueType UniqueTag ∷ ReferenceType AddReply ∷ ValueType ℕ ∷ [ ValueType ℕ ]ˡ

Calculator : InboxShape
Calculator = [ AddMessage ]ˡ

calculatorActor : ∀ {i} → ∞ActorM (↑ i) Calculator (Lift (lsuc lzero) ⊤) [] (λ _ → [])
calculatorActor .force = receive ∞>>= λ {
  (Msg Z (tag ∷ _ ∷ n ∷ m ∷ [])) .force →
    (Z ![t: Z ] (lift tag ∷ [ lift (n + m) ]ᵃ)) ∞>> (do
    strengthen []
    calculatorActor)
  ; (Msg (S ()) _)
  }

TestBox : InboxShape
TestBox = AddReply

calltestActor : ∀{i} → ∞ActorM i TestBox (Lift (lsuc lzero) ℕ) [] (λ _ → [])
calltestActor .force = spawn∞ calculatorActor ∞>> do
    x ← call Z Z 0
         ((lift 10) ∷ [ lift 32 ]ᵃ)
         ⊆-refl Z
    strengthen []
    return-result x
  where
    return-result : SelectedMessage {TestBox} (call-select 0 [ Z ]ᵐ Z) →
                    ∀ {i} → ∞ActorM i TestBox (Lift (lsuc lzero) ℕ) [] (λ _ → [])
    return-result record { msg = (Msg Z (tag ∷ n ∷ [])) } = return n
    return-result record { msg = (Msg (S x) x₁) ; msg-ok = () }