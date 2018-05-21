module Examples.TestCall where

open import Prelude
open import Libraries.SelectiveReceive
open import Libraries.Call

open SelRec

AddReplyMessage : MessageType
AddReplyMessage = ValueType UniqueTag ∷ [ ValueType ℕ ]ˡ

AddReply : InboxShape
AddReply = [ AddReplyMessage ]ˡ

AddMessage : MessageType
AddMessage = ValueType UniqueTag ∷ ReferenceType AddReply ∷ ValueType ℕ ∷ [ ValueType ℕ ]ˡ

Calculator : InboxShape
Calculator = [ AddMessage ]ˡ

calculatorActor : ∀ {i} → ∞ActorM (↑ i) Calculator (Lift ⊤) [] (λ _ → [])
calculatorActor = loop
  where
    loop : ∀ {i} → ∞ActorM i Calculator (Lift ⊤) [] (λ _ → [])
    loop .force = receive ∞>>= λ {
      (Msg Z (tag ∷ _ ∷ n ∷ m ∷ [])) → do
        Z ![t: Z ] ((lift tag) ∷ [ lift (n + m) ]ᵃ )
        strengthen []
        loop
      ; (Msg (S ()) _) }

TestBox : InboxShape
TestBox = AddReply

calltestActor : ∀ {i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
calltestActor .force = spawn∞ calculatorActor ∞>> do
    x ← call [] Z Z 0
         ((lift 10) ∷ [ lift 32 ]ᵃ)
         ⊆-refl Z
    strengthen []
    return-result x
  where
    return-result : SelRec TestBox (call-select 0 ⊆-refl Z) →
                    ∀ {i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
    return-result record { msg = (Msg Z (tag ∷ n ∷ [])) } = return n
    return-result record { msg = (Msg (S x) x₁) ; msg-ok = () }
