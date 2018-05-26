module Selective.Examples.TestCall2 where

open import Selective.Libraries.Call2
open import Prelude

AddReplyMessage : MessageType
AddReplyMessage = ValueType UniqueTag ∷ [ ValueType ℕ ]ˡ

AddReply : InboxShape
AddReply = [ AddReplyMessage ]ˡ

AddMessage : MessageType
AddMessage = ValueType UniqueTag ∷ ReferenceType AddReply ∷ ValueType ℕ ∷ [ ValueType ℕ ]ˡ

Calculator : InboxShape
Calculator = [ AddMessage ]ˡ

CalculatorProtocol : ChannelInitiation
CalculatorProtocol = record
                       { request = Calculator
                       ; response = record {
                         channel-shape = AddReply
                         ; all-tagged = (HasTag _) ∷ []
                         }
                       ; request-tagged = [ HasTag+Ref _ ]ᵃ
                       }

calculatorActor : ∀ {i} → ∞ActorM (↑ i) Calculator (Lift ⊤) [] (λ _ → [])
calculatorActor .force = receive ∞>>= λ {
  (Msg Z (tag ∷ _ ∷ n ∷ m ∷ [])) .force →
    Z ![t: Z ] (lift tag ∷ [ lift (n + m) ]ᵃ) ∞>> (do
    strengthen []
    calculatorActor)
  ; (Msg (S ()) _)
  }

TestBox : InboxShape
TestBox = AddReply

calltestActor : ∀{i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
calltestActor = do
  (spawn∞ calculatorActor)
  Msg Z (tag ∷ n ∷ []) ← call CalculatorProtocol (record {
    var = Z
    ; chosen-field = Z
    ; fields = (lift 32) ∷ [ lift 10 ]ᵃ
    ; session = record {
      can-request = ⊆-refl
      ; response-session = record {
        can-receive = [ Z ]ᵐ
        ; tag = 0
        }
      }
    })
    where
      Msg (S ()) _
  (strengthen [])
  (return n)
