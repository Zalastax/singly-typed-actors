module Selective.Examples.TestAO where

open import Selective.ActorMonad
open import Prelude
open import Selective.Libraries.Call2
open import Selective.Libraries.ActiveObjects


open import Debug
open import Data.Nat.Show using (show)

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

TestBox : InboxShape
TestBox = AddReply

calculator-ci : ChannelInitiation
calculator-ci = record {
  request = Calculator
  ; response = record { channel-shape = AddReply ; all-tagged = (HasTag _) ∷ [] }
  ; request-tagged = (HasTag+Ref _) ∷ [] }

add-method-header = ResponseMethod calculator-ci
multiply-method-header = ResponseMethod calculator-ci

calculator-methods : List ActiveMethod
calculator-methods = add-method-header ∷ multiply-method-header ∷ []

calculator-inbox = methods-shape calculator-methods

calculator-state-vars : ⊤₁ → TypingContext
calculator-state-vars _ = []

add : (active-method calculator-inbox ⊤₁ calculator-state-vars add-method-header)
add _ _ (Msg Z (n ∷ m ∷ [])) v = return₁ (record { new-state = _ ; reply = SendM Z  [ lift (n + m)]ᵃ })
add _ _ (Msg (S ()) _) _

multiply : (active-method calculator-inbox ⊤₁ (λ _ → []) multiply-method-header)
multiply _ _ (Msg Z (n ∷ m ∷ [])) v = return₁ (record { new-state = _ ; reply = SendM Z [ lift (n * m)]ᵃ })
multiply _ _ (Msg (S ()) _) _

calculator : ActiveObject
calculator = record {
  state-type = ⊤₁
  ; vars = calculator-state-vars
  ; methods = calculator-methods
  ; extra-messages = []
  ; handlers = add ∷ multiply ∷ []
  }

calculator-actor = run-active-object calculator _

calculator-test-actor : ∀{i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
calculator-test-actor = do
  spawn∞ calculator-actor
  Msg Z (_ ∷ n ∷ []) ← call CalculatorProtocol (record {
    var = Z
    ; chosen-field = Z
    ; fields = lift 32 ∷ [ lift 10 ]ᵃ
    ; session = record {
      can-request = [ Z ]ᵐ
      ; response-session = record {
        can-receive = [ Z ]ᵐ
        ; tag = 0
        }
      }
    })
    where
      Msg (S ()) _
  Msg Z (_ ∷ m ∷ []) ← debug (show n) (call CalculatorProtocol (record {
    var = Z
    ; chosen-field = Z
    ; fields = lift 32 ∷ [ lift 10 ]ᵃ
    ; session = record {
      can-request = [ S Z ]ᵐ
      ; response-session = record {
        can-receive = [ Z ]ᵐ
        ; tag = 1
        }
      }
    }))
    where
      Msg (S ()) _
  debug (show m) (strengthen [])
  return m
