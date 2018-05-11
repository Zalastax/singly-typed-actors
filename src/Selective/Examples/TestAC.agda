module Selective.Examples.TestAC where

open import Selective.ActorMonad
open import Prelude
open import Selective.Examples.Channel
open import Selective.Examples.Call2
open import Selective.Examples.ActiveObjects


open import Debug
open import Data.Nat.Show using (show)

calculator-ci : ChannelInitiation
calculator-ci = record {
  request = Calculator
  ; response = record { channel-shape = AddReply ; all-tagged = (HasTag _) ∷ [] }
  ; request-tagged = (HasTag+Ref _) ∷ [] }

calculator-methods : List ChannelInitiation
calculator-methods = calculator-ci ∷ calculator-ci ∷ []

calculator-inbox = active-inbox-shape calculator-methods

add : (active-method calculator-inbox ⊤₁ (λ _ → []) calculator-ci)
add (Msg Z (n ∷ m ∷ [])) v = return₁ (record { new-state = _ ; reply = SendM Z  [ lift (n + m)]ᵃ })
add (Msg (S ()) _) _

multiply : (active-method calculator-inbox ⊤₁ (λ _ → []) calculator-ci)
multiply (Msg Z (n ∷ m ∷ [])) v = return₁ (record { new-state = _ ; reply = SendM Z [ lift (n * m)]ᵃ })
multiply (Msg (S ()) _) _

calculator : ActiveObject
calculator = record {
  state-type = ⊤₁
  ; vars = λ _ → []
  ; methods = calculator-methods
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
