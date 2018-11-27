module Selective.Examples.TestAO where

open import Selective.ActorMonad
open import Prelude
open import Selective.Libraries.Call2
open import Selective.Libraries.ActiveObjects

open import Debug
open import Data.Nat.Show using (show)

ℕ-ReplyMessage : MessageType
ℕ-ReplyMessage = ValueType UniqueTag ∷ [ ValueType ℕ ]ˡ

ℕ-Reply : InboxShape
ℕ-Reply = [ ℕ-ReplyMessage ]ˡ

ℕ×ℕ→ℕ-Message : MessageType
ℕ×ℕ→ℕ-Message = ValueType UniqueTag ∷ ReferenceType ℕ-Reply ∷ ValueType ℕ ∷ [ ValueType ℕ ]ˡ

Calculate : InboxShape
Calculate = [ ℕ×ℕ→ℕ-Message ]ˡ

CalculateProtocol : ChannelInitiation
CalculateProtocol = record
                       { request = Calculate
                       ; response = record {
                         channel-shape = ℕ-Reply
                         ; all-tagged = (HasTag _) ∷ []
                         }
                       ; request-tagged = [ HasTag+Ref _ ]ᵃ
                       }

ℕ×ℕ→ℕ-ci : ChannelInitiation
ℕ×ℕ→ℕ-ci = record {
  request = Calculate
  ; response = record { channel-shape = ℕ-Reply ; all-tagged = (HasTag _) ∷ [] }
  ; request-tagged = (HasTag+Ref _) ∷ [] }

add-method-header = ResponseMethod ℕ×ℕ→ℕ-ci
multiply-method-header = ResponseMethod ℕ×ℕ→ℕ-ci

calculator-methods : List ActiveMethod
calculator-methods = add-method-header ∷ multiply-method-header ∷ []

calculator-inbox = methods-shape calculator-methods

calculator-state-vars : ⊤₁ → TypingContext
calculator-state-vars _ = []

add : (active-method calculator-inbox ⊤₁ calculator-state-vars add-method-header)
add _ (_ sent Msg Z (n ∷ m ∷ [])) v = return₁ (record { new-state = _ ; reply = SendM Z  [ lift (n + m)]ᵃ })
add _ (_ sent Msg (S ()) _) _

multiply : (active-method calculator-inbox ⊤₁ (λ _ → []) multiply-method-header)
multiply _ (_ sent Msg Z (n ∷ m ∷ [])) v = return₁ (record { new-state = _ ; reply = SendM Z [ lift (n * m)]ᵃ })
multiply _ (_ sent Msg (S ()) _) _

calculator : ActiveObject
calculator = record {
  state-type = ⊤₁
  ; vars = calculator-state-vars
  ; methods = calculator-methods
  ; extra-messages = []
  ; handlers = add ∷ multiply ∷ []
  }

calculator-actor = run-active-object calculator _


TestBox : InboxShape
TestBox = ℕ-Reply


-- import Selective.Examples.CalculatorProtocol as CP
-- calculator-test-actor = CP.calculator-test-actor calculator-actor

calculator-test-actor : ∀{i} → ∞ActorM i TestBox (Lift (lsuc lzero) ℕ) [] (λ _ → [])
calculator-test-actor = do
  spawn∞ calculator-actor
  Msg Z (_ ∷ n ∷ []) ← call CalculateProtocol (record {
    var = Z
    ; chosen-field = Z
    ; fields = lift 32 ∷ [ lift 10 ]ᵃ
    ; session = record {
      can-request = [ Z ]ᵐ -- Pick add method
      ; response-session = record {
        can-receive = [ Z ]ᵐ
        ; tag = 0
        }
      }
    })
    where
      Msg (S ()) _
  Msg Z (_ ∷ m ∷ []) ← debug (show n) (call CalculateProtocol (record {
    var = Z
    ; chosen-field = Z
    ; fields = lift n ∷ [ lift 10 ]ᵃ
    ; session = record {
      can-request = [ S Z ]ᵐ -- Pick multiply method
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
