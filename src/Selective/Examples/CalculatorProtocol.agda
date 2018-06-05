module Selective.Examples.CalculatorProtocol where

open import Selective.Libraries.Call2
open import Prelude

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

Calculator : InboxShape
Calculator = ℕ×ℕ→ℕ-Message ∷ [ ℕ×ℕ→ℕ-Message ]ˡ

TestBox : InboxShape
TestBox = ℕ-Reply

calculator-test-actor : ∀{i} →
  ∞ActorM (↑ i) Calculator (Lift ⊤) [] (λ _ → []) →
  ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
calculator-test-actor calculator-actor = do
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
