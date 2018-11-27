module Selective.Examples.TestChannel where

open import Selective.Libraries.Channel
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

calculator-actor : ∀ {i} → ∞ActorM (↑ i) Calculator (Lift (lsuc lzero) ⊤) [] (λ _ → [])
calculator-actor .force = receive ∞>>= λ {
  (Msg Z (tag ∷ _ ∷ n ∷ m ∷ [])) .force →
    Z ![t: Z ] (lift tag ∷ [ lift (n + m) ]ᵃ) ∞>> (do
    strengthen []
    calculator-actor)
  ; (Msg (S Z) (tag ∷ _ ∷ n ∷ m ∷ [])) .force →
    (Z ![t: Z ] (lift tag ∷ ([ lift (n * m) ]ᵃ))) ∞>> (do
    (strengthen [])
    calculator-actor)
  ; (Msg (S (S ())) _)
  }

TestBox : InboxShape
TestBox = ℕ-Reply

calculator-test-actor : ∀{i} → ∞ActorM i TestBox (Lift (lsuc lzero) ℕ) [] (λ _ → [])
calculator-test-actor = do
  spawn∞ calculator-actor
  let add-request = (record {
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
    add-rs = add-request .session .response-session
  initiate-channel _ add-request
  Msg Z (_ ∷ n ∷ []) ← from-channel (CalculateProtocol .response) add-rs
    where
      Msg (S ()) _
  let mult-request = (record {
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
    })
    mult-rs = add-rs = mult-request .session .response-session
  Msg Z (_ ∷ m ∷ []) ← from-channel (CalculateProtocol .response) mult-rs
    where
      Msg (S ()) _
  debug (show m) (strengthen [])
  return m
