module Selective.Examples.TestSelectiveReceive-calc where

open import Selective.ActorMonad
open import Prelude

open import Debug
open import Data.Nat.Show using (show)

UniqueTag = ℕ
TagField = ValueType UniqueTag

ℕ-ReplyMessage : MessageType
ℕ-ReplyMessage = ValueType UniqueTag ∷ [ ValueType ℕ ]ˡ

ℕ-Reply : InboxShape
ℕ-Reply = [ ℕ-ReplyMessage ]ˡ

ℕ×ℕ→ℕ-Message : MessageType
ℕ×ℕ→ℕ-Message = ValueType UniqueTag ∷ ReferenceType ℕ-Reply ∷ ValueType ℕ ∷ [ ValueType ℕ ]ˡ

Calculate : InboxShape
Calculate = [ ℕ×ℕ→ℕ-Message ]ˡ

Calculator : InboxShape
Calculator = ℕ×ℕ→ℕ-Message ∷ [ ℕ×ℕ→ℕ-Message ]ˡ

calculator-actor : ∀ {i} → ∞ActorM (↑ i) Calculator (Lift ⊤) [] (λ _ → [])
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

accept-tagged-ℕ : UniqueTag → MessageFilter TestBox
accept-tagged-ℕ tag (Msg Z (tag' ∷ _)) = ⌊ tag ≟ tag' ⌋
accept-tagged-ℕ tag (Msg (S ()) _)

calculator-test-actor : ∀{i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
calculator-test-actor = do
  spawn∞ calculator-actor
  self
  (S Z ![t: Z ] ((lift 0) ∷ (([ Z ]>: ⊆-refl) ∷ lift 32 ∷ [ lift 10 ]ᵃ)))
  (strengthen (⊆-suc ⊆-refl))
  sm: Msg Z (_ ∷ n ∷ []) [ _ ] ← (selective-receive (accept-tagged-ℕ 0))
    where
      sm: Msg (S ()) _ [ _ ]
  self
  (S Z ![t: S Z ] ((lift 0) ∷ (([ Z ]>: ⊆-refl) ∷ lift 32 ∷ [ lift 10 ]ᵃ)))
  strengthen (⊆-suc ⊆-refl)
  sm: Msg Z (_ ∷ m ∷ []) [ _ ] ← (selective-receive (accept-tagged-ℕ 0))
    where
      sm: Msg (S ()) _ [ _ ]
  strengthen []
  return m
