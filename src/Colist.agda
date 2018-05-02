module Colist where

open import Size using (Size ; Size<_)

data Colist (i : Size) {a} (A : Set a) : Set a

record ∞Colist (i : Size) {a} (A : Set a) : Set a where
  coinductive
  constructor delay_
  field force : ∀ {j : Size< i} → Colist j A

data Colist (i : Size) {a} (A : Set a) where
  [] : Colist i A
  _∷_ : (x : A) (xs : ∞Colist i A) → Colist i A
