module Examples.InfiniteBind where

open import ActorMonad
open import Prelude

Box : InboxShape
Box = []

binder : ∀ {i} → ∞ActorM i Box ⊤₁ [] (λ _ → [])
binder .force = binder ∞>> binder

