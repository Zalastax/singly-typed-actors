module Singleton where

open import Data.List
  using (List ; [] ; _∷_)
open import Data.List.All
  using (All ; [] ; _∷_)
open import Membership
  using (_∈_; _⊆_ ; _∷_ ; [])

[_]ˡ : ∀{a}{A : Set a} → A → List A
[ a ]ˡ = a ∷ []

[_]ᵃ : ∀{a p} {A : Set a} {P : A → Set p} {x : A} → P x → All P (x ∷ [])
[ p ]ᵃ = p ∷ []

[_]ᵐ :  ∀{a} {A : Set a} {x : A} {ys : List A} → (x ∈ ys) → ((x ∷ []) ⊆ ys)
[ p ]ᵐ = p ∷ []
