module Membership where
open import Data.List.Any.Membership.Propositional public

open import Data.List
open import Data.List.Any
open import Data.List.All
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

All-⊆ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} → xs ⊆ ys → All P ys → All P xs
All-⊆ {xs = []} {ys} subs pys = []
All-⊆ {xs = x ∷ xs} {ys} subs pys = lookup pys (subs (here refl)) ∷ All-⊆ (λ q → subs (there q)) pys
