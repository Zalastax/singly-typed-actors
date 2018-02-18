module Sublist where

open import Data.List
open import Data.List.All
open import Data.List.Any
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Category.Monad
open import Data.Product

open import Membership-equality hiding (_⊆_; set)

infix 3 _⊆_

-- Sublist without re-ordering, to be improved later...
data _⊆_ {a}{A : Set a} : List A → List A → Set a where
  []   : ∀ {ys} → [] ⊆ ys
  keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
  skip : ∀ {x xs ys} → xs ⊆ ys → xs ⊆ x ∷ ys

singleton-⊆ : ∀ {a} {A : Set a} {x : A} {xs : List A} → x ∈ xs → [ x ] ⊆ xs
singleton-⊆ (here refl) = keep []
singleton-⊆ (there mem) = skip (singleton-⊆ mem)

reflexive-⊆ : ∀ {a} {A : Set a} {xs : List A} → xs ⊆ xs
reflexive-⊆ {xs = []} = []
reflexive-⊆ {xs = x ∷ xs} = keep reflexive-⊆

All-⊆ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} → xs ⊆ ys → All P ys → All P xs
All-⊆ [] al = []
All-⊆ (keep inc) (px ∷ al) = px ∷ All-⊆ inc al
All-⊆ (skip inc) (px ∷ al) =  All-⊆ inc al
