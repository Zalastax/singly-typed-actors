{-# OPTIONS --allow-unsolved-metas #-}
module Membership where
-- open import Data.List.Any.Membership.Propositional public

open import Data.List
open import Data.List.Any using ()
open import Data.List.All using (All ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Empty using (⊥)

data _∈_ {a} {A : Set a} : A → (List A) -> Set a where
  Z : ∀ {x xs} → x ∈ (x ∷ xs)
  S : ∀ {x y xs} → x ∈ xs -> x ∈ (y ∷ xs)

x∈[]-⊥ : ∀ {a} {A : Set a} {x : A} → x ∈ [] → ⊥
x∈[]-⊥ ()

data _⊆_ {a} {A : Set a} : List A -> List A -> Set a where
  [] : ∀ {xs} → [] ⊆ xs
  _∷_ : ∀ {x xs ys} → x ∈ ys -> xs ⊆ ys -> (x ∷ xs) ⊆ ys

⊆-suc : ∀ {a} {A : Set a} {y : A} {xs ys : List A} → xs ⊆ ys → xs ⊆ (y ∷ ys)
⊆-suc [] = []
⊆-suc (x₁ ∷ subs) = (S x₁) ∷ (⊆-suc subs)

⊆-refl : ∀ {a} {A : Set a} {xs : List A} → xs ⊆ xs
⊆-refl {xs = []} = []
⊆-refl {xs = x ∷ xs} = Z ∷ (⊆-suc ⊆-refl)


find-∈ : ∀ {a} {A : Set a} {ls : List A} {x : A} → (x ∈ ls) → A
find-∈ {ls = x ∷ xs} Z = x
find-∈ (S px) = find-∈ px

translate-⊆ : ∀ {a} {A : Set a} {ls ks : List A} {x : A} → (ls ⊆ ks) → (x ∈ ls) → (x ∈ ks)
translate-⊆ [] ()
translate-⊆ (x₂ ∷ subs) Z = x₂
translate-⊆ (x₂ ∷ subs) (S px) = translate-⊆ subs px

lookup-parallel : ∀ {a b} {A : Set a} {B : Set b} {x : A} {gss : List A} → x ∈ gss → (refs : List B) → (f : B → A) → map f refs ≡ gss → B
lookup-parallel Z [] f ()
lookup-parallel Z (x ∷ refs) f refl = x
lookup-parallel (S px) [] f ()
lookup-parallel (S px) (x ∷ refs) f refl = lookup-parallel px refs f refl

lookup-parallel-≡ : ∀ {a b} {A : Set a} {B : Set b} {x : A} {gss : List A} → (x₁ : x ∈ gss) → (refs : List B) → (f : B → A) → (eq : map f refs ≡ gss) → x ≡ f (lookup-parallel x₁ refs f eq)
lookup-parallel-≡ Z [] f ()
lookup-parallel-≡ Z (x ∷ refs) f refl = refl
lookup-parallel-≡ (S px) [] f ()
lookup-parallel-≡ (S px) (x ∷ refs) f refl = lookup-parallel-≡ px refs f refl

translate-∈ : ∀ {a b} {A : Set a} {B : Set b} {x : A} {gss : List A} (x₁ : x ∈ gss) → (refs : List B) → (f : B → A) → (eq : map f refs ≡ gss) → lookup-parallel x₁ refs f eq ∈ refs
translate-∈ Z [] f ()
translate-∈ (S px) [] f ()
translate-∈ Z (x ∷ refs) f refl = Z
translate-∈ (S px) (x ∷ refs) f refl = S (translate-∈ px refs f refl)

lookup-all : ∀ {a p} {A : Set a} {P : A → Set p} {ls : List A} {x : A} → x ∈ ls → All P ls → P x
lookup-all Z (px ∷ pxs) = px
lookup-all (S px) (px₁ ∷ pxs) = lookup-all px pxs

All-⊆ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} → xs ⊆ ys → All P ys → All P xs
All-⊆ {xs = []} {ys} subs pys = []
All-⊆ (x₁ ∷ subs) pys = lookup-all x₁ pys ∷ All-⊆ subs pys

⊆-trans : ∀ {a} {A : Set a} {as bs cs : List A} → as ⊆ bs → bs ⊆ cs → as ⊆ cs
⊆-trans [] _ = []
⊆-trans (x₁ ∷ asbs) bscs = (translate-⊆ bscs x₁) ∷ (⊆-trans asbs bscs)
