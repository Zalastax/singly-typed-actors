module Membership where
-- open import Data.List.Any.Membership.Propositional public

open import Data.List
open import Data.List.Any using ()
open import Data.List.All using (All ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)


data _∈_ {a} {A : Set a} : A → (List A) -> Set a where
  Z : ∀ {x xs} → x ∈ (x ∷ xs)
  S : ∀ {x y xs} → x ∈ xs -> x ∈ (y ∷ xs)

data _⊆_ {a} {A : Set a} : List A -> List A -> Set a where
  SubNil : ∀ {xs} → [] ⊆ xs
  InList : ∀ {x xs ys} → x ∈ ys -> xs ⊆ ys -> (x ∷ xs) ⊆ ys

lookup-∈ : ∀ {a} {A : Set a} {ls : List A} {x : A} → (x ∈ ls) → A
lookup-∈ {ls = x ∷ xs} Z = x
lookup-∈ (S px) = lookup-∈ px

translate-⊆ : ∀ {a} {A : Set a} {ls ks : List A} {x : A} → (ls ⊆ ks) → (x ∈ ls) → (x ∈ ks)
translate-⊆ SubNil ()
translate-⊆ (InList x₂ subs) Z = x₂
translate-⊆ (InList x₂ subs) (S px) = translate-⊆ subs px


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

All-⊆ : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys} → xs ⊆ ys → All P ys → All P xs
All-⊆ {xs = []} {ys} subs pys = []
All-⊆ {xs = x ∷ xs} {ys} (InList x₁ subs) pys = {!!}
