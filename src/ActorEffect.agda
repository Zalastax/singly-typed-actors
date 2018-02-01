module ActorEffect where

open import Effect
import IO.Primitive as IO
open import Data.String using (String)
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Unit using (⊤ ; tt)
open import Category.Monad using (RawMonad)
open import Level using (zero)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.All using (All ; lookup ; _∷_ ; [])
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership-≡ using (_∈_)
open import Data.Product using (Σ ; _,_ ; _×_)
open import Data.Nat using (ℕ ; zero ; suc)

Name = ℕ
InboxType = Set

data ActorM (IT : InboxType) : (A : Set) →
              (es : List InboxType) →
              (ce : A → List InboxType) →
              Set₁ where
  Value : ∀ {A ce} → (val : A) → ActorM IT A (ce val) ce
  ABind : ∀ {A B es ce₁ ce₂} → ActorM IT A es ce₁ →
          (∀ x → ActorM IT B (ce₁ x) (ce₂)) →
          ActorM IT B es ce₂
  Spawn : {NewIT : InboxType} → {A : Set} → ∀ {es ceN} →
          ActorM NewIT A [] ceN →
          ActorM IT ⊤ es λ _ → NewIT ∷ es
  Send : ∀ {es} → {ToIT : InboxType} →
    (prf : ToIT ∈ es) →
    (v : ToIT) →
    ActorM IT ⊤ es (λ _ → es)

