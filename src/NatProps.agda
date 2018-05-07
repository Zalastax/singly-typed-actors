module NatProps where
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; zero ; suc ; s≤s)
open import Data.Nat.Properties using (s≤s-injective)
open import Relation.Nullary using (Dec ; yes ; no ; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym)
open import Data.Empty using (⊥)

<-¬≡ : ∀ {n m} → n < m → ¬ n ≡ m
<-¬≡ {zero} {zero} ()
<-¬≡ {zero} {suc m} p = λ ()
<-¬≡ {suc n} {zero} p = λ ()
<-¬≡ {suc n} {suc m} (Data.Nat.s≤s p) with (<-¬≡ p)
... | q = λ { refl → q refl }
