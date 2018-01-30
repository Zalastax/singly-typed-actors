module Effect where

open import Data.List
open import Data.List.All
open import Data.List.Any
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Category.Monad

open import Membership-≡ hiding (_⊆_; set)

infix 3 _⊆_

data _⊆_ {a}{A : Set a} : List A → List A → Set a where
  []   : ∀ {ys} → [] ⊆ ys
  keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
  skip : ∀ {x xs ys} → xs ⊆ ys → xs ⊆ x ∷ ys

singleton-⊆ : ∀ {a} {A : Set a} {x : A} {xs : List A} → x ∈ xs → [ x ] ⊆ xs
singleton-⊆ (here refl) = keep []
singleton-⊆ (there mem) = skip (singleton-⊆ mem)

Effect : ∀ {l} → Set l → Set (suc l)
Effect {l} S = (A : Set l) (i : S) (o : A → S) → Set l

record EFFECT : Set₁ where
  constructor mkEff
  field S : Set
        E : Effect S

State : List EFFECT → Set₁
State = All EFFECT.S

embed : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys : List A} → All P ys → xs ⊆ ys → All P xs → All P ys
embed pys        []         pxs        = pys
embed (_ ∷ pys)  (keep inc) (px ∷ pxs) = px ∷ embed pys inc pxs
embed (py ∷ pys) (skip inc) pxs        = py ∷ embed pys inc pxs

set : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} {x} → All P xs → x ∈ xs → P x → All P xs
set ps inc px = embed ps (singleton-⊆ inc) (px ∷ [])

extract : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys : List A} → All P ys → xs ⊆ ys → All P xs
extract _          []       = []
extract (p ∷ ps) (keep inc) = p ∷ extract ps inc
extract (_ ∷ ps) (skip inc) = extract ps inc

syntax EffM M E A i (λ x → o) = ⟨ M ⟩Eff E [ x ∶ A ] i ==> o

Evaluator : (Set → Set) → EFFECT → Set₁
Evaluator M Eff = ∀ {A i o} → EFFECT.E Eff A i o → M A

data EffM (M : Set → Set) (Es : List EFFECT) : (A : Set) (i : State Es) (o : A → State Es) → Set₁ where
  return : ∀ {A o} (x : A) → EffM M Es A (o x) o
  _>>=_  : ∀ {A B s₁ s₂ s₃} → EffM M Es A s₁ s₂ → (∀ x → EffM M Es B (s₂ x) s₃) → EffM M Es B s₁ s₃
  effect : ∀ {A E i is} (mem : E ∈ Es) {o} → lookup is mem ≡ i → EFFECT.E E A i o →
             EffM M Es A is (set is mem ∘ o)
  lift : ∀ {Es₁ A i o} (inc : Es₁ ⊆ Es) → EffM M Es₁ A (extract i inc) o →
             EffM M Es A i (embed i inc ∘ o)
  new : ∀ {E A is os i}{o : A → EFFECT.S E} →
          Evaluator M E →
          ⟨ M ⟩Eff (E ∷ Es) [ x ∶ A ] i ∷ is ==> (o x ∷ os x) →
          EffM M Es A is os

_<$>_ : ∀ {M E i A B o} → (A → B) → ⟨ M ⟩Eff E [ _ ∶ A ] i ==> o → ⟨ M ⟩Eff E [ _ ∶ B ] i ==> o
f <$> m = m >>= λ x → return (f x)

_<$_ : ∀ {M E i A B o} → B → ⟨ M ⟩Eff E [ _ ∶ A ] i ==> o → ⟨ M ⟩Eff E [ _ ∶ B ] i ==> o
x <$ m = (λ _ → x) <$> m

module _ {M : Set → Set} (Mon : RawMonad M) where
  module M = RawMonad Mon

  run : ∀ {Es A i o} → All (Evaluator M) Es → EffM M Es A i o → M A
  run env (return x) = M.return x
  run env (m >>= f) = run env m M.>>= λ x → run env (f x)
  run env (effect mem _ e) = lookup env mem e
  run env (lift inc m) = run (extract env inc) m
  run env (new eval m) = run (eval ∷ env) m
