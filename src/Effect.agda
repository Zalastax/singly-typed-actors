module Effect where

open import Data.List
open import Data.List.All
open import Data.List.Any
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Category.Monad
open import Data.Product

open import Membership-≡ hiding (_⊆_; set)

infix 3 _⊆_

-- Sublist without re-ordering, to be improves later...
data _⊆_ {a}{A : Set a} : List A → List A → Set a where
  []   : ∀ {ys} → [] ⊆ ys
  keep : ∀ {x xs ys} → xs ⊆ ys → x ∷ xs ⊆ x ∷ ys
  skip : ∀ {x xs ys} → xs ⊆ ys → xs ⊆ x ∷ ys

singleton-⊆ : ∀ {a} {A : Set a} {x : A} {xs : List A} → x ∈ xs → [ x ] ⊆ xs
singleton-⊆ (here refl) = keep []
singleton-⊆ (there mem) = skip (singleton-⊆ mem)

Effect : ∀ f → Set (suc f)
Effect f = (result : Set f) (i : Set f) (o : result → Set f) → Set f

record EFFECT (f : Level) : Set (suc f) where
  constructor mkEff
  field S : Set f
        E : Effect f

-- State : List EFFECT → Set₁
-- State = All EFFECT.S

embed : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys : List A} → All P ys → xs ⊆ ys → All P xs → All P ys
embed pys        []         pxs        = pys
embed (_ ∷ pys)  (keep inc) (px ∷ pxs) = px ∷ embed pys inc pxs
embed (py ∷ pys) (skip inc) pxs        = py ∷ embed pys inc pxs

set : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} {x} → All P xs → x ∈ xs → P x → All P xs
set ps inc px = embed ps (singleton-⊆ inc) (px ∷ [])

updateResTy : ∀ {f A E i o} → (val : A) →
              (es : List (EFFECT f)) →
              (prf : (mkEff i E) ∈ es) →
              (eff : E A i o) →
              List (EFFECT f)
updateResTy {o = o} val (mkEff i e ∷ es) (here px) eff = mkEff (o val) e ∷ es
updateResTy val (e ∷ es) (there prf) eff = e ∷ updateResTy val es prf eff

updateWith : ∀ {f ys} (ys' : List (EFFECT f)) → (xs : List (EFFECT f)) →
             (ys ⊆ xs) → List (EFFECT f)
updateWith [] xs inc = xs
updateWith (y' ∷ ys') xs [] = xs
updateWith (y' ∷ ys') (_ ∷ xs) (keep inc) = y' ∷ updateWith ys' xs inc
updateWith (y' ∷ ys') (x ∷ xs) (skip inc) = x ∷ updateWith (y' ∷ ys') xs inc

extract : ∀ {a p} {A : Set a} {P : A → Set p} {xs ys : List A} → All P ys → xs ⊆ ys → All P xs
extract _          []       = []
extract (p ∷ ps) (keep inc) = p ∷ extract ps inc
extract (_ ∷ ps) (skip inc) = extract ps inc

-- syntax EffM M E A i (λ x → o) = ⟨ M ⟩Eff[ x ∶ A ] i ==> o

Handler : ∀ {f} → (Set f → Set f) → Effect f → Set (suc f)
Handler M e = ∀ {A a o res} → (r : res) → (eff : e A res o) →
              (k : ((x : A) → o x → M a)) → M a

-- @ A  The return type of the result
-- @ es The list of allowed side-effects
-- @ ce The function to compute a new list of allowed side-effects
data EffM {f : Level} (m : Set f → Set f) : (A : Set f) →
             (es : List (EFFECT f)) →
             (ce : A → List (EFFECT f)) → Set (suc f) where
  return : ∀ {A ce} (val : A) → EffM m A (ce val) ce
  _>>=_  : ∀ {A B es ce₁ ce₂} → EffM m A es ce₁ → (∀ x → EffM m B (ce₁ x) ce₂) → EffM m B es ce₂
  effect : ∀ {A E i es o} (prf : (mkEff i E) ∈ es) →
             (eff : E A i o) →
             EffM m A es (λ v → updateResTy v es prf eff)
  -- use to invoke sub-programs that use some or all of the available effects
  lift   : ∀ {A ys ys' xs} → (inc : ys ⊆ xs) →
           EffM m A ys ys' →
           EffM m A xs (λ v → updateWith (ys' v) xs inc)
  new : ∀ {A es} →
    (e : EFFECT f) →
    (val : EFFECT.S e) →
    Handler m (EFFECT.E e) →
    EffM {f} m A (e ∷ es) (λ v → e ∷ es) →
    EffM m A es (λ v → es)

-- _<$>_ : ∀ {M E i A B o} → (A → B) → ⟨ M ⟩Eff E [ _ ∶ A ] i ==> o → ⟨ M ⟩Eff E [ _ ∶ B ] i ==> o
-- f <$> m = m >>= λ x → return (f x)

-- _<$_ : ∀ {M E i A B o} → B → ⟨ M ⟩Eff E [ _ ∶ A ] i ==> o → ⟨ M ⟩Eff E [ _ ∶ B ] i ==> o
-- x <$ m = (λ _ → x) <$> m

-- postulate eta-contraction : {A : Set} → {f : A → Set} → {v : A} → (B : f v) → Set

data Env {f : Level} : (m : Set f → Set f) → List (EFFECT f) → Set (suc f) where
  [] : ∀ {m} → Env m []
  _∷_ : ∀ {m eff es a} → (el : Handler m eff × a) → Env m es → Env m (mkEff a eff ∷ es)

execEff : ∀ {f m A es E i} {o : A → Set f} {B} →
  Env {f} m es →
  (prf : (mkEff i E) ∈ es) →
  (eff : E A i o) →
  ((v : A) → Env {f} m (updateResTy v es prf eff) → m B) → m B
execEff {m = m} {A = A} {o = o} {B = B} ((handle , val) ∷ env) (here refl) eff k = handle val eff cont
  where
    cont : (v : A) → o v → m B
    cont v res = k v ((handle , res) ∷ env) -- TODO: Make res eta-contract
execEff (e ∷ env) (there prf) eff k = execEff env prf eff λ v → λ env' → k v (e ∷ env')

dropEnv : ∀ {f m ys xs} → Env {f} m ys → xs ⊆ ys → Env m xs
dropEnv [] [] = []
dropEnv (el ∷ env) [] = []
dropEnv (el ∷ env) (keep sub) = el ∷ (dropEnv env sub)
dropEnv (el ∷ env) (skip sub) = dropEnv env sub

rebuildEnv : ∀ {f m ys' ys xs} → Env {f} m ys' → (prf : ys ⊆ xs) →
             Env m xs → Env m (updateWith ys' xs prf)
rebuildEnv [] [] env = env
rebuildEnv (_ ∷ _) [] env = env
rebuildEnv [] (keep prf) env = env
rebuildEnv (el ∷ els) (keep prf) (_ ∷ env) = el ∷ rebuildEnv els prf env
rebuildEnv [] (skip prf) env = env
rebuildEnv (el ∷ els) (skip prf) (en ∷ env) = en ∷ rebuildEnv (el ∷ els) prf env

eff : ∀ {f m es A B ce} → Env {f} m es → EffM m A es ce → ((v : A) → Env m (ce v) → m B) → m B
eff env (return val) k = k val env
eff env (effM >>= c) k = eff env effM λ p' → λ env' → eff env' ((c p')) k
eff env (effect prf effP) k = execEff env prf effP k
eff env (lift inc effM) k = eff env' effM λ p' → λ envk → k p' (rebuildEnv envk inc env)
  where
    env' = dropEnv env inc
eff {f} {m} {es} {A} {B} env (new e val handler effM) k = eff ((handler , val) ∷ env) effM cont
  where
    cont : (v : A) → Env {f} m (e ∷ es) → m B
    cont v (val ∷ envk) = k v envk

run : ∀ {f a xs xs'} → ∀ m → (mon : RawMonad m) → (prog : EffM {f} m a xs xs') → Env m xs → m a
run m mon prog env = eff env prog λ r → λ env' → RawMonad.return mon r

-- module _ {M : Set → Set} (Mon : RawMonad M) where
--   module M = RawMonad Mon

--  runEnv : ∀ {A xs'} → {m : ∀ {f} → (Set f → Set f)} → ∀ {xs} → Env {zero} (m {zero}) xs → EffM (m {zero}) A xs xs' →
--           m {suc zero} (Σ A λ a → Env m (xs' a))
--  runEnv env prog = eff env prog ? -- {!env!} {!prog!} {!!}
   -- eff = ?
  -- run : ∀ {Es A i o} → All (Handler M) Es → EffM M A i o → M A
  -- run env (return x) = M.return x
  -- run env (m >>= f) = run env m M.>>= λ x → run env (f x)
  -- run env (effect prf eff) = execEff env prf eff
  -- run env (lift inc m) = run (extract env inc) m
  -- run env (new eval m) = run (eval ∷ env) m

