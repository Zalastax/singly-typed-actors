module Effect where

open import Data.List
open import Data.List.All
open import Data.List.Any
open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Function
open import Category.Monad
open import Data.Product
open import EffectUtil
open import Membership-equality hiding (_⊆_; set)

Effect : ∀ f → Set (suc f)
Effect f = (result : Set f) (i : Set f) (o : result → Set f) → Set f

record EFFECT (f : Level) : Set (suc f) where
  constructor mkEff
  field S : Set f
        E : Effect f

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

pure : ∀ {l m A es} → A → EffM {l} m A es (λ v → es)
pure = return

_<*>_ : ∀ {l m A B es} → EffM {l} m (A → B) es (λ v → es) →
                    EffM {l} m A es (λ v → es) →
                    EffM {l} m B es (λ v → es)
_<*>_ prog v = prog >>= λ fn →
               v >>= λ arg →
               pure (fn arg)

_<$>_ : ∀ {l m A B es} → (f : A → B) → EffM {l} m A es (λ v → es) → EffM {l} m B es (λ v → es)
_<$>_ f m = pure f <*> m

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
    cont v res = k v ((handle , res) ∷ env)
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

