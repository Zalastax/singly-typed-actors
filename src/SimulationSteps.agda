module SimulationSteps where
open import ActorMonad
open import SimulationEnvironment
open import EnvironmentOperations

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.List using (List ; _∷_ ; [])
open import Data.Unit using (⊤ ; tt)

open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Coinduction using (∞ ; ♯_ ; ♭)

is-actor-value : ∀ {IS A pre post} → ActorM IS A pre post → Set
is-actor-value (Value val) = ⊤
is-actor-value _ = ⊥

is-actor-bind : ∀ {IS A pre post} → ActorM IS A pre post → Set
is-actor-bind (_ >>= _) = ⊤
is-actor-bind _ = ⊥

is-actor-bind-of : (∀ {IS' A' pre' post'} → ActorM IS' A' pre' post' → Set) → ∀ {IS A pre post} → ActorM IS A pre post → Set
is-actor-bind-of f (m >>= _) = f (♭ m)
is-actor-bind-of _ _ = ⊥

is-env-top : (∀ {IS A pre post} → ActorM IS A pre post → Set) → Env → Set
is-env-top f record { acts = actor@(_) ∷ _ } = f (Actor.actor-m actor)
is-env-top _ _ = ⊥


is-env-value = is-env-top is-actor-value
is-env-bind = is-env-top is-actor-bind

is-env-bind-value = is-env-top (is-actor-bind-of is-actor-value)

simulate-value : (env : Env) → is-env-value env → Env
simulate-value env@(record { acts = (record { actor-m = Value v }) ∷ _}) tt = drop-top-actor env
simulate-value record { acts = [] } ()
simulate-value record { acts = (record { actor-m = (_ >>= _)} ∷ _)} ()
simulate-value record { acts = (record { actor-m = Spawn _ } ∷ _)} ()
simulate-value record { acts = (record { actor-m = SendValue _ _ } ∷ _)} ()
simulate-value record { acts = (record { actor-m = SendReference _ _ _ } ∷ _)} ()
simulate-value record { acts = (record { actor-m = Receive } ∷ _)} ()
simulate-value record { acts = (record { actor-m = ALift _ _ } ∷ _)} ()
simulate-value record { acts = (record { actor-m = Self } ∷ _)} ()

simulate-value-no-comm : (env : Env) → (p : is-env-value env) → no-comm env (simulate-value env p)
simulate-value-no-comm env@(record { acts = (record { actor-m = Value v }) ∷ _ ; env-inboxes = env-inboxes }) tt = drop-top-actor-no-comm env
simulate-value-no-comm record { acts = [] } ()
simulate-value-no-comm record { acts = (record { actor-m = (_ >>= _)} ∷ _)} ()
simulate-value-no-comm record { acts = (record { actor-m = Spawn _ } ∷ _)} ()
simulate-value-no-comm record { acts = (record { actor-m = SendValue _ _ } ∷ _)} ()
simulate-value-no-comm record { acts = (record { actor-m = SendReference _ _ _ } ∷ _)} ()
simulate-value-no-comm record { acts = (record { actor-m = Receive } ∷ _)} ()
simulate-value-no-comm record { acts = (record { actor-m = ALift _ _ } ∷ _)} ()
simulate-value-no-comm record { acts = (record { actor-m = Self } ∷ _)} ()

simulate-bind-value : (env : Env) → is-env-bind-value env → Env
simulate-bind-value record { acts = [] } ()
simulate-bind-value record { acts = (record { actor-m = Value _ } ∷ _)} ()
simulate-bind-value record { acts = (record { actor-m = (m >>= _)} ∷ _)} p with (♭ m)
... | (Value v) = {!!}
... | (_ >>= _) = ⊥-elim p
... | (Spawn _) = ⊥-elim p
... | (SendValue _ _) = ⊥-elim p
... | (SendReference _ _ _) = ⊥-elim p
... | Receive = ⊥-elim p
... | (ALift _ _) = ⊥-elim p
... | Self = ⊥-elim p

simulate-bind-value record { acts = (record { actor-m = Spawn _ } ∷ _)} ()
simulate-bind-value record { acts = (record { actor-m = SendValue _ _ } ∷ _)} ()
simulate-bind-value record { acts = (record { actor-m = SendReference _ _ _ } ∷ _)} ()
simulate-bind-value record { acts = (record { actor-m = Receive } ∷ _)} ()
simulate-bind-value record { acts = (record { actor-m = ALift _ _ } ∷ _)} ()
simulate-bind-value record { acts = (record { actor-m = Self } ∷ _)} ()


simulate-bind : (env : Env) → is-env-bind env → Env
simulate-bind record { acts = [] } ()
simulate-bind record { acts = (record { actor-m = Value _ } ∷ _)} ()
simulate-bind record { acts = (record { actor-m = (m >>= f)} ∷ _)} tt with (♭ m)
... | bm = {!!}
simulate-bind record { acts = (record { actor-m = Spawn _ } ∷ _)} ()
simulate-bind record { acts = (record { actor-m = SendValue _ _ } ∷ _)} ()
simulate-bind record { acts = (record { actor-m = SendReference _ _ _ } ∷ _)} ()
simulate-bind record { acts = (record { actor-m = Receive } ∷ _)} ()
simulate-bind record { acts = (record { actor-m = ALift _ _ } ∷ _)} ()
simulate-bind record { acts = (record { actor-m = Self } ∷ _)} ()

