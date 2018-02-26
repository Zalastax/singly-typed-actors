module Simulate where

open import Sublist using (_⊆_ ; [] ; keep ; skip ; All-⊆)
open import ActorMonad public
open import SimulationEnvironment
open import EnvironmentOperations
open import SimulationSteps

open import Data.Colist using (Colist ; [] ; _∷_)
open import Data.List using (List ; _∷_ ; [] ; map)
open import Data.List.All using (All ; _∷_ ; [] ; lookup) renaming (map to ∀map)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_ ; s≤s)
open import Data.Nat.Properties using (≤-reflexive ; ≤-step)
open import Data.Unit using (⊤ ; tt)
open import Data.Maybe using (Maybe ; just ; nothing ; monad)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; trans)

open import Level using (Lift ; lift) renaming (suc to lsuc ; zero to lzero)
open import Coinduction using (∞ ; ♯_ ; ♭)

data ReceiveKind : Set where
  Nothing : ReceiveKind
  Value : ReceiveKind
  Reference : Name → ReceiveKind
  Dropped : ReceiveKind

data Trace : Set where
  Return : Name → Trace
  Bind : Trace → Trace
  BindDouble : Name → Trace -- If we encounter a bind and then a bind again...
  Spawn : (spawner : Name) → (spawned : Name) → Trace
  SendValue : (sender : Name) → (receiver : Name) → Trace
  SendReference : (sender : Name) → (receiver : Name) → (reference : Name) → Trace
  Receive : Name → ReceiveKind → Trace
  TLift : Name → Trace
  Self : Name → Trace

-- A step in the simulation is the next environment paired up with what step was taken
record EnvStep : Set₂ where
  field
    env : Env
    trace : Trace

Trampoline = Maybe EnvStep

trace : Maybe Env → Trace → Trampoline
trace (just env) t = just (record { env = env ; trace = t })
trace nothing t = nothing

open Actor
open ValidActor
open Env
open FoundReference
open LiftedReferences
open UpdatedInboxes
open ValidMessageList
open NamedInbox

simulate : Env → Trampoline
simulate env@(record { acts = [] }) = nothing
simulate env@(record { acts = (record { actor-m = Value val ; name = name } ∷ rest) }) = trace (just (simulate-value env _)) (Return name)
simulate env@(record { acts = (record { actor-m = (m >>= f) } ∷ rest) }) = {!!}
simulate env@(record { acts = (record { actor-m = Spawn actor-m₁ } ∷ rest) }) = {!!}
simulate env@(record { acts = (record { actor-m = SendValue canSendTo msg } ∷ rest) }) = {!!}
simulate env@(record { acts = (record { actor-m = SendReference canSendTo canForward msg } ∷ rest) }) = {!!}
simulate env@(record { acts = (record { actor-m = Receive } ∷ rest) }) = {!!}
simulate env@(record { acts = (record { actor-m = ALift inc x } ∷ rest) }) = {!!}
simulate env@(record { acts = (record { actor-m = Self } ∷ rest) }) = {!!}



