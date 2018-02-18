module Examples.PingPong where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [])
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc)
open import Coinduction
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; InList ; SubNil)
open import Data.Unit using (⊤ ; tt)

open InboxShape

-- An example including three actors: spawner, pinger, ponger
--
-- Spawner is the actor that starts it all.
-- Spawner spawns both pinger and ponger.
-- Then spawner send the reference of ponger to pinger,
-- and the reference of pinger to ponger.
--
-- Pinger is an actor that can receive Bool messages.
-- Pinger counts the number of 'false' messages it receives, until it receives a 'true'
--
-- Ponger is an actor that can receive Nat messages.
-- Ponger keeps sending 'false' until it receives a message containing 10.

Spawnbox : InboxShape
Spawnbox = record { value-types = [] ; reference-types = [] }


mutual
  Pingbox : InboxShape
  Pingbox .value-types = Bool ∷ []
  Pingbox .reference-types = Pongbox ∷ []

  Pongbox : InboxShape
  Pongbox .value-types = ℕ ∷ []
  Pongbox .reference-types = Pingbox ∷ []

pingrefs : ReferenceTypes
pingrefs = Pongbox ∷ []

constPingrefs : {A : Set₁} → (A → ReferenceTypes)
constPingrefs _ =  pingrefs

pingMainActor : (A : Set₁) → Set₂
pingMainActor A = ActorM Pingbox A pingrefs constPingrefs

mutual
  pingReceive : (msg : Message Pingbox) → ∞ (ActorM Pingbox (Lift Bool) (add-if-reference pingrefs msg) constPingrefs)
  pingReceive (Value Z b) = return b
  pingReceive (Value (S ()) _)
  pingReceive (Reference _) = ♯ ALift (InList (S Z) SubNil) loopTillPingValue

  loopTillPingValue : ∞ (pingMainActor (Lift Bool))
  loopTillPingValue = ♯ (receive >>= pingReceive)

pinger : ActorM Pingbox ⊤₁ [] constPingrefs
pinger = loopTillPong >>= (λ _ → pingMain 0)
  where
    loopTillPong : ∞ (ActorM Pingbox ⊤₁ [] constPingrefs)
    loopTillPong = ♯ (receive >>= ((λ
      { (Value _ _) → loopTillPong
      ; (Reference Z) → return _
      ; (Reference (S ())) })))
    pingMain : ℕ → ∞ (pingMainActor ⊤₁)
    pingMain n = ♯ ((loopTillPingValue >>= λ
      { (lift false) → ♯ ( (Z !v Value Z n) >>= λ _ → pingMain (suc n))
      ; (lift true) → return _}))

pongrefs : ReferenceTypes
pongrefs = Pingbox ∷ []

constPongrefs : {A : Set₁} → (A → ReferenceTypes)
constPongrefs _ = pongrefs

pongMainActor : (A : Set₁) → Set₂
pongMainActor A = ActorM Pongbox A pongrefs constPongrefs

mutual
  pongReceive : (msg : Message Pongbox) → ∞ (ActorM Pongbox (Lift ℕ) (add-if-reference pongrefs msg) constPongrefs)
  pongReceive (Value Z n) = return n
  pongReceive (Value (S ()) _)
  pongReceive (Reference _) = ♯ ALift (InList (S Z) SubNil) loopTillPongValue
  loopTillPongValue : ∞ (pongMainActor (Lift ℕ))
  loopTillPongValue = ♯ (receive >>= pongReceive)

ponger : ActorM Pongbox ⊤₁ [] constPongrefs
ponger = loopTillPing >>= λ _ → ♯ ((Z !v Value Z false) >>= λ _ → pongMain)
  where
    loopTillPing : ∞ (ActorM Pongbox ⊤₁ [] constPongrefs)
    loopTillPing = ♯ (receive >>= λ
      { (Value _ _) → loopTillPing
      ; (Reference Z) → return _
      ; (Reference (S ()))})
    pongMain : ∞ (pongMainActor ⊤₁)
    pongMain = ♯ (loopTillPongValue >>= λ
      { (lift 10) → ♯ (Z !v Value Z true >>= λ _ → return _)
        ; (lift n) → ♯ (Z !v Value Z false >>= λ _ → pongMain)})

spawner : ActorM Spawnbox ⊤₁ [] (λ _ → Pingbox ∷ Pongbox ∷ [])
spawner = spawn ponger >>= λ _ →
          ♯ (spawn pinger >>= λ _ →
          ♯ (to Z !r Reference Z via S Z >>= λ _ →
          to S Z !r Reference Z via Z))

