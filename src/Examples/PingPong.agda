module Examples.PingPong where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [])
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc)
open import Coinduction
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Sublist using ([] ; keep ; skip ; reflexive-⊆)
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
Spawnbox = record { Values = [] ; References = [] }


mutual
  Pingbox : InboxShape
  Pingbox .Values = Bool ∷ []
  Pingbox .References = Pongbox ∷ []

  Pongbox : InboxShape
  Pongbox .Values = ℕ ∷ []
  Pongbox .References = Pingbox ∷ []

pingrefs : List InboxShape
pingrefs = Pongbox ∷ []

constPingrefs : {A : Set₁} → (A → List InboxShape)
constPingrefs _ =  pingrefs

pingMainActor : (A : Set₁) → Set₂
pingMainActor A = ActorM Pingbox A pingrefs constPingrefs

mutual
  pingReceive : (msg : Message Pingbox) → ∞ (ActorM Pingbox (Lift Bool) (addIfRef pingrefs msg) constPingrefs)
  pingReceive (Value (here refl) b) = return b
  pingReceive (Value (there ()) _)
  pingReceive (Reference _) = ♯ ALift (skip reflexive-⊆) loopTillPingValue

  loopTillPingValue : ∞ (pingMainActor (Lift Bool))
  loopTillPingValue = ♯ (receive >>= pingReceive)

pinger : ActorM Pingbox ⊤₁ [] constPingrefs
pinger = loopTillPong >>= (λ _ → pingMain 0)
  where
    loopTillPong : ∞ (ActorM Pingbox ⊤₁ [] constPingrefs)
    loopTillPong = ♯ (receive >>= ((λ
      { (Value _ _) → loopTillPong
      ; (Reference (here refl)) → return _
      ; (Reference (there ())) })))
    pingMain : ℕ → ∞ (pingMainActor ⊤₁)
    pingMain n = ♯ ((loopTillPingValue >>= λ
      { (lift false) → ♯ ( (here refl !v Value (here refl) n) >>= λ _ → pingMain (suc n))
      ; (lift true) → return _}))

pongrefs : List InboxShape
pongrefs = Pingbox ∷ []

constPongrefs : {A : Set₁} → (A → List InboxShape)
constPongrefs _ = pongrefs

pongMainActor : (A : Set₁) → Set₂
pongMainActor A = ActorM Pongbox A pongrefs constPongrefs

mutual
  pongReceive : (msg : Message Pongbox) → ∞ (ActorM Pongbox (Lift ℕ) (addIfRef pongrefs msg) constPongrefs)
  pongReceive (Value (here refl) n) = return n
  pongReceive (Value (there ()) _)
  pongReceive (Reference _) = ♯ ALift (skip reflexive-⊆) loopTillPongValue

  loopTillPongValue : ∞ (pongMainActor (Lift ℕ))
  loopTillPongValue = ♯ (receive >>= pongReceive)

ponger : ActorM Pongbox ⊤₁ [] constPongrefs
ponger = loopTillPing >>= λ _ → ♯ ((here refl !v Value (here refl) false) >>= λ _ → pongMain)
  where
    loopTillPing : ∞ (ActorM Pongbox ⊤₁ [] constPongrefs)
    loopTillPing = ♯ (receive >>= λ
      { (Value _ _) → loopTillPing
      ; (Reference (here refl)) → return _
      ; (Reference (there ()))})
    pongMain : ∞ (pongMainActor ⊤₁)
    pongMain = ♯ (loopTillPongValue >>= λ
      { (lift 10) → ♯ (here refl !v Value (here refl) true >>= λ _ → return _)
        ; (lift n) → ♯ (here refl !v Value (here refl) false >>= λ _ → pongMain)})

spawner : ActorM Spawnbox ⊤₁ [] (λ _ → Pingbox ∷ Pongbox ∷ [])
spawner = spawn ponger >>= λ _ →
          ♯ (spawn pinger >>= λ _ →
          ♯ (to here refl !r Reference (here refl) via there (here refl) >>= λ _ →
          to there (here refl) !r Reference (here refl) via here refl))

