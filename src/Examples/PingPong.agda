module Examples.PingPong where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [])
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc)
open import Coinduction
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; _∷_ ; [] ; ⊆-refl)
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
  PingValues = Bool ∷ []
  PongValues = ℕ ∷ []

  PingRefs = ⊠-of-values PongValues ∷ []
  PongRefs = ⊠-of-values PingValues ∷ []

  Pingbox : InboxShape
  Pingbox = ⊠[V: PingValues ][R: PingRefs ]

  Pongbox : InboxShape
  Pongbox = ⊠[V: PongValues ][R: PongRefs ]


constPingrefs : {A : Set₁} → (A → ReferenceTypes)
constPingrefs _ =  PingRefs

pingMainActor : (A : Set₁) → Set₂
pingMainActor A = ActorM Pingbox A PingRefs constPingrefs

mutual
  pingReceive : (msg : Message Pingbox) → ∞ (ActorM Pingbox (Lift Bool) (add-if-reference PingRefs msg) constPingrefs)
  pingReceive (Value Z b) = return b
  pingReceive (Value (S ()) _)
  pingReceive (Reference _) = ♯ ALift ((S Z) ∷ []) loopTillPingValue

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

constPongrefs : {A : Set₁} → (A → ReferenceTypes)
constPongrefs _ = PongRefs

pongMainActor : (A : Set₁) → Set₂
pongMainActor A = ActorM Pongbox A PongRefs constPongrefs

mutual
  pongReceive : (msg : Message Pongbox) → ∞ (ActorM Pongbox (Lift ℕ) (add-if-reference PongRefs msg) constPongrefs)
  pongReceive (Value Z n) = return n
  pongReceive (Value (S ()) _)
  pongReceive (Reference _) = ♯ ALift ((S Z) ∷ []) loopTillPongValue
  loopTillPongValue : ∞ (pongMainActor (Lift ℕ))
  loopTillPongValue = ♯ (receive >>= pongReceive) -- ♯ (receive >>= pongReceive)

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
          ♯ (to Z !r Reference (record { wanted-is-reference = Z ; fw-handles-wanted =  record { values-sub = ⊆-refl ; references-sub = [] } }) via S Z >>= λ _ →
          to S Z !r Reference (record { wanted-is-reference = Z ; fw-handles-wanted = record { values-sub = ⊆-refl ; references-sub = [] } }) via Z))
  where
    open _<:_


