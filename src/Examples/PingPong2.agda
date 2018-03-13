module Examples.PingPong2 where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [])
open import Data.List.All using (All ; _∷_ ; [])
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc)
open import Coinduction
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; _∷_ ; [] ; ⊆-refl)
open import Data.Unit using (⊤ ; tt)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)

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
Spawnbox = []

mutual
  PingValues = Bool ∷ []
  PongValues = ℕ ∷ []

  PingRefs : ReferenceTypes
  PingRefs = (⊠-of-values PongValues) ∷ []
  PongRefs : ReferenceTypes
  PongRefs = ⊠-of-values PingValues ∷ []

  Pingbox : InboxShape
  Pingbox = (ValueType Bool ∷ []) ∷ (ReferenceType (⊠-of-values PongValues) ∷ []) ∷ []

  Pongbox : InboxShape
  Pongbox = (ValueType ℕ ∷ []) ∷ (ReferenceType (⊠-of-values PingValues) ∷ []) ∷ []


constPingrefs : {A : Set₁} → (A → ReferenceTypes)
constPingrefs _ =  PingRefs

pingMainActor : (A : Set₁) → Set₂
pingMainActor A = ActorM Pingbox A PingRefs constPingrefs

mutual
  pingReceive : (msg : Message Pingbox) → ∞ (ActorM Pingbox (Lift Bool) (add-references PingRefs msg) constPingrefs)
  pingReceive (Msg Z (b ∷ [])) = return b
  pingReceive (Msg (S Z) _) = ♯ ALift (S Z ∷ []) loopTillPingValue
  pingReceive (Msg (S (S ())) x₁)

  loopTillPingValue : ∞ (pingMainActor (Lift Bool))
  loopTillPingValue = ♯ (receive >>= pingReceive)

pinger : ActorM Pingbox ⊤₁ [] constPingrefs
pinger = loopTillPong >>= (λ _ → pingMain 0)
  where
    loopTillPong : ∞ (ActorM Pingbox ⊤₁ [] constPingrefs)
    loopTillPong = ♯ (receive >>= ((λ
      { (Msg Z x₁) → loopTillPong
      ; (Msg (S Z) x₁) → return _
      ; (Msg (S (S ())) x₁)
      })))
    pingMain : ℕ → ∞ (pingMainActor ⊤₁)
    pingMain n = ♯ ((loopTillPingValue >>= λ
      { (lift false) → ♯ ( (Z ![t: Z ] (lift n ∷ [])) >>= λ _ → pingMain (suc n))
      ; (lift true) → return _}))

constPongrefs : {A : Set₁} → (A → ReferenceTypes)
constPongrefs _ = PongRefs

pongMainActor : (A : Set₁) → Set₂
pongMainActor A = ActorM Pongbox A PongRefs constPongrefs

mutual
  pongReceive : (msg : Message Pongbox) → ∞ (ActorM Pongbox (Lift ℕ) (add-references PongRefs msg) constPongrefs)
  pongReceive (Msg Z (n ∷ [])) = return n
  pongReceive (Msg (S Z) _) = ♯ ALift (S Z ∷ []) loopTillPongValue
  pongReceive (Msg (S (S ())) _)
  loopTillPongValue : ∞ (pongMainActor (Lift ℕ))
  loopTillPongValue = ♯ (receive >>= pongReceive)

ponger : ActorM Pongbox ⊤₁ [] constPongrefs
ponger = loopTillPing >>= λ _ → ♯ ((Z ![t: Z ] ((lift false) ∷ [])) >>= λ _ → pongMain)
  where
    loopTillPing : ∞ (ActorM Pongbox ⊤₁ [] constPongrefs)
    loopTillPing = ♯ (♯ SelectiveReceive (λ {
      (Msg Z x₁) → false
      ; (Msg (S Z) _) → true
      ; (Msg (S (S ())) _)}) >>= λ {
        record { msg = (Msg Z _) ; msg-ok = () }
      ; record { msg = (Msg (S Z) _) ; msg-ok = msg-ok } → return₁ _
      ; record { msg = (Msg (S (S ())) x₁) }})
    pongMain : ∞ (pongMainActor ⊤₁)
    pongMain = ♯ (loopTillPongValue >>= λ
      { (lift 10) → ♯ (Z ![t: Z ] ((lift true) ∷ []) >>= λ _ → return _)
        ; (lift n) → ♯ (Z ![t: Z ] ((lift false) ∷ []) >>= λ _ → pongMain)})

-- TODO: this needs to look prettier
spawner : ActorM Spawnbox ⊤₁ [] (λ _ → Pingbox ∷ Pongbox ∷ [])
spawner = spawn ponger >>= λ _ →
        ♯ (spawn pinger >>= λ _ → ♯ ((Z ![t: S Z ](([ S Z ]>: (Z ∷ [])) ∷ [])) >>= λ _ →
          S Z ![t: S Z ] (([ Z ]>: (Z ∷ [])) ∷ [])))
