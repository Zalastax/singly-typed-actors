module Examples.PingPong where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [])
open import Data.List.All using (All ; _∷_ ; [])
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc)
open import Size
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; _∷_ ; [] ; ⊆-refl)
open import Data.Unit using (⊤ ; tt)

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


constPingrefs : {A : Set₁} → (A → TypingContext)
constPingrefs _ =  PingRefs

pingMainActor : (i : Size) (A : Set₁) → Set₂
pingMainActor i A = ∞ActorM i Pingbox A PingRefs constPingrefs

mutual
  pingReceive : ∀ {i} (msg : Message Pingbox) → ∞ActorM i Pingbox (Lift Bool) (add-references PingRefs msg) constPingrefs
  pingReceive (Msg Z (b ∷ [])) = return b
  pingReceive (Msg (S Z) _) = strengthen (S Z ∷ []) >> loopTillPingValue
  pingReceive (Msg (S (S ())) x₁)

  loopTillPingValue : ∀ {i} → pingMainActor i (Lift Bool)
  loopTillPingValue .force = receive ∞>>= pingReceive

pinger : ∀ {i} → ∞ActorM (↑ i) Pingbox ⊤₁ [] constPingrefs
pinger .force = loopTillPong ∞>> pingMain 0
  where
    loopTillPong : ∀ {i} → ∞ActorM i Pingbox ⊤₁ [] constPingrefs
    loopTillPong .force = receive ∞>>= ((λ
      { (Msg Z x₁) → loopTillPong
      ; (Msg (S Z) x₁) → return _
      ; (Msg (S (S ())) x₁)
      }))
    pingMain : ∀ {i} → ℕ → pingMainActor i ⊤₁
    pingMain n .force = loopTillPingValue ∞>>= λ
      { (lift false) → (Z ![t: Z ] (lift n ∷ [])) >> pingMain (suc n)
      ; (lift true) → return _}

constPongrefs : {A : Set₁} → (A → TypingContext)
constPongrefs _ = PongRefs

pongMainActor : (i : Size) (A : Set₁) → Set₂
pongMainActor i A = ∞ActorM i Pongbox A PongRefs constPongrefs

mutual
  pongReceive : ∀ {i} (msg : Message Pongbox) → ∞ActorM i Pongbox (Lift ℕ) (add-references PongRefs msg) constPongrefs
  pongReceive (Msg Z (n ∷ [])) = return n
  pongReceive (Msg (S Z) _) = strengthen (S Z ∷ []) >> loopTillPongValue
  pongReceive (Msg (S (S ())) _)
  loopTillPongValue : ∀ {i} → pongMainActor i (Lift ℕ)
  loopTillPongValue .force = receive ∞>>= pongReceive

ponger : ∀ {i} → ∞ActorM (↑ i) Pongbox ⊤₁ [] constPongrefs
ponger .force = loopTillPing ∞>> ((Z ![t: Z ] ((lift false) ∷ [])) >> pongMain)
  where
    loopTillPing : ∀ {i} → ∞ActorM i Pongbox ⊤₁ [] constPongrefs
    loopTillPing .force = receive ∞>>= λ {
      (Msg Z _) → loopTillPing
      ; (Msg (S Z) _) → return _
      ; (Msg (S (S ())) _)
      }
    pongMain : ∀ {i} → pongMainActor i ⊤₁
    pongMain .force = loopTillPongValue ∞>>= λ {
      (lift 10) → Z ![t: Z ] ((lift true) ∷ [])
      ; (lift n) → (Z ![t: Z ] ((lift false) ∷ [])) >> pongMain
      }

-- TODO: this needs to look prettier
spawner : ∀ {i} → ∞ActorM i Spawnbox ⊤₁ [] (λ _ → Pingbox ∷ Pongbox ∷ [])
spawner = do
  spawn∞ ponger
  spawn∞ pinger
  Z ![t: S Z ] (([ (S Z) ]>: (Z ∷ [])) ∷ [])
  S Z ![t: S Z ] (([ Z ]>: (Z ∷ [])) ∷ [])
