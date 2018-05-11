module Examples.PingPong where

open import ActorMonad public
open import Prelude

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
  PingValues = [ Bool ]ˡ
  PongValues = [ ℕ ]ˡ

  PingRefs : TypingContext
  PingRefs = [ ⊠-of-values PongValues ]ˡ
  PongRefs : TypingContext
  PongRefs = [ ⊠-of-values PingValues ]ˡ

  PongReferenceMessage : MessageType
  PongReferenceMessage = [ ReferenceType (⊠-of-values PongValues) ]ˡ

  BoolMessage : MessageType
  BoolMessage = [ ValueType Bool ]ˡ

  Pingbox : InboxShape
  Pingbox = BoolMessage ∷ [ PongReferenceMessage ]ˡ

  PingReferenceMessage : MessageType
  PingReferenceMessage = [ ReferenceType (⊠-of-values PingValues) ]ˡ

  NatMessage : MessageType
  NatMessage = [ ValueType ℕ ]ˡ

  Pongbox : InboxShape
  Pongbox = NatMessage ∷ [ PingReferenceMessage ]ˡ


constPingrefs : {A : Set₁} → (A → TypingContext)
constPingrefs _ =  PingRefs

pingMainActor : (i : Size) (A : Set₁) → Set₂
pingMainActor i A = ∞ActorM i Pingbox A PingRefs constPingrefs

mutual
  pingReceive : ∀ {i} (msg : Message Pingbox) → ∞ActorM i Pingbox (Lift Bool) (add-references PingRefs msg) constPingrefs
  pingReceive (Msg Z (b ∷ [])) = return b
  pingReceive (Msg (S Z) _) = strengthen [ S Z ]ᵐ >> loopTillPingValue
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
      { (lift false) → (Z ![t: Z ] ( [ lift n ]ᵃ)) >> pingMain (suc n)
      ; (lift true) → return _}

constPongrefs : {A : Set₁} → (A → TypingContext)
constPongrefs _ = PongRefs

pongMainActor : (i : Size) (A : Set₁) → Set₂
pongMainActor i A = ∞ActorM i Pongbox A PongRefs constPongrefs

mutual
  pongReceive : ∀ {i} (msg : Message Pongbox) → ∞ActorM i Pongbox (Lift ℕ) (add-references PongRefs msg) constPongrefs
  pongReceive (Msg Z (n ∷ [])) = return n
  pongReceive (Msg (S Z) _) = strengthen [ S Z ]ᵐ >> loopTillPongValue
  pongReceive (Msg (S (S ())) _)
  loopTillPongValue : ∀ {i} → pongMainActor i (Lift ℕ)
  loopTillPongValue .force = receive ∞>>= pongReceive

ponger : ∀ {i} → ∞ActorM (↑ i) Pongbox ⊤₁ [] constPongrefs
ponger .force = loopTillPing ∞>> ((Z ![t: Z ] ([ lift false ]ᵃ)) >> pongMain)
  where
    loopTillPing : ∀ {i} → ∞ActorM i Pongbox ⊤₁ [] constPongrefs
    loopTillPing .force = receive ∞>>= λ {
      (Msg Z _) → loopTillPing
      ; (Msg (S Z) _) → return _
      ; (Msg (S (S ())) _)
      }
    pongMain : ∀ {i} → pongMainActor i ⊤₁
    pongMain .force = loopTillPongValue ∞>>= λ {
      (lift 10) → Z ![t: Z ] [ lift true ]ᵃ
      ; (lift n) → Z ![t: Z ] [ lift false ]ᵃ >> pongMain
      }

spawner : ∀ {i} → ∞ActorM i Spawnbox ⊤₁ [] (λ _ → Pingbox ∷ [ Pongbox ]ˡ)
spawner = do
  spawn∞ ponger
  spawn∞ pinger
  Z ![t: S Z ] [ [ S Z ]>: [ Z ]ᵐ ]ᵃ
  S Z ![t: S Z ] [ [ Z ]>: [ Z ]ᵐ ]ᵃ
