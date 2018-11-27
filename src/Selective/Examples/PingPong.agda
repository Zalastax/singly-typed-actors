module Selective.Examples.PingPong where

open import Selective.ActorMonad public
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

ℕ₁ : Set₁
ℕ₁ = Lift (lsuc lzero) ℕ

Bool₁ : Set₁
Bool₁ = Lift (lsuc lzero) Bool

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

pinger : ∀ {i} → ∞ActorM (↑ i) Pingbox ⊤₁ [] constPingrefs
pinger .force = waitForPong ∞>> pingMain 0
  where
    waitForPong : ∀ {i} → ∞ActorM i Pingbox ⊤₁ [] constPingrefs
    waitForPong = selective-receive (λ {
      (Msg Z _) → false
      ; (Msg (S Z) _) → true
      ; (Msg (S (S ())) _)
      }) >>= λ {
        record { msg = (Msg Z _) ; msg-ok = () }
        ; record { msg = (Msg (S Z) _) ; msg-ok = refl } → return _
        ; record { msg = (Msg (S (S ())) x₁) }
      }
    waitForPingValue : ∀ {i Γ} → ∞ActorM i Pingbox Bool₁ Γ (λ _ → Γ)
    waitForPingValue = selective-receive (λ {
      (Msg Z _) → true
      ; (Msg (S Z) _) → false
      ; (Msg (S (S ())) _)
      }) >>= λ {
      record { msg = (Msg Z (b ∷ [])) ; msg-ok = refl } → return b
      ; record { msg = (Msg (S Z) _) ; msg-ok = () }
      ; record { msg = (Msg (S (S ())) x₁) }
      }
    pingMain : ∀ {i} → ℕ → pingMainActor i ⊤₁
    pingMain n .force = waitForPingValue ∞>>= λ
      { (lift false) → (Z ![t: Z ] ([ lift n ]ᵃ)) >> pingMain (suc n)
      ; (lift true) → return _}

constPongrefs : {A : Set₁} → (A → TypingContext)
constPongrefs _ = PongRefs

pongMainActor : (i : Size) (A : Set₁) → Set₂
pongMainActor i A = ∞ActorM i Pongbox A PongRefs constPongrefs

ponger : ∀ {i} → ∞ActorM (↑ i) Pongbox ⊤₁ [] constPongrefs
ponger .force = waitForPing ∞>> ((Z ![t: Z ] ([ lift false ]ᵃ)) >> pongMain)
  where
    waitForPing : ∀ {i} → ∞ActorM i Pongbox ⊤₁ [] constPongrefs
    waitForPing = selective-receive (λ {
      (Msg Z _) → false
      ; (Msg (S Z) _) → true
      ; (Msg (S (S ())) _)
      }) >>= λ {
        record { msg = (Msg Z _) ; msg-ok = () }
        ; record { msg = (Msg (S Z) x₁) ; msg-ok = refl } → return _
        ; record { msg = (Msg (S (S ())) x₁) }
        }
    waitForPongValue : ∀ {i Γ} → ∞ActorM i Pongbox ℕ₁ Γ (λ _ → Γ)
    waitForPongValue = selective-receive (λ {
      (Msg Z _) → true
      ; (Msg (S Z) _) → false
      ; (Msg (S (S ())) _)
      }) >>= λ {
        record { msg = (Msg Z (n ∷ [])) ; msg-ok = refl } → return n
        ; record { msg = (Msg (S Z) x₁) ; msg-ok = () }
        ; record { msg = (Msg (S (S ())) x₁) }
        }
    pongMain : ∀ {i} → pongMainActor i ⊤₁
    pongMain .force = waitForPongValue ∞>>= λ {
      (lift 10) → Z ![t: Z ] [ lift true ]ᵃ
      ; (lift n) → Z ![t: Z ] [ lift false ]ᵃ >> pongMain
      }

spawner : ∀ {i} → ∞ActorM i Spawnbox ⊤₁ [] (λ _ → Pingbox ∷ [ Pongbox ]ˡ)
spawner = do
  spawn∞ ponger
  spawn∞ pinger
  Z ![t: S Z ] [ [ S Z ]>: [ Z ]ᵐ ]ᵃ
  S Z ![t: S Z ] [ [ Z ]>: [ Z ]ᵐ ]ᵃ
