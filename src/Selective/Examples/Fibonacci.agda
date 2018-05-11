module Selective.Examples.Fibonacci where

open import Selective.ActorMonad
open import Prelude

open import Debug
open import Data.Nat.Show using (show)

data End : Set where
  END : End

ℕ-message : MessageType
ℕ-message = [ ValueType ℕ ]ˡ

End-message : MessageType
End-message = [ ValueType End ]ˡ

Client-to-Server : InboxShape
Client-to-Server = ℕ-message ∷ [ End-message ]ˡ

Server-to-Client : InboxShape
Server-to-Client = [ ℕ-message ]ˡ


ServerInterface : InboxShape
ServerInterface = [ ReferenceType Server-to-Client ]ˡ ∷ Client-to-Server

ClientInterface : InboxShape
ClientInterface = [ ReferenceType Client-to-Server ]ˡ ∷ Server-to-Client

ServerRefs : TypingContext
ServerRefs = [ Server-to-Client ]ˡ

constServerRefs : {A : Set₁} → (A → TypingContext)
constServerRefs _ = ServerRefs

data ServerAction : Set₁ where
  Next : ℕ → ServerAction
  Done : ServerAction

server : ∀ {i} → ActorM i ServerInterface ⊤₁ [] constServerRefs
server = wait-for-client ∞>> run-fibonacci 1
  where
    wait-for-client = selective-receive (λ {
      (Msg Z _) → true
      ; (Msg (S _) _) → false }) >>= λ {
        record { msg = (Msg Z _) } → return tt
        ; record { msg = (Msg (S _) _) ; msg-ok = () } }
    wait-for-value : ∀ {i} → ∞ActorM i ServerInterface ServerAction ServerRefs constServerRefs
    wait-for-value = selective-receive (λ {
      (Msg Z _) → false
      ; (Msg (S Z) _) → true
      ; (Msg (S (S Z)) _) → true
      ; (Msg (S (S (S ()))) x₁) }) >>= λ {
        record { msg = (Msg Z _) ; msg-ok = () }
        ; record { msg = (Msg (S Z) (n ∷ [])) } → return₁ (Next n)
        ; record { msg = (Msg (S (S Z)) _) } → return₁ Done
        ; record { msg = (Msg (S (S (S ()))) _) }
        }
    run-fibonacci : ℕ → ∀ {i} → ∞ActorM i ServerInterface ⊤₁ ServerRefs constServerRefs
    run-fibonacci x .force = begin do
      Next n ← wait-for-value
        where Done → return _
      let next = x + n
      Z ![t: Z ] [ lift next ]ᵃ
      (run-fibonacci next)

ClientRefs : TypingContext
ClientRefs = [ Client-to-Server ]ˡ

constClientRefs : {A : Set₁} → (A → TypingContext)
constClientRefs _ = ClientRefs

client : ∀ {i} → ActorM i ClientInterface ⊤₁ [] constClientRefs
client = wait-for-server ∞>> run 10 0
  where
    wait-for-server : ∀ {i} → ∞ActorM i ClientInterface ⊤₁ [] constClientRefs
    wait-for-server = selective-receive (λ {
      (Msg Z _) → true
      ; (Msg (S _) _) → false }) >>= λ {
        record { msg = (Msg Z _) ; msg-ok = msg-ok } → return tt
        ; record { msg = (Msg (S _) _) ; msg-ok = () }
        }
    wait-for-value : ∀ {i} → ∞ActorM i ClientInterface (Lift ℕ) ClientRefs constClientRefs
    wait-for-value = do
      record { msg = Msg (S Z) (n ∷ []) } ← selective-receive (λ {
        (Msg Z _) → false
        ; (Msg (S Z) _) → true
        ; (Msg (S (S ())) _) })
        where
          record { msg = (Msg Z _) ; msg-ok = () }
          record { msg = (Msg (S (S ())) x₁) }
      return n
    run : ℕ → ℕ → ∀ {i} → ∞ActorM i ClientInterface ⊤₁ ClientRefs constClientRefs
    run zero x = Z ![t: S Z ] [ lift END ]ᵃ
    run (suc todo) x .force = begin do
      (Z ![t: Z ] ((lift x) ∷ []))
      (lift n) ← wait-for-value
      let next = x + n
      run (debug (show next) todo) next

spawner : ∀ {i} → ∞ActorM i [] ⊤₁ [] (λ _ → ClientInterface ∷ [ ServerInterface ]ˡ)
spawner = do
  spawn server
  spawn client
  S Z ![t: Z ] [ [ Z ]>: ⊆-suc ⊆-refl ]ᵃ
  Z ![t: Z ] [ [ S Z ]>: ⊆-suc ⊆-refl ]ᵃ
