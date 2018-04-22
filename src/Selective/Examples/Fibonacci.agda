module Selective.Examples.Fibonacci where

open import Selective.ActorMonad public
open import Data.List using (List ; _∷_ ; [])
open import Data.List.All using (All ; _∷_ ; [])
open import Data.Bool using (Bool  ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Size
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; _∷_ ; [] ; ⊆-refl ; ⊆-suc)
open import Data.Unit using (⊤ ; tt)

open import Debug
open import Data.Nat.Show using (show)

data End : Set where
  END : End

ℕ-message : MessageType
ℕ-message = ValueType ℕ ∷ []

End-message : MessageType
End-message = ValueType End ∷ []

Client-to-Server : InboxShape
Client-to-Server = ℕ-message ∷ End-message ∷ []

Server-to-Client : InboxShape
Server-to-Client = ℕ-message ∷ []


ServerInterface : InboxShape
ServerInterface =
  (ReferenceType Server-to-Client ∷ [])
  ∷ Client-to-Server

ClientInterface : InboxShape
ClientInterface =
  (ReferenceType Client-to-Server ∷ [])
  ∷ Server-to-Client

ServerRefs : TypingContext
ServerRefs = Server-to-Client ∷ []

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
      (Z ![t: Z ] (lift next ∷ []))
      (run-fibonacci next)

ClientRefs : TypingContext
ClientRefs = Client-to-Server ∷ []

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
    run zero x = Z ![t: S Z ] ((lift END) ∷ [])
    run (suc todo) x .force = begin do
      (Z ![t: Z ] ((lift x) ∷ []))
      (lift n) ← wait-for-value
      let next = x + n
      run (debug (show next) todo) next

spawner : ∀ {i} → ∞ActorM i [] ⊤₁ [] (λ _ → ClientInterface ∷ ServerInterface ∷ [])
spawner = do
  (spawn server)
  (spawn client)
  (S Z ![t: Z ] (([ Z ]>: ⊆-suc ⊆-refl) ∷ []))
  (Z ![t: Z ] (([ S Z ]>: ⊆-suc ⊆-refl) ∷ []))
