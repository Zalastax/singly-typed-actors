module ActorEffect where

open import EffectUtil
import IO.Primitive as IO
open import Data.String using (String)
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Unit using (⊤ ; tt)
open import Category.Monad using (RawMonad)
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.All using (All ; lookup ; _∷_ ; [])
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership-≡ using (_∈_)
open import Data.Product using (Σ ; _,_ ; _×_)
open import Data.Nat using (ℕ ; zero ; suc)
open import Coinduction

Name = ℕ
InboxType = Set

record InboxShape : Set₁ where
  coinductive
  field Values : List Set
        References : List InboxShape


data ValueMessage (S : InboxShape) : Set₁ where
  Value : ∀ {A} → A ∈ InboxShape.Values S → A → ValueMessage S

data ReferenceMessage (S Fw : InboxShape) : Set₁ where
  Reference : Fw ∈ InboxShape.References S → ReferenceMessage S Fw

data Message (S : InboxShape): Set₁ where
  MsgV : ValueMessage S → Message S
  MsgR : ∀ {Fw} → ReferenceMessage S Fw → Message S

⊤₁ : Set₁
⊤₁ = Lift ⊤

addIfRef : ∀ {S} → List InboxShape → Message S → List InboxShape
addIfRef es (MsgV x) = es
addIfRef es (MsgR {Fw} x) = Fw ∷ es

infixl 1 _>>=_

data ActorM (IS : InboxShape) : (A : Set₁) →
              (es : List InboxShape) →
              (ce : A → List InboxShape) →
              Set₂ where
  Value : ∀ {A ce} → (val : A) → ActorM IS A (ce val) ce
  _>>=_ : ∀ {A B es ce₁ ce₂} → (m : ∞ (ActorM IS A es ce₁)) →
          (f : (x : A) → ∞ (ActorM IS B (ce₁ x) (ce₂))) →
          ActorM IS B es ce₂
  Spawn : {NewIS : InboxShape} → {A : Set₁} → ∀ {es ceN} →
          ActorM NewIS A [] ceN →
          ActorM IS ⊤₁ es λ _ → NewIS ∷ es
  SendValue : ∀ {es} → {ToIS : InboxShape} →
    (canSendTo : ToIS ∈ es) →
    (msg : ValueMessage ToIS) →
    ActorM IS ⊤₁ es (λ _ → es)
  SendReference : ∀ {es} → {ToIS FwIS : InboxShape} →
    (canSendTo : ToIS ∈ es) →
    (canForward : FwIS ∈ es) →
    ActorM IS ⊤₁ es (λ _ → es)
  Receive : ∀ {es} → ActorM IS (Message IS) es (addIfRef es)
  ALift   : ∀ {A ys ce xs} → (inc : ys ⊆ xs) →
    ∞ (ActorM IS A ys ce) →
    ActorM IS A xs (λ v → (ce v))

return : {A : Set} → ∀ {IS ce} → (val : A) → ∞ (ActorM IS (Lift A) (ce (lift val)) ce)
return val = ♯ Value (lift val)

return₁ : {A : Set (lsuc lzero)} → ∀ {IS ce} → (val : A) → ∞ (ActorM IS A (ce val) ce)
return₁ val = ♯ Value val


spawn : ∀ {IS NewIS A es ceN} →
  ActorM NewIS A [] ceN →
  ∞ (ActorM IS ⊤₁ es λ _ → NewIS ∷ es)
spawn newAct = ♯ Spawn newAct

_!v_ : ∀ {IS ToIS es} →
  (canSendTo : ToIS ∈ es) →
  (msg : ValueMessage ToIS) →
  ∞ (ActorM IS ⊤₁ es (λ _ → es))
canSendTo !v msg = ♯ SendValue canSendTo msg

_!r_ : ∀ {IS es} → {ToIS FwIS : InboxShape} →
  (canSendTo : ToIS ∈ es) →
  (canForward : FwIS ∈ es) →
  ∞ (ActorM IS ⊤₁ es (λ _ → es))
canSendTo !r canForward = ♯ SendReference canSendTo canForward

receive : ∀ {IS es} → ∞ (ActorM IS (Message IS) es (addIfRef es))
receive = ♯ Receive


open InboxShape

Spawnbox : InboxShape
Spawnbox = record { Values = [] ; References = [] }

mutual
  Pingbox : InboxShape
  Values Pingbox = Bool ∷ []
  References Pingbox = Pongbox ∷ []

  Pongbox : InboxShape
  Values Pongbox = ℕ ∷ []
  References Pongbox = Pingbox ∷ []

pingrefs : List InboxShape
pingrefs = Pongbox ∷ []

constPingrefs : {A : Set₁} → (A → List InboxShape)
constPingrefs _ =  pingrefs

pingMainActor : (A : Set₁) → Set₂
pingMainActor A = ActorM Pingbox A pingrefs constPingrefs

mutual
  pingReceive : (msg : Message Pingbox) → ∞ (ActorM Pingbox (Lift Bool) (addIfRef pingrefs msg) constPingrefs)
  pingReceive (MsgV (Value (here refl) b)) = return b
  pingReceive (MsgV (Value (there ()) _))
  pingReceive (MsgR x) = ♯ ALift (skip reflexive-⊆) loopTillPingValue

  loopTillPingValue : ∞ (pingMainActor (Lift Bool))
  loopTillPingValue = ♯ (receive >>= pingReceive)

pinger : ActorM Pingbox ⊤₁ [] constPingrefs
pinger = loopTillPong >>= (λ _ → pingMain 0)
  where
    loopTillPong : ∞ (ActorM Pingbox ⊤₁ [] constPingrefs)
    loopTillPong = ♯ (receive >>= ((λ
      { (MsgV _) → loopTillPong
      ; (MsgR (Reference (here refl))) → return _
      ; (MsgR (Reference (there ()))) })))
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
  pongReceive (MsgV (Value (here refl) n)) = return n
  pongReceive (MsgV (Value (there ()) _))
  pongReceive (MsgR x) = ♯ ALift (skip reflexive-⊆) loopTillPongValue

  loopTillPongValue : ∞ (pongMainActor (Lift ℕ))
  loopTillPongValue = ♯ (receive >>= pongReceive)

ponger : ActorM Pongbox ⊤₁ [] constPongrefs
ponger = loopTillPing >>= λ _ → pongMain
  where
    loopTillPing : ∞ (ActorM Pongbox ⊤₁ [] constPongrefs)
    loopTillPing = ♯ (receive >>= λ
      { (MsgV _) → loopTillPing
      ; (MsgR (Reference (here refl))) → return _
      ; (MsgR (Reference (there ())))})
    pongMain : ∞ (pongMainActor ⊤₁)
    pongMain = ♯ (loopTillPongValue >>= λ
      { (lift 10) → ♯ (here refl !v Value (here refl) true >>= λ _ → return _)
        ; (lift n) → ♯ (here refl !v Value (here refl) false >>= λ _ → pongMain)})

spawner : ActorM Spawnbox ⊤₁ [] (λ _ → Pingbox ∷ Pongbox ∷ [])
spawner = spawn ponger >>= λ _ →
          ♯ (spawn pinger >>= λ _ →
          ♯ (here refl !r there (here refl) >>= λ _ →
          there (here refl) !r here refl))
