module ActorMonad where
open import Membership-equality using (_∈_)
open import Sublist using (_⊆_)

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (⊤ ; tt)

open import Coinduction using (∞ ; ♯_)
open import Level using (Lift ; lift ; suc ; zero)

-- An Actor is indexed by the shape of its inbox.
-- The shape is constant over the actors whole life-time
-- The use of coinduction is a product of wanting to allow actors to have mutual references
-- Alternative solutions are welcome
--
-- Values and references are kept separate, since the sending and receiving of values have different behaviour from sending and receiving references.
record InboxShape : Set₁ where
  coinductive
  field Values : List Set
        References : List InboxShape

-- A value message is a proof that the receiver accepts values of that type, and the value itself
data ValueMessage (S : InboxShape) : Set₁ where
  Value : ∀ {A} → A ∈ InboxShape.Values S → A → ValueMessage S

-- A reference message is just the proof that the receiver accepts references of that type
-- The constructors in ActorM is what limits the sending of references to only those that are valid in the current context
-- ReferenceMessage is indexed by both the reference type and the receiver's inbox shape due to the needs of ActorM
data ReferenceMessage (S Fw : InboxShape) : Set₁ where
  Reference : Fw ∈ InboxShape.References S → ReferenceMessage S Fw

-- A Message is either a value or a reference
data Message (S : InboxShape): Set₁ where
  Value : ∀ {A} → A ∈ InboxShape.Values S → A → Message S
  Reference : ∀ {Fw} → Fw ∈ InboxShape.References S → Message S

-- Simple lifting of ⊤ to reduce noise when the monad returns ⊤
⊤₁ : Set₁
⊤₁ = Lift ⊤

-- When a message is received, we increase our capabilities iff the message is a reference
addIfRef : ∀ {S} → List InboxShape → Message S → List InboxShape
addIfRef es (Value _ _) = es
addIfRef es (Reference {Fw} _) = Fw ∷ es

infixl 1 _>>=_

-- An Actor is a monad.
--
-- It is indexed by the shape of its inbox, which can't change over the course of its life-time.
--
-- 'A' is the return value of the monad.
--
-- 'es' is the precondition on the list of references that are available.
-- Sending a message is done by indexing into 'es'.
--
-- 'ce' is the postcondition on the list of references.
-- The postcondition some times depends on what happens during runtime,
-- and is thus modelled as a function on 'A'.
-- 'ce' is what enables receive to have the right type.
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
    (msg : ReferenceMessage ToIS FwIS) →
    ActorM IS ⊤₁ es (λ _ → es)
  Receive : ∀ {es} → ActorM IS (Message IS) es (addIfRef es)
  ALift   : ∀ {A ys ce xs} → (inc : ys ⊆ xs) →
    ∞ (ActorM IS A ys ce) →
    ActorM IS A xs ce
  Self : ∀ {es} → ActorM IS ⊤₁ es (λ _ → IS ∷ es)

--
-- ========== Helpers for ActorM ==========
--

-- coinduction helper for Value
return₁ : {A : Set (suc zero)} → ∀ {IS ce} → (val : A) → ∞ (ActorM IS A (ce val) ce)
return₁ val = ♯ Value val

-- universe lifting for return₁
return : {A : Set} → ∀ {IS ce} → (val : A) → ∞ (ActorM IS (Lift A) (ce (lift val)) ce)
return val = return₁ (lift val)

-- coinduction helper for spawn
spawn : ∀ {IS NewIS A es ceN} →
  ActorM NewIS A [] ceN →
  ∞ (ActorM IS ⊤₁ es λ _ → NewIS ∷ es)
spawn newAct = ♯ Spawn newAct

-- coinduction helper and neater syntax for value sending
_!v_ : ∀ {IS ToIS es} →
  (canSendTo : ToIS ∈ es) →
  (msg : ValueMessage ToIS) →
  ∞ (ActorM IS ⊤₁ es (λ _ → es))
canSendTo !v msg = ♯ SendValue canSendTo msg

-- coinduction helper and neater syntax for reference sending
to_!r_via_ : ∀ {IS es} → {ToIS FwIS : InboxShape} →
  (canSendTo : ToIS ∈ es) →
  (msg : ReferenceMessage ToIS FwIS)
  (canForward : FwIS ∈ es) →
  ∞ (ActorM IS ⊤₁ es (λ _ → es))
to canSendTo !r msg via canForward = ♯ SendReference canSendTo canForward msg

-- coinduction helper for Receive
receive : ∀ {IS es} → ∞ (ActorM IS (Message IS) es (addIfRef es))
receive = ♯ Receive
