module ActorMonad where
open import Membership using (_∈_ ; _⊆_ ; xs⊆xs)

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (⊤ ; tt)

open import Coinduction using (∞ ; ♯_)
open import Level using (Lift ; lift ; suc ; zero)

-- An Actor is indexed by the shape of its inbox.
--
-- The shape dictates what types the messages sent to an actor can have,
-- and thus also what types the messages being received by the actor can have.
--
-- The shape is constant over the actors whole life-time.
-- It would be nice to allow the shape to grow monotonically over time.
--
-- The use of coinduction is a product of wanting to allow actors to have mutual references
-- Alternative solutions are welcome
--
-- Values and references are kept separate,
--  since the sending and receiving of values have different behaviour from sending and receiving references.
mutual
  record InboxShape : Set₁ where
    coinductive
    field
      value-types : ValueTypes
      reference-types : ReferenceTypes

  ReferenceTypes = List InboxShape
  ValueTypes = List Set

-- A type is a value type for an inbox of shape S,
-- if it is an element of the value-types list for S.
_is-value-in_ : Set → InboxShape → Set₁
A is-value-in S = A ∈ InboxShape.value-types S

-- An inbox shape is a reference type for an inbox of shape S,
-- if it is an element of the reference-types list for S.
_is-reference-in_ : InboxShape → InboxShape → Set₁
R is-reference-in S = R ∈ InboxShape.reference-types S

-- An inbox shape can be used in place of another if
-- it accepts every value and reference of the other.
record [_]-handles-all-of-[_] (actual wanted : InboxShape) : Set₁ where
  field
    values-sub : InboxShape.value-types wanted ⊆ InboxShape.value-types actual
    references-sub : InboxShape.reference-types wanted ⊆ InboxShape.reference-types actual

-- A reference can be used in place of another reference in S if
-- it accepts every value and reference of the other,
-- and of course, the other has to be in S  
record [_]-is-super-reference-in-[_] (Fw S : InboxShape) : Set₁ where
  field
    {wanted} : InboxShape
    wanted-is-reference : wanted is-reference-in S
    fw-handles-wanted : [ Fw ]-handles-all-of-[ wanted ]

-- We can create a value message for an inbox of shape S,
-- if the type of the value is a value type for S.
data ValueMessage (S : InboxShape) : Set₁ where
  Value : ∀ {A} → A is-value-in S → A → ValueMessage S

-- We can create a reference message for an inbox of shape S,
-- if the type of the reference is a reference type for S.
--
-- When a reference message is received, the actors capabilities will increase,
-- allowing the actor to send messages to the actor referenced by the message.
--
-- A reference message can be created without having a valid reference in the current context.
-- It is the constructors of ActorM (more specifically SendReference) that limits the sending
-- of references to only those that are valid in the current context.
--
-- We index ReferenceMessage by both the reference type and the receiver's inbox.
data ReferenceMessage (S Fw : InboxShape) : Set₁ where
  Reference : [ Fw ]-is-super-reference-in-[ S ] → ReferenceMessage S Fw

-- A Message is either a value or a reference.
--
-- We could just have wrapped ValueMessage and ReferenceMessage,
-- but that makes for a noisier experience when pattern matching in application code.
data Message (S : InboxShape): Set₁ where
  Value : ∀ {A} → A is-value-in S → A → Message S
  Reference : ∀ {Fw} → Fw is-reference-in S → Message S

-- Simple lifting of ⊤ to reduce noise when the monad returns ⊤
⊤₁ : Set₁
⊤₁ = Lift ⊤

-- When a message is received, we increase our capabilities iff the message is a reference.
add-if-reference : ∀ {S} → ReferenceTypes → Message S → ReferenceTypes
add-if-reference pre (Value _ _) = pre
add-if-reference pre (Reference {Fw} _) = Fw ∷ pre

infixl 1 _>>=_

-- An Actor is modeled as a monad.
--
-- It is indexed by the shape of its inbox, which can't change over the course of its life-time.
--
--
-- 'A' is the return value of the monad.
--
-- 'pre' is the precondition on the list of references that are available.
-- The precondition is what limits an actor to only being able to send messages
-- to actors that it has a reference to.
-- Sending a message is done by indexing into 'es',
-- thereby proving that the actor has a reference to the actor
-- that it's sending the message to.
--
-- 'post' is the postcondition on the list of references.
-- The postcondition sometimes depends on what happens during runtime,
-- and is thus modelled as a function on 'A'.
-- 'post' is what enables receive to have the right type.
data ActorM (IS : InboxShape) : (A : Set₁) →
              (pre : ReferenceTypes) →
              (post : A → ReferenceTypes) →
              Set₂ where
  -- Value is also known as return.
  -- The precondition is the same as the assignment axiom schema in Hoare logic.
  Value : ∀ {A post} → (val : A) → ActorM IS A (post val) post
  -- Bind / composition
  -- This is the same as the rule of composition in Hoare logic.
  -- post₁ is the midcondition.
  _>>=_ : ∀ {A B pre post₁ post₂} → (m : ∞ (ActorM IS A pre post₁)) →
          (f : (x : A) → ∞ (ActorM IS B (post₁ x) (post₂))) →
          ActorM IS B pre post₂
  -- Spawn a new actor.
  -- The spawned actor does not know any references.
  -- The reference to the spawned actor is added to the parent actor.
  Spawn : {NewIS : InboxShape} → {A : Set₁} → ∀ {pre postN} →
          ActorM NewIS A [] postN →
          ActorM IS ⊤₁ pre λ _ → NewIS ∷ pre
  -- Send a value to an actor.
  -- A value can only be sent to an actor if a reference to it is
  -- available in the precondition.
  -- ValueMessage is indexed by the shape of the inbox we're sending to,
  -- which makes sure that it's not possible to send values of the wrong type.
  SendValue : ∀ {pre} → {ToIS : InboxShape} →
    (canSendTo : ToIS ∈ pre) →
    (msg : ValueMessage ToIS) →
    ActorM IS ⊤₁ pre (λ _ → pre)
  -- Send a reference to an actor.
  -- A reference can only be sent to an actor if a reference to it is
  -- available in the precondition.
  -- The reference being sent also has to be available in the precondition.
  -- ReferenceMessage is indexed by the shape of both the shape of the forwarded
  -- reference and the shape of the receiving inbox.
  SendReference : ∀ {pre} → {ToIS FwIS : InboxShape} →
    (canSendTo : ToIS ∈ pre) →
    (canForward : FwIS ∈ pre) →
    (msg : ReferenceMessage ToIS FwIS) →
    ActorM IS ⊤₁ pre (λ _ → pre)
  -- Receive a message.
  -- When receiving a message, the postcondition depends on whether the message
  -- is a value or a reference.
  -- If the message is a value, the postcondition is the same as the precondition.
  -- If the message is a reference, the postcondition is the reference cons'ed to the precondition.
  -- If a receive is encountered when there are no messages in the actor's inbox,
  -- then the actor is moved to the 'blocked queue'.
  -- Sending a message to a blocked actor will move the actor from the 'blocked queue' back to the
  -- active actors.
  Receive : ∀ {pre} → ActorM IS (Message IS) pre (add-if-reference pre)
  -- Lift let's you call a sub-program that needs less references than what is currently available.
  -- To allow that a lifted program increases the available references,
  -- the postcondition of the resulting actor is the same as the postcondition of the lifted program.¨
  -- We'd like there to be a way of re-adding the forgotten references, but that's easy to implement.
  -- To implement re-adding references we'd have to carry around what references to re-add when the
  -- lifted part is finished.
  ALift   : ∀ {A ys post xs} → (inc : ys ⊆ xs) →
    ∞ (ActorM IS A ys post) →
    ActorM IS A xs post
  -- Adds the reference to this actor to its available references.
  Self : ∀ {pre} → ActorM IS ⊤₁ pre (λ _ → IS ∷ pre)

--
-- ========== Helpers for ActorM ==========
--

-- coinduction helper for Value
return₁ : {A : Set (suc zero)} → ∀ {IS post} → (val : A) → ∞ (ActorM IS A (post val) post)
return₁ val = ♯ Value val

-- universe lifting for return₁
return : {A : Set} → ∀ {IS post} → (val : A) → ∞ (ActorM IS (Lift A) (post (lift val)) post)
return val = return₁ (lift val)

-- coinduction helper for spawn
spawn : ∀ {IS NewIS A pre postN} →
  ActorM NewIS A [] postN →
  ∞ (ActorM IS ⊤₁ pre λ _ → NewIS ∷ pre)
spawn newAct = ♯ Spawn newAct

-- coinduction helper and neater syntax for value sending
_!v_ : ∀ {IS ToIS pre} →
  (canSendTo : ToIS ∈ pre) →
  (msg : ValueMessage ToIS) →
  ∞ (ActorM IS ⊤₁ pre (λ _ → pre))
canSendTo !v msg = ♯ SendValue canSendTo msg

-- coinduction helper and neater syntax for reference sending
to_!r_via_ : ∀ {IS pre} → {ToIS FwIS : InboxShape} →
  (canSendTo : ToIS ∈ pre) →
  (msg : ReferenceMessage ToIS FwIS)
  (canForward : FwIS ∈ pre) →
  ∞ (ActorM IS ⊤₁ pre (λ _ → pre))
to canSendTo !r msg via canForward = ♯ SendReference canSendTo canForward msg

-- coinduction helper for Receive
receive : ∀ {IS pre} → ∞ (ActorM IS (Message IS) pre (add-if-reference pre))
receive = ♯ Receive

-- An inbox can handle every value and reference of itself
handles-self : {IS : InboxShape} → [ IS ]-handles-all-of-[ IS ]
handles-self = record { values-sub = xs⊆xs ; references-sub = xs⊆xs }
