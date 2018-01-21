module Embedding where

open import Prelude.Unit
open import Prelude.Nat
open import Agda.Builtin.Nat

data ActorRef : (InboxType : Set) → Set where
  create-actor-ref : ∀ {A} → ActorRef A

data Actor (InboxType : Set) : (Value : Set) → Set₁ where
  Return : ∀ {A} → A → Actor InboxType A
  Bind : ∀ {A B} →
    (m : Actor InboxType A) →
    (f : A → Actor InboxType B) →
    Actor InboxType B
  Spawn : {NewInboxType : Set} → {a : Set} →
    Actor NewInboxType a →
    Actor InboxType (ActorRef NewInboxType)
  Send : ∀ {ToInboxType A : Set} →
    ActorRef ToInboxType →
    A →
    Actor InboxType ⊤
  Receive : Actor InboxType InboxType

