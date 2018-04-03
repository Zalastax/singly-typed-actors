
module Cont where

open import ActorMonad
open import SimulationEnvironment
open import Membership using (_∈_ ; _⊆_ ; [] ; _∷_ ; Z ; S ; lookup-parallel ; lookup-parallel-≡ ; translate-∈ ; x∈[]-⊥ ; translate-⊆ ; ⊆-trans ; find-∈)

open import Data.List using (List ; _∷_ ; [] ; map ; _++_ ; drop)
open import Data.List.All using (All ; _∷_ ; []; lookup) renaming (map to ∀map)
open import Data.List.All.Properties using (++⁺ ; drop⁺)
open import Data.List.Properties using (map-++-commute)
open import Data.List.Any using (Any ; here ; there)
open import Data.Nat using (ℕ ; zero ; suc ; _≟_ ; _<_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Data.Unit using (⊤ ; tt)
open import Data.Empty using (⊥ ; ⊥-elim)

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; sym ; cong ; cong₂ ; trans)
open import Relation.Nullary using (Dec ; yes ; no)

open import Level using (Lift ; lift)
open import Size using (Size; ∞)

open Actor
open ValidActor
open Env
open NamedInbox


Cont : ∀ (i : Size) (IS : InboxShape) {A B : Set₁}
              (pre : A → TypingContext)
              (post : B → TypingContext) →
              Set₂
Cont i IS {A} {B} pre post = (x : A) → ∞ActorM i IS B (pre x) post

data ContStack (i : Size) (IS : InboxShape) {A : Set₁} (pre : A → TypingContext) :
    ∀ {B : Set₁} (post : B → TypingContext) → Set₂ where
  []    : ContStack i IS pre pre
  _∷_   : ∀{B C}{mid : B → TypingContext} {post : C → TypingContext}
        → Cont i IS pre mid → ContStack i IS mid post → ContStack i IS pre post

record ActorState (i : Size) (IS : InboxShape) (C : Set₁) (pre : TypingContext) (post : C → TypingContext) : Set₂ where
  field
    {A}   : Set₁
    {mid} : A → TypingContext
    act   : ActorM i IS A pre mid
    cont  : ContStack i IS mid post
