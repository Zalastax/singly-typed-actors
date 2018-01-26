module Embedding where

open import Agda.Primitive
open import Prelude.Unit using (⊤ ; tt)
open import Prelude.Nat
open import Prelude.Product
open import Prelude.List
open import Prelude.Maybe
open import Prelude.Equality
open import AocUtil
open import AocIO
open import Prelude.String
open import Foreign.Haskell using (Unit)
open import Prelude.Show

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

Name = Nat
InboxType = Set

data ActorRef : (InboxType : Set) → Set where
  create-actor-ref : ∀ {A} → Name → ActorRef A

data Actor (IT : InboxType) : (Value : Set) → Set₁ where
  Return : ∀ {A} → A → Actor IT A
  Bind : ∀ {A B} →
    (m : Actor IT A) →
    (f : A → Actor IT B) →
    Actor IT B
  Spawn : {NewIT : InboxType} → {A : Set} →
    Actor NewIT A →
    Actor IT (ActorRef NewIT)
  Send : {ToIT : InboxType} →
    ActorRef ToIT →
    ToIT →
    Actor IT ⊤
  Receive : Actor IT IT
  Self : Actor IT (ActorRef IT)

ActorContainer = Σ[ IT ∈ InboxType ] Σ[ A ∈ Set ] (Actor IT A × List IT)

data Trace : Set where
  Return : Nat → Trace
  Bind : Nat → Trace
  Spawn : Nat → Nat → Trace
  Send : Nat → Nat → Trace
  Receive : Nat → Trace
  Self : Nat → Trace
  Crash : Trace
  OutOfSteps : Trace
  ActorsDone : Trace

Env : Set₁
Env = List (Name × ActorContainer)

postulate trustMeEqualTypes : (A B : Set) → A ≡ B

-- The running processes are taken in a round-robin fashion
-- remember to actually do round-robin...
run : Nat → Env → List Name → List Trace
run 0 _ _ = [ OutOfSteps ]
run (suc steps) env [] = [ ActorsDone ]
run (suc steps) env (name ∷ running) = maybeStep (lookup env name)
  where
    bindStep : ∀ {A} → (IT : InboxType) → (B : Set) → List IT → Actor IT A → (A → Actor IT B) → List Trace
    bindStep IT B inb (Return x) f = Return name ∷ run steps ((name , IT , (B , (f x , inb))) ∷ env) (name ∷ running)
    bindStep IT B inb (Bind act f₁) f = Bind name ∷ run steps ((name , IT , (B , (Bind act λ a₁ → Bind (f₁ a₁) f ) , inb)) ∷ env) (name ∷ running)
    bindStep IT refT inb (Spawn {NewIT} {A} act) f with (length env)
    ... | n with (create-actor-ref n)
    ... | ref = Spawn name n ∷ run steps ((n , NewIT , (A , (act , []))) ∷ (name , IT , (refT , f ref , inb)) ∷ env) (n ∷ name ∷ running)
    bindStep IT B inb (Send {ToIT} (create-actor-ref n) v) f with (lookup env n)
    ... | nothing = [ Crash ]
    ... | just (T , (C , act , inb2)) with (trustMeEqualTypes T ToIT)
    ... | p rewrite p = Send name n ∷ run steps ((n , ToIT , (C , act , v ∷ inb2)) ∷ (name , IT , (B , ((f tt) , inb))) ∷ env) (n ∷ name ∷ running)
    bindStep IT B [] Receive f = run steps env running --It's OK to just remove it from running, we will log the bind again but whatevs
    bindStep IT B (x ∷ inb) Receive f = Receive name ∷ run steps ((name , (IT , (B , (f x) , inb))) ∷ env) (name ∷ running)
    bindStep IT B inb Self f = Self name ∷ run steps ((name , (IT , (B , ((f (create-actor-ref name)) , inb)))) ∷ env) (name ∷ running)
    step : (IT : InboxType) → (A : Set) → List IT → Actor IT A → List Trace
    step IT A inb (Return x) = Return name ∷ run steps env running -- not changin the environment, maybe bad? it's removed from running at least
    step IT A inb (Bind act f) = (bindStep IT A inb act f)
    step IT refT inb (Spawn {NewIT} {A} act) with (length env)
    ... | n with (create-actor-ref n)
    ... | ref = Spawn name n ∷ run steps ((n , (NewIT , A , (act , []))) ∷ (name , (IT , (refT , (Return ref) , inb))) ∷ env) (n ∷ running)
    step IT .⊤ inb (Send {ToIT} (create-actor-ref n) v) with (lookup env n)
    ... | nothing = [ Crash ]
    ... | (just (T , (B , act , inb2))) with (trustMeEqualTypes T ToIT)
    ... | p rewrite p = (Send name n ∷ run steps ((n , ToIT , (B , (act , v ∷ inb2))) ∷ (name , IT , (⊤ , (Return tt , inb))) ∷ env) (n ∷ running))
    step IT .IT [] Receive = run steps env running -- The actor is stuck, just remove it from the queue for now
    step IT .IT (x ∷ inb) Receive = Receive name ∷ run steps ((name , (IT , (IT , ((Return x) , inb)))) ∷ env) running
    step IT refT inb Self = Self name ∷ run steps ((name , (IT , refT , ((Return (create-actor-ref name)) , inb))) ∷ env) running
    maybeStep : Maybe ActorContainer → List Trace
    maybeStep nothing = [ Crash ]
    maybeStep (just (IT , A , act , inb)) = step IT A inb act

startActor : ∀ {IT A} → Nat → Actor IT A → List Trace
startActor {IT} {A} steps act = reverse (run steps ([ 0 , (IT , A , act , []) ]) ([ 0 ]))

myTrace : List Trace
myTrace = startActor {IT = ⊤} 1000 (Bind
          (Spawn {NewIT = Nat}
            (Bind
            (Spawn
              (Return {⊤} {⊤} tt)
            )
            λ _ → Bind
            Receive λ n → Return n
            )
          )
          λ ref → Send ref 5)

main : IO Unit
main = printTraces myTrace
  where
    stringify : Trace → String
    stringify (Return x) = "Return for " & show x
    stringify (Bind x) = "Bind for " & show x
    stringify (Spawn x y) = "Spawn for " & show x & " spawning " & show y
    stringify (Send x y) = "Send for " & show x & " to " & show y
    stringify (Receive x) = "Receive for " & show x
    stringify (Self x) = "Self for " & show x
    stringify Crash = "Crash!"
    stringify OutOfSteps = "Out of steps!"
    stringify ActorsDone = "Done!"
    printTrace : Trace → IO Unit
    printTrace t = printString (stringify t)
    printTraces : List Trace → IO Unit
    printTraces [] = return Unit.unit
    printTraces (x ∷ l) = printTrace x >>= λ _ → printTraces l
