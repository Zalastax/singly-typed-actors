module Selective.Examples.TestAC where

open import Selective.ActorMonad public
open import Selective.Examples.Channel public
open import Selective.Examples.Call2 public
open import Selective.Examples.ActiveObjects public

open import Data.List using (List ; _∷_ ; [] ; _++_ ; map)
open import Data.List.All using (All ; _∷_ ; []) renaming (map to ∀map)
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _≟_ )
open import Size
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality
            using (_≡_ ; refl ; cong ; sym ; inspect ; [_] ; trans)
open import Membership using (
              _∈_ ; _⊆_ ; S ; Z ; _∷_ ; []
              ; ⊆-refl ; ⊆-trans ; ⊆-suc ; translate-⊆
              ; lookup-all
              )
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary using (yes ; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Product using (Σ ; _,_ ; _×_ ; Σ-syntax)
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)

hej-ci : ChannelInitiation
hej-ci = record {
  request = Calculator
  ; response = record { channel-shape = CalculatorResponse ; all-tagged = (HasTag _) ∷ [] }
  ; request-tagged = (HasTag+Ref _) ∷ [] }

hej : (active-method Calculator ⊤₁ (λ _ → []) hej-ci)
hej (Msg Z (n ∷ m ∷ [])) v = return₁ (record { new-state = _ ; reply = SendM Z ((lift (n + m)) ∷ []) })
hej (Msg (S ()) _) _

HEJ : ActiveObject
HEJ = record {
  state-type = ⊤₁
  ; vars = λ _ → []
  ; methods = hej-ci ∷ []
  ; handlers = hej ∷ []
  }

hej-actor = run-active-object HEJ _

hej-test-actor : ∀{i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
hej-test-actor = do
  spawn∞ hej-actor
  Msg Z (tag ∷ n ∷ []) ← call CalculatorProtocol (record {
    var = Z
    ; chosen-field = Z
    ; fields = (lift 32) ∷ ((lift 10) ∷ [])
    ; session = record {
      can-request = ⊆-refl
      ; response-session = record {
        can-receive = Z ∷ []
        ; tag = 0
        }
      }
    })
    where
      Msg (S ()) _
  (strengthen [])
  (return n)
