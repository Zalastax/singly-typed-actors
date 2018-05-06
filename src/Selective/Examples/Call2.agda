module Selective.Examples.Call2 where

open import Selective.ActorMonad public
open import Selective.Examples.Channel public
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

open ChannelType
open ChannelInitiation

call : ∀ {Γ i caller} →
        ∀ protocol →
        Request Γ caller protocol →
        ∞ActorM i caller (Message (protocol .response .channel-shape)) Γ (add-references Γ)
call protocol request =
  let
    open ChannelInitiationSession
    open Request
    open ChannelSession
  in do
    initiate-channel _ request
    let rs = request .session .response-session
    from-channel (protocol .response) rs

CalculatorResponse : InboxShape
CalculatorResponse = (
  ValueType UniqueTag ∷
  ValueType ℕ ∷ []) ∷ []

Calculator : InboxShape
Calculator = (
  ValueType UniqueTag ∷
  ReferenceType CalculatorResponse ∷
  ValueType ℕ ∷
  ValueType ℕ ∷ []
  ) ∷ []

CalculatorProtocol : ChannelInitiation
CalculatorProtocol = record
                       { request = Calculator
                       ; response = record {
                         channel-shape = CalculatorResponse
                         ; all-tagged = (HasTag _) ∷ []
                         }
                       ; request-tagged = (HasTag+Ref (ValueType ℕ ∷ ValueType ℕ ∷ [])) ∷ []
                       }

calculatorActor : ∀ {i} → ∞ActorM (↑ i) Calculator (Lift ⊤) [] (λ _ → [])
calculatorActor .force = receive ∞>>= λ {
  (Msg Z (tag ∷ _ ∷ n ∷ m ∷ [])) .force →
    (Z ![t: Z ] ((lift tag) ∷ (lift (n + m)) ∷ [])) ∞>> (do
    strengthen []
    calculatorActor)
  ; (Msg (S ()) _)
  }

TestBox : InboxShape
TestBox = (
  ValueType UniqueTag ∷
  ValueType ℕ ∷ []) ∷
  [] ∷ []

calltestActor : ∀{i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
calltestActor = do
  (spawn∞ calculatorActor)
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

