module Selective.Examples.Call where

open import Selective.ActorMonad public
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.List.All using (All ; _∷_ ; [])
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
              )
open import Data.Unit using (⊤ ; tt)
open import Relation.Nullary using (yes ; no)

open SelectedMessage

UniqueTag = ℕ

call-select-unwrap : ∀ {MtIn MT} {IS : InboxShape} →
                       UniqueTag →
                       MT ∈ IS →
                       All receive-field-content MT →
                       (ValueType UniqueTag ∷ MtIn) ∈ IS →
                       Bool
call-select-unwrap tag Z (tag' ∷ fs) Z with (tag ≟ tag')
... | yes p = true
... | no p = false
call-select-unwrap _ Z _ (S p) = false
call-select-unwrap _ (S x) _ Z = false
call-select-unwrap tag (S x) fs (S p) = call-select-unwrap tag x fs p

call-select : ∀ {IS IS' MtIn} →
                UniqueTag →
                IS' <: IS →
                (ValueType UniqueTag ∷ MtIn) ∈ IS' →
                MessageFilter IS
call-select {IS} tag sub which (Msg x fs) =
  call-select-unwrap tag x fs (translate-⊆  sub which)

call : ∀ {Γ MtTo MtIn i} {To IS IS' : InboxShape} →
       (Γ ⊢ To) →
       ((ValueType UniqueTag ∷ ReferenceType IS' ∷ MtTo) ∈ To) →
       (tag : UniqueTag) →
       All (send-field-content Γ) MtTo →
       (ISsubs : IS' <: IS) →
       (whichIn : (ValueType UniqueTag ∷ MtIn) ∈ IS') →
       ∞ActorM i IS
         (SelectedMessage (call-select tag ISsubs whichIn))
         Γ (add-selected-references Γ)
call {Γ} {IS = IS} var toFi tag vals sub whichIn = do
     self
     S var ![t: toFi ] ((lift tag) ∷ ([ Z ]>: sub) ∷ (translate-fields vals))
     strengthen (⊆-suc ⊆-refl)
     selective-receive (call-select tag sub whichIn)
  where
    translate-fields : ∀ {MT} →
                       All (send-field-content Γ) MT →
                       All (send-field-content (IS ∷ Γ)) MT
    translate-fields [] = []
    translate-fields {ValueType x ∷ MT} (px ∷ vals) =
      px ∷ (translate-fields vals)
    translate-fields {ReferenceType x ∷ MT} (([ p ]>: v) ∷ vals) =
      ([ (S p) ]>: v) ∷ (translate-fields vals)

Calculator : InboxShape
Calculator = (
  ValueType UniqueTag ∷
  ReferenceType ((
    ValueType UniqueTag ∷
    ValueType ℕ ∷ []) ∷ []
  ) ∷
  ValueType ℕ ∷
  ValueType ℕ ∷ []
  ) ∷ []

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
calltestActor .force = spawn∞ calculatorActor ∞>> (do
                       x ← call Z Z 0 ((lift 10) ∷ ((lift 32) ∷ [])) (Z ∷ []) Z
                       strengthen []
                       return-result x)
  where
    return-result : SelectedMessage {TestBox} (call-select 0 (Z ∷ []) Z) →
                    ∀ {i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
    return-result record { msg = (Msg Z (tag ∷ n ∷ [])) } = return n
    return-result record { msg = (Msg (S x) x₁) ; msg-ok = () }

