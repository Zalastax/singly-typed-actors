module Examples.Call where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.List.All using (All ; _∷_ ; [])
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Coinduction
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; sym ; inspect ; [_] ; trans)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; _∷_ ; [] ; ⊆-refl ; ⊆-trans ; ⊆-suc ; translate-⊆)
open import Data.Unit using (⊤ ; tt)
open import Examples.SelectiveReceive --  using (selective-receive ; SelRec ; waiting-refs ; add-references++)

open SelRec

call-select-unwrap : ∀ {MtIn MT} {IS : InboxShape} → MT ∈ IS → MtIn ∈ IS → Bool
call-select-unwrap Z Z = true
call-select-unwrap Z (S p) = false
call-select-unwrap (S x) Z = false
call-select-unwrap (S x) (S p) = call-select-unwrap x p

call-select : ∀ {IS IS' MtIn} → IS' <: IS → MtIn ∈ IS' → Message IS → Bool
call-select sub which (Msg x x₁) = call-select-unwrap x (translate-⊆  sub which)

call : ∀ {Γ MtTo MtIn} {To IS IS' : InboxShape} → (q : List (Message IS)) → (Γ ⊢ To) →
       ((ReferenceType IS' ∷ MtTo) ∈ To) → All (send-field-content Γ) MtTo →
       (ISsubs : IS' <: IS) → (whichIn : MtIn ∈ IS') →
       (ActorM IS (SelRec IS (call-select ISsubs whichIn)) (Γ ++ (waiting-refs q)) (λ m → (add-references Γ (msg m)) ++ (waiting-refs (waiting m))))
call {Γ} {IS = IS} q var toFi vals sub whichIn = ♯ Self >>= λ _ →
  ♯ ((S (translate-⊆ (⊆++-refl Γ (waiting-refs q)) var) ![t: toFi ] (([ Z ]>: sub) ∷ translate-fields vals)) >>= λ _ →
  ♯ (strengthen (⊆-suc ⊆-refl) >>= λ _ →
  ♯ selective-receive q (call-select sub whichIn)))
  where
    translate-fields : ∀ {MT} → All (send-field-content  Γ) MT → All (send-field-content (IS ∷ Γ ++ waiting-refs q)) MT
    translate-fields {[]} [] = []
    translate-fields {ValueType x ∷ MT} (px ∷ ps) = px ∷ translate-fields ps
    translate-fields {ReferenceType x ∷ MT} (([ p ]>: v) ∷ ps) = ([ (S (∈-inc Γ (waiting-refs q) _ p)) ]>: v) ∷ (translate-fields ps)

Calculator : InboxShape
Calculator = (ReferenceType ((ValueType ℕ ∷ []) ∷ []) ∷ ValueType ℕ ∷ ValueType ℕ ∷ []) ∷ []

calculatorActor : ActorM Calculator (Lift ⊤) [] (λ _ → [])
calculatorActor = loop >>= return₁
  where
    loop : ∞ (ActorM Calculator (Lift ⊤) [] (λ _ → []))
    loop = ♯ (receive >>= λ {
      (Msg Z (_ ∷ n ∷ m ∷ [])) → ♯ ((Z ![t: Z ] ((lift (n + m)) ∷ [])) >>= λ _ → ♯ (strengthen [] >>= λ _ → loop))
      ; (Msg (S ()) x₁)
      })

TestBox : InboxShape
TestBox = ((ValueType ℕ ∷ [])) ∷ [] ∷ []

calltestActor : ActorM TestBox (Lift ℕ) [] (λ _ → [])
calltestActor = spawn calculatorActor >>= (λ _ →
            ♯ (_>>=_ { mid = λ m → add-references (Calculator ∷ []) (msg m) ++ waiting-refs (waiting m)}
              (♯ (call [] Z Z ((lift 10) ∷ ((lift 32) ∷ []))) (Z ∷ []) Z)  λ x →
              ♯ ( strengthen [] >>= λ _ →
              return-result x)))
  where
    return-result : SelRec TestBox (call-select (Z ∷ []) Z) → ∞ (ActorM TestBox (Lift ℕ) [] (λ _ → []))
    return-result record { msg = (Msg Z (px ∷ x₁)) ; right-msg = right-msg ; waiting = waiting } = return px
    return-result record { msg = (Msg (S x) x₁) ; right-msg = () }

