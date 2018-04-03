module Examples.Call where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.List.All using (All ; _∷_ ; [])
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _≟_)
open import Coinduction
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality
            using (_≡_ ; refl ; cong ; sym ; inspect ; [_] ; trans)
open import Membership using (
            _∈_ ; _⊆_ ; S ; Z ; _∷_ ; [] ; ⊆-refl
            ; ⊆-trans ; ⊆-suc ; translate-⊆)
open import Data.Unit using (⊤ ; tt)
open import Examples.SelectiveReceive using (
            selective-receive ; SelRec ; waiting-refs
            ; add-references++ ; ∈-inc ; ⊆++-refl)
open import Relation.Nullary using (yes ; no)

open import Size

open SelRec

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
              Message IS →
              Bool
call-select tag sub which (Msg x fs) =
  call-select-unwrap tag x fs (translate-⊆  sub which)

call : ∀ {Γ MtTo MtIn i} {To IS IS' : InboxShape} →
       (q : List (Message IS)) →
       (Γ ⊢ To) →
       ((ValueType UniqueTag ∷ ReferenceType IS' ∷ MtTo) ∈ To) →
       (tag : UniqueTag) →
       All (send-field-content Γ) MtTo →
       (ISsubs : IS' <: IS) →
       (whichIn : (ValueType UniqueTag ∷ MtIn) ∈ IS') →
       ∞ActorM i IS
         (SelRec IS (call-select tag ISsubs whichIn))
         (Γ ++ (waiting-refs q))
         (λ m → (add-references Γ (msg m)) ++ (waiting-refs (waiting m)))
call {Γ} {IS = IS} q var toFi tag vals sub whichIn = do
     self
     S (translate-⊆ (⊆++-refl Γ (waiting-refs q)) var)
       ![t: toFi ]
       ((lift tag) ∷ ([ Z ]>: sub) ∷ (translate-fields vals))
     strengthen (⊆-suc ⊆-refl)
     selective-receive q (call-select tag sub whichIn)
  where
    translate-fields : ∀ {MT} → All (send-field-content  Γ) MT →
                         All (send-field-content (IS ∷ Γ ++ waiting-refs q)) MT
    translate-fields {[]} [] = []
    translate-fields {ValueType x ∷ MT} (px ∷ ps) =
      px ∷ translate-fields ps
    translate-fields {ReferenceType x ∷ MT} (([ p ]>: v) ∷ ps) =
      ([ (S (∈-inc Γ (waiting-refs q) _ p)) ]>: v) ∷ (translate-fields ps)

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
calculatorActor = loop
  where
    loop : ∀ {i} → ∞ActorM i Calculator (Lift ⊤) [] (λ _ → [])
    loop .force = receive ∞>>= λ {
      (Msg Z (tag ∷ _ ∷ n ∷ m ∷ [])) → do
        Z ![t: Z ] ((lift tag) ∷ (lift (n + m)) ∷ [])
        strengthen []
        loop
      ; (Msg (S ()) _) }

TestBox : InboxShape
TestBox = ((ValueType UniqueTag ∷ ValueType ℕ ∷ [])) ∷ [] ∷ []

calltestActor : ∀ {i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
calltestActor .force = spawn∞ calculatorActor ∞>>
                       [mid: (λ m → add-references (Calculator ∷ []) (msg m) ++
                                    waiting-refs (waiting m)) ]
                         call [] Z Z 0
                           ((lift 10) ∷ ((lift 32) ∷ []))
                           (Z ∷ []) Z >>=
                       λ x → strengthen [] >>
                       return-result x
  where
    return-result : SelRec TestBox (call-select 0 (Z ∷ []) Z) →
                    ∀ {i} → ∞ActorM i TestBox (Lift ℕ) [] (λ _ → [])
    return-result record { msg = (Msg Z (tag ∷ n ∷ [])) } = return n
    return-result record { msg = (Msg (S x) x₁) ; msg-ok = () }

