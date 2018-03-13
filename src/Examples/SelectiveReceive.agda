module Examples.SelectiveReceive where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [] ; _++_)
open import Data.List.All using (All ; _∷_ ; [])
open import Data.List.Properties using (++-assoc ; ++-identityʳ)
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Nat using (ℕ ; zero ; suc)
open import Coinduction
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; cong ; sym ; inspect ; [_] ; trans)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; _∷_ ; [] ; ⊆-refl ; ⊆-trans ; ⊆-suc)
open import Data.Unit using (⊤ ; tt)
open import Level using (Level) renaming (suc to lsuc)

record SelRec (IS : InboxShape) (f : Message IS → Bool) : Set₁ where
  field
    msg : Message IS
    right-msg : f msg ≡ true
    waiting : List (Message IS)

open SelRec

waiting-refs : ∀ {IS} → (q : List (Message IS)) → ReferenceTypes
waiting-refs [] = []
waiting-refs (x ∷ q) = add-references (waiting-refs q) x

record SplitList {a : Level} {A : Set a} (ls : List A) : Set (lsuc a) where
  field
    heads : List A
    el : A
    tails : List A
    is-ls : (heads) ++ (el ∷ tails) ≡ ls

data FoundInList {a : Level} {A : Set a} (ls : List A) (f : A → Bool) : Set (lsuc a) where
  Found : (split : SplitList ls) → (f (SplitList.el split) ≡ true) → FoundInList ls f
  Nothing : FoundInList ls f

find-split : {a : Level} {A : Set a} (ls : List A) (f : A → Bool) → FoundInList ls f
find-split [] f = Nothing
find-split (x ∷ ls) f with (f x) | (inspect f x)
... | false | p = add-x (find-split ls f)
  where
    add-x : FoundInList ls f → FoundInList (x ∷ ls) f
    add-x (Found split x₁) = Found (record { heads = x ∷ heads split ; el = el split ; tails = tails split ; is-ls = cong (_∷_ x) (is-ls split) }) x₁
      where open SplitList
    add-x Nothing = Nothing
... | true | [ eq ] = Found (record { heads = [] ; el = x ; tails = ls ; is-ls = refl }) eq

⊆++ : {a : Level} {A : Set a} (xs ys zs : List A) → xs ⊆ zs → ys ⊆ zs → (xs ++ ys) ⊆ zs
⊆++ _ ys zs [] q = q
⊆++ _ ys zs (x₁ ∷ p) q = x₁ ∷ (⊆++ _ ys zs p q)

∈-insert : ∀ {a} {A : Set a} (xs ys : List A) → (x : A) → x ∈ (ys ++ x ∷ xs)
∈-insert xs [] x = Z
∈-insert xs (x₁ ∷ ys) x = S (∈-insert xs ys x)

-- count down both the proof and the list
-- Result depends on which is shortest
insert-one : ∀ {a} {A : Set a} {x₁ : A} (xs ys : List A) → (y : A) → x₁ ∈ (xs ++ ys) → x₁ ∈ (xs ++ y ∷ ys)
insert-one [] ys y p = S p
insert-one (x ∷ xs) ys y Z = Z
insert-one (x ∷ xs) ys y (S p) = S (insert-one xs ys y p)

⊆-insert : ∀ {a} {A : Set a} (xs ys zs : List A) → (x : A) → xs ⊆ (ys ++ zs) → xs ⊆ (ys ++ x ∷ zs)
⊆-insert [] ys zs x p = []
⊆-insert (x₁ ∷ xs) ys zs x (x₂ ∷ p) = insert-one ys zs x x₂ ∷ (⊆-insert xs ys zs x p)

⊆-move : {a : Level} {A : Set a} (xs ys : List A) → (xs ++ ys) ⊆ (ys ++ xs)
⊆-move [] ys rewrite (++-identityʳ ys) = ⊆-refl
⊆-move (x ∷ xs) ys with (⊆-move xs ys)
... | q = ∈-insert xs ys x ∷ ⊆-insert (xs ++ ys) ys xs x q

⊆-skip : {a : Level} {A : Set a} (xs ys zs : List A) → ys ⊆ zs → (xs ++ ys) ⊆ (xs ++ zs)
⊆-skip [] ys zs p = p
⊆-skip (x ∷ xs) ys zs p = Z ∷ (⊆-suc (⊆-skip xs ys zs p))

⊆++-l-refl : ∀ {a} {A : Set a} → (xs ys : List A) → xs ⊆ (ys ++ xs)
⊆++-l-refl xs [] = ⊆-refl
⊆++-l-refl xs (x ∷ ys) = ⊆-suc (⊆++-l-refl xs ys)

∈-inc : ∀ {a} {A : Set a} (xs ys : List A) → (x : A) → x ∈ xs → (x ∈ (xs ++ ys))
∈-inc _ ys x Z = Z
∈-inc _ ys x (S p) = S (∈-inc _ ys x p)

⊆-inc : ∀ {a} {A : Set a} (xs ys zs : List A) → xs ⊆ ys → (xs ++ zs) ⊆ (ys ++ zs)
⊆-inc [] [] zs p = ⊆-refl
⊆-inc [] (x ∷ ys) zs p = ⊆++-l-refl zs (x ∷ ys)
⊆-inc (x ∷ xs) ys zs (px ∷ p) = ∈-inc ys zs x px ∷ (⊆-inc xs ys zs p)

⊆++comm : ∀ {a} {A : Set a} (xs ys zs : List A) → ((xs ++ ys) ++ zs) ⊆ (xs ++ (ys ++ zs))
⊆++comm [] ys zs = ⊆-refl
⊆++comm (x ∷ xs) ys zs = Z ∷ (⊆-suc (⊆++comm xs ys zs))

⊆++comm' : ∀ {a} {A : Set a} (xs ys zs : List A) → (xs ++ ys ++ zs) ⊆ ((xs ++ ys) ++ zs)
⊆++comm' [] ys zs = ⊆-refl
⊆++comm' (x ∷ xs) ys zs = Z ∷ ⊆-suc (⊆++comm' xs ys zs)

add-references++ : ∀ {IS} → (xs ys : ReferenceTypes) → (x : Message IS) → add-references (xs ++ ys) x ≡ add-references xs x ++ ys
add-references++ xs ys (Msg {MT} x x₁) = sym (++-assoc (extract-references MT) xs ys)

waiting-refs++ : ∀ {IS} → (xs ys : List (Message IS)) → waiting-refs (xs ++ ys) ≡ waiting-refs xs ++ waiting-refs ys
waiting-refs++ [] _ = refl
waiting-refs++ (x ∷ xs) ys with (waiting-refs++ xs ys)
... | q with (cong (λ qs → add-references qs x) q)
... | r = trans r (halp xs ys x)
  where
    halp : ∀ {IS} → (xs ys : List (Message IS)) (x : Message IS) →
      add-references (waiting-refs xs ++ waiting-refs ys) x ≡
      add-references (waiting-refs xs) x ++ waiting-refs ys
    halp xs ys x = add-references++ (waiting-refs xs) (waiting-refs ys) x

move-received : ∀ {IS} → ∀ pre → (q : List (Message IS)) → (x : Message IS) → ((pre ++ (waiting-refs (x ∷ q))) ⊆ (add-references (pre ++ waiting-refs q) x))
move-received pre q (Msg {MT} x x₁) = ⊆-trans move-2 (⊆-trans (⊆-inc (pre ++ extract-references MT) (extract-references MT ++ pre) (waiting-refs q) (⊆-move pre (extract-references MT))) move-3)
  where
    move-1 : (pre ++ extract-references MT) ⊆ (extract-references MT ++ pre)
    move-1 = ⊆-move pre (extract-references MT)
    move-2 : (pre ++ extract-references MT ++ waiting-refs q) ⊆ ((pre ++ extract-references MT) ++ waiting-refs q)
    move-2 = ⊆++comm' pre (extract-references MT) (waiting-refs q)
    move-3 : ((extract-references MT ++ pre) ++ waiting-refs q) ⊆ (extract-references MT ++ pre ++ waiting-refs q)
    move-3 = ⊆++comm (extract-references MT) pre (waiting-refs q)

accept-received : ∀ {IS} → ∀ pre → (q : List (Message IS)) → (x : Message IS) →  (add-references pre x ++ waiting-refs q) ⊆ (add-references (pre ++ waiting-refs q) x)
accept-received pre q (Msg {MT} x x₁) = ⊆++comm (extract-references MT) pre (waiting-refs q)

open SplitList


accept-found : ∀ {IS} → ∀ pre → (q : List (Message IS)) → (split : SplitList q) →
               (add-references pre (el split) ++ waiting-refs (heads split ++ tails split)) ⊆ (pre ++ waiting-refs q)
accept-found pre q record { heads = heads ; el = Msg {MT} x y ; tails = tails ; is-ls = is-ls } rewrite (sym is-ls) =
  ⊆-trans (⊆-inc (extract-references MT ++ pre) (pre ++ extract-references MT) (waiting-refs (heads ++ tails)) (⊆-move (extract-references MT) pre))
  (⊆-trans (⊆++comm pre (extract-references MT) (waiting-refs (heads ++ tails)))
  (⊆-skip pre (extract-references MT ++ waiting-refs (heads ++ tails)) (waiting-refs (heads ++ Msg x y ∷ tails))
  haj))
  where
    haj : (extract-references MT ++ waiting-refs (heads ++ tails)) ⊆ waiting-refs (heads ++ Msg x y ∷ tails)
    haj rewrite (waiting-refs++ heads tails) | (waiting-refs++ heads (Msg x y ∷ tails)) = ⊆-trans (⊆++comm' (extract-references MT) (waiting-refs heads) (waiting-refs tails))
      (⊆-trans (⊆-inc (extract-references MT ++ waiting-refs heads) (waiting-refs heads ++ extract-references MT) (waiting-refs tails)
        (⊆-move (extract-references MT) (waiting-refs heads)))
      (⊆++comm (waiting-refs heads) (extract-references MT) (waiting-refs tails)))

-- TODO: move-received should add at the end!
selective-receive : ∀ {IS pre} → (q : List (Message IS)) → (f : Message IS → Bool) → ActorM IS (SelRec IS f) (pre ++ (waiting-refs q)) (λ m → (add-references pre (msg m)) ++ (waiting-refs (waiting m)))
selective-receive {IS} {pre} q f = case-of-find (find-split q f)
  where
    case-of-find : FoundInList q f → ActorM IS (SelRec IS f) (pre ++ waiting-refs q) (λ m → add-references pre (msg m) ++ waiting-refs (waiting m))
    case-of-find (Found split x) = ALift (accept-found pre q split) (return₁ (record { msg = el split ; right-msg = x ; waiting = (heads split) ++ (tails split) }))
    case-of-find Nothing = receive >>= handle-receive
      where
        handle-receive : (x : Message IS) → ∞ (ActorM IS (SelRec IS f) (add-references (pre ++ waiting-refs q) x) (λ m → (add-references pre (msg m) ++ waiting-refs (waiting m))))
        handle-receive x with (f x) | (inspect f x)
        handle-receive x | false | p = ♯ ALift (move-received pre q x) (♯ selective-receive (x ∷ q) f)
        handle-receive x | true | [ p ] = ♯ ALift (accept-received pre q x) (return₁ ret-v)
          where
            ret-v : SelRec IS f
            ret-v = record { msg = x ; right-msg = p ; waiting = q }

TestBox : InboxShape
TestBox = (ValueType Bool ∷ []) ∷ []

testActor : ActorM TestBox (Lift Bool) [] (λ _ → [])
testActor = _>>=_ {TestBox} {SelRec TestBox only-true} {Lift Bool} {[]} {λ m → add-references [] (msg m) ++ waiting-refs (waiting m)} (♯ selective-receive [] only-true) after-receive
  where
    only-true : Message TestBox → Bool
    only-true (Msg Z (b ∷ [])) = b
    only-true (Msg (S ()) x₁)
    after-receive : (x : SelRec TestBox only-true) → ∞ (ActorM TestBox (Lift Bool) (add-references [] (msg x) ++ waiting-refs (waiting x)) (λ _ → []))
    after-receive record { msg = (Msg Z (.true ∷ [])) ; right-msg = refl ; waiting = waiting } = ♯ ALift [] (return true)
    after-receive record { msg = (Msg (S ()) x₁) ; right-msg = right-msg ; waiting = waiting }

spawner : ActorM [] ⊤₁ [] (λ _ → [])
spawner = spawn testActor >>= λ _ → ♯ ((Z ![t: Z ] ((lift false) ∷ [])) >>= λ _ → ♯ ALift [] (return _))
