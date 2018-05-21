module Selective.Examples.Bookstore where

open import Selective.ActorMonad
open import Selective.Libraries.Call using (UniqueTag ; call)
open import Prelude

open import Data.Nat
  using ( _≟_ ; pred ; ⌈_/2⌉ ; _≤?_ ; _∸_ ; _≤_ ; z≤n ; s≤s ; _<_ ; _≰_  )
open import Data.Nat.Properties
  using (≤-antisym ; ≰⇒>)
open import Data.Nat.Show
  using (show)
open import Data.String
  using (primStringEquality)

open import Debug

BookTitle = String
Money = ℕ

data BuyerRole : Set where
  Buyer1 Buyer2 : BuyerRole

record Book : Set where
  field
    title : BookTitle
    price : Money

-- ===========
--  GET QUOTE
-- ===========

GetQuoteReply : MessageType
GetQuoteReply = ValueType UniqueTag ∷ [ ValueType (Maybe Book) ]ˡ

GetQuoteReplyInterface : InboxShape
GetQuoteReplyInterface = [ GetQuoteReply ]ˡ

GetQuote : MessageType
GetQuote = ValueType UniqueTag ∷ ReferenceType GetQuoteReplyInterface ∷ [ ValueType BookTitle ]ˡ

-- ======================
--  PROPOSE CONTRIBUTION
-- ======================

record Contribution : Set where
  field
    book : Book
    money : Money

ContributionMessage : MessageType
ContributionMessage = [ ValueType Contribution ]ˡ

-- ===============
--  AGREE OR QUIT
-- ===============

data AgreeChoice : Set where
  AGREE QUIT : AgreeChoice

AgreeDecision : MessageType
AgreeDecision = [ ValueType AgreeChoice ]ˡ

-- ================
--  TRANSFER MONEY
-- ================

Transfer : MessageType
Transfer = ValueType BuyerRole ∷  [ ValueType Contribution ]ˡ

-- ============
--  INTERFACES
-- ============

Buyer1-to-Seller : InboxShape
Buyer1-to-Seller = GetQuote ∷ [ Transfer ]ˡ

Buyer2-to-Seller : InboxShape
Buyer2-to-Seller = AgreeDecision ∷ [ Transfer ]ˡ

Buyer1-to-Buyer2 : InboxShape
Buyer1-to-Buyer2 = [ ContributionMessage ]ˡ

Buyer2-to-Buyer1 : InboxShape
Buyer2-to-Buyer1 = [ AgreeDecision ]ˡ

SellerInterface : InboxShape
SellerInterface = GetQuote ∷ AgreeDecision ∷ [ Transfer ]ˡ

Buyer1Interface : InboxShape
Buyer1Interface = [ ReferenceType Buyer1-to-Seller ]ˡ ∷  [ ReferenceType Buyer1-to-Buyer2 ]ˡ ∷ GetQuoteReply ∷ [ AgreeDecision ]ˡ

Buyer2Interface : InboxShape
Buyer2Interface = [ ReferenceType Buyer2-to-Seller ]ˡ ∷ [ ReferenceType Buyer2-to-Buyer1 ]ˡ ∷ [ ContributionMessage ]ˡ

-- ========
--  COMMON
-- ========

book1 : BookTitle
book1 = "Crime and Punishment"

transfer-money : ∀ {i IS Seller Γ} →
                 Γ ⊢ Seller →
                 [ Transfer ]ˡ <: Seller →
                 BuyerRole →
                 Book →
                 Money →
                 ∞ActorM i IS ⊤₁ Γ (λ _ → Γ)
transfer-money p sub role book money = p ![t: translate-⊆ sub Z ] ((lift role) ∷ [ lift record { book = book ; money = money } ]ᵃ)

-- ========
--  SELLER
-- ========

same-buyer-role : BuyerRole → BuyerRole → Bool
same-buyer-role Buyer1 Buyer1 = true
same-buyer-role Buyer1 Buyer2 = false
same-buyer-role Buyer2 Buyer1 = false
same-buyer-role Buyer2 Buyer2 = true

data TransactionStatus (book : Book) (c1 c2 : Contribution) : Set where
  TooLittleMoney : (Contribution.money c1 + Contribution.money c2) < (Book.price book) → TransactionStatus book c1 c2
  Accepted : (Contribution.money c1 + Contribution.money c2) ≡ (Book.price book) → TransactionStatus book c1 c2
  TooMuchMoney : (Book.price book) < (Contribution.money c1 + Contribution.money c2) → TransactionStatus book c1 c2

transaction-status? : ∀ book c1 c2 → TransactionStatus book c1 c2
transaction-status? book c1 c2 with (Contribution.money c1 + Contribution.money c2 ≤? Book.price book) | (Book.price book ≤? Contribution.money c1 + Contribution.money c2)
transaction-status? book c1 c2 | yes p | yes q = Accepted (≤-antisym p q)
transaction-status? book c1 c2 | yes p | no ¬p = TooLittleMoney (≰⇒> ¬p)
transaction-status? book c1 c2 | no ¬p | q = TooMuchMoney (≰⇒> ¬p)

seller : ∀ {i} → ActorM i SellerInterface ⊤₁ [] (λ _ → [])
seller = begin do
    record {msg = Msg Z (tag ∷ _ ∷ title ∷ []) } ← selective-receive select-quote
      where
        record { msg = (Msg (S _) _) ; msg-ok = () }
    let maybe-book = find-book known-books title
    (Z ![t: Z ] (lift tag ∷ [ lift maybe-book ]ᵃ))
    after-book-quote maybe-book
  where
    select-quote : MessageFilter SellerInterface
    select-quote (Msg Z _) = true
    select-quote _ = false
    known-books : List Book
    known-books = [ record { title = book1 ; price = 37 } ]ˡ
    find-book : List Book → BookTitle → Maybe Book
    find-book [] title = nothing
    find-book (book ∷ books) title with (primStringEquality (Book.title book) title)
    ... | true = just book
    ... | false = find-book books title
    select-decision : MessageFilter SellerInterface
    select-decision (Msg (S Z) _) = true
    select-decision _ = false
    wait-for-decision : ∀ {i Γ} →
                        ∞ActorM i SellerInterface (Lift AgreeChoice) Γ (λ _ → Γ)
    wait-for-decision = do
      record { msg = Msg (S Z) (ac ∷ []) } ← (selective-receive select-decision)
        where
          record { msg = (Msg Z _) ; msg-ok = () }
          record { msg = (Msg (S (S _)) _) ; msg-ok = () }
      return ac
    select-contribution-from : BuyerRole → MessageFilter SellerInterface
    select-contribution-from br (Msg (S (S Z)) (br' ∷ _)) = same-buyer-role br br'
    select-contribution-from _ _ = false
    wait-for-money-from : ∀ {i Γ} →
                          BuyerRole →
                          ∞ActorM i SellerInterface (Lift Contribution) Γ (λ _ → Γ)
    wait-for-money-from br = do
      record { msg = Msg (S (S Z)) (_ ∷ contribution ∷ []) } ← (selective-receive (select-contribution-from br))
        where
          record { msg = (Msg Z _) ; msg-ok = () }
          record { msg = (Msg (S Z) _) ; msg-ok = () }
          record { msg = (Msg (S (S (S _))) _) ; msg-ok = () }
      return contribution
    transaction-message : Book → Contribution → Contribution → String
    transaction-message book c1 c2 with (transaction-status? book c1 c2)
    ... | Accepted _ = "Accepted purchase of " || Book.title book || " for $" || show (Book.price book)
    ... | TooLittleMoney p = "Received too little money for " || Book.title book || ". $" || show (Book.price book) || " - $" || show (Contribution.money c1) || " - $" || show (Contribution.money c2) || " = $" || show (Book.price book ∸ Contribution.money c1 ∸ Contribution.money c2)
    ... | TooMuchMoney p = "Received too much money for " || Book.title book || ". $" || show (Book.price book) || " - $" || show (Contribution.money c1) || " - $" || show (Contribution.money c2) || " = -$" || show ((Contribution.money c1 + Contribution.money c2) ∸ Book.price book)
    after-book-quote : ∀ {i} →
                       Maybe Book →
                       ∞ActorM i SellerInterface ⊤₁ [ GetQuoteReplyInterface ]ˡ (λ _ → [])
    after-book-quote (just book) = do
      lift AGREE ← wait-for-decision
        where
          lift QUIT → debug "seller sees that transaction was quit" (strengthen [])
      lift contrib1 ← wait-for-money-from Buyer1
      lift contrib2 ← wait-for-money-from Buyer2
      debug (transaction-message book contrib1 contrib2) (strengthen [])
    after-book-quote nothing = strengthen []

-- =========
--  BUYER 1
-- =========

buyer1 : ∀ {i} → ActorM i Buyer1Interface ⊤₁ [] (λ _ → [])
buyer1 = begin do
    wait-for-seller
    lift (just book) ← get-quote Z 0 book1
      where
        (lift nothing) → strengthen []
    wait-for-buyer2
    let my-contribution = ⌈ Book.price book /2⌉
    send-contribution Z book my-contribution
    lift AGREE ← wait-for-decision
      where
        lift QUIT → debug "buyer1 sees that transaction was quit" (strengthen [])
    (transfer-money (S Z) (⊆-suc ⊆-refl) Buyer1 book my-contribution)
    (strengthen [])
  where
    select-seller : MessageFilter Buyer1Interface
    select-seller (Msg Z _) = true
    select-seller (Msg (S _) _) = false
    wait-for-seller : ∀ {i Γ} → ∞ActorM i Buyer1Interface ⊤₁ Γ (λ _ → Buyer1-to-Seller ∷ Γ)
    wait-for-seller = do
      record { msg = Msg Z _ } ← (selective-receive select-seller)
        where
          record { msg = (Msg (S _) _) ; msg-ok = () }
      return _
    select-buyer2 : MessageFilter Buyer1Interface
    select-buyer2 (Msg (S Z) _) = true
    select-buyer2 _ = false
    wait-for-buyer2 : ∀ {i Γ} → ∞ActorM i Buyer1Interface ⊤₁ Γ (λ _ → Buyer1-to-Buyer2 ∷ Γ)
    wait-for-buyer2 = do
      record {msg = Msg (S Z) _ } ← selective-receive select-buyer2
        where
          record { msg = (Msg Z _) ; msg-ok = () }
          record { msg = (Msg (S (S _)) _) ; msg-ok = () }
      return _
    get-quote : ∀ {i Γ} →
               Γ ⊢ Buyer1-to-Seller →
               UniqueTag →
               BookTitle →
               ∞ActorM i Buyer1Interface (Lift (Maybe Book)) Γ (λ _ → Γ)
    get-quote p tag title = do
      record { msg = Msg (S (S Z)) (_ ∷ book ∷ []) ; msg-ok = msg-ok } ← call p Z tag [ lift title ]ᵃ [ S (S Z) ]ᵐ Z
        where
          record { msg = (Msg Z (_ ∷ _)) ; msg-ok = () }
          record { msg = (Msg (S Z) (_ ∷ _)) ; msg-ok = () }
          record { msg = (Msg (S (S (S Z))) _) ; msg-ok = () }
          record { msg = (Msg (S (S (S (S _)))) _) ; msg-ok = () }
      return book
    send-contribution : ∀ {i Γ} →
                       Γ ⊢ Buyer1-to-Buyer2 →
                       Book →
                       Money →
                       ∞ActorM i Buyer1Interface ⊤₁ Γ (λ _ → Γ)
    send-contribution p book money = p ![t: Z ] [ lift record { book = book ; money = money } ]ᵃ
    select-decision : MessageFilter Buyer1Interface
    select-decision (Msg (S (S (S Z))) _) = true
    select-decision _ = false
    wait-for-decision : ∀ {i Γ} →
                        ∞ActorM i Buyer1Interface (Lift AgreeChoice) Γ (λ _ → Γ)
    wait-for-decision = do
      record {msg = Msg (S (S (S Z))) (ac ∷ []) } ← (selective-receive select-decision)
        where
          record { msg = (Msg Z _) ; msg-ok = () }
          record { msg = (Msg (S Z) _) ; msg-ok = () }
          record { msg = (Msg (S (S Z)) _) ; msg-ok = () }
          record { msg = (Msg (S (S (S (S _)))) _) ; msg-ok = () }
      return ac


-- =========
--  BUYER 2
-- =========

buyer2 : ∀ {i} → ActorM i Buyer2Interface ⊤₁ [] (λ _ → [])
buyer2 = begin do
    wait-for-seller
    wait-for-buyer1
    lift contribution ← wait-for-contribution
    handle-contribution (S Z) Z contribution
    strengthen []
  where
    select-seller : MessageFilter Buyer2Interface
    select-seller (Msg Z _) = true
    select-seller (Msg (S _) _) = false
    wait-for-seller : ∀ {i Γ} → ∞ActorM i Buyer2Interface ⊤₁ Γ (λ _ → Buyer2-to-Seller ∷ Γ)
    wait-for-seller = do
      record { msg = Msg Z _ } ← (selective-receive select-seller)
        where
          record { msg = (Msg (S _) _) ; msg-ok = () }
      return _
    select-buyer1 : MessageFilter Buyer2Interface
    select-buyer1 (Msg (S Z) _) = true
    select-buyer1 _ = false
    wait-for-buyer1 : ∀ {i Γ} → ∞ActorM i Buyer2Interface ⊤₁ Γ (λ _ → Buyer2-to-Buyer1 ∷ Γ)
    wait-for-buyer1 = do
      record {msg = Msg (S Z) _ } ← selective-receive select-buyer1
        where
          record { msg = (Msg Z _) ; msg-ok = () }
          record { msg = (Msg (S (S _)) _) ; msg-ok = () }
      return _
    select-contribution : MessageFilter Buyer2Interface
    select-contribution (Msg (S (S Z)) _) = true
    select-contribution _ = false
    wait-for-contribution : ∀ {i Γ} → ∞ActorM i Buyer2Interface (Lift Contribution) Γ (λ _ → Γ)
    wait-for-contribution = do
      record { msg = Msg (S (S Z)) (cc ∷ []) } ← (selective-receive select-contribution)
        where
          record { msg = (Msg Z _) ; msg-ok = () }
          record { msg = (Msg (S Z) _) ; msg-ok = () }
          record { msg = (Msg (S (S (S _))) _) ; msg-ok = () }
      return cc
    contribution-is-fair : Money → Money → Bool
    contribution-is-fair price money = ⌊ price ∸ money ≤? money ⌋
    handle-contribution : ∀ {i Γ} →
                          Γ ⊢ Buyer2-to-Seller →
                          Γ ⊢ Buyer2-to-Buyer1 →
                          Contribution →
                          ∞ActorM i Buyer2Interface ⊤₁ Γ (λ _ → Γ)
    handle-contribution seller buyer1 record { book = book ; money = money } with (contribution-is-fair (Book.price book) money)
    ... | true = do
      buyer1 ![t: Z ] [ lift AGREE ]ᵃ
      seller ![t: Z ] [ lift AGREE ]ᵃ
      transfer-money seller (⊆-suc ⊆-refl) Buyer2 book ((Book.price book) ∸ money)
    ... | false = do
      buyer1 ![t: Z ] [ lift QUIT ]ᵃ
      seller ![t: Z ] [ lift QUIT ]ᵃ

-- ============
--  SUPERVISOR
-- ============

bookstore-supervisor : ∀ {i} → ∞ActorM i [] ⊤₁ [] (λ _ → [])
bookstore-supervisor = do
  spawn seller
  spawn buyer1
  spawn buyer2
  Z ![t: Z ]  [ [ (S (S Z)) ]>: ( S Z ∷ [ S (S Z) ]ᵐ)]ᵃ
  Z ![t: S Z ] [ [ S Z ]>: [ S (S (S Z)) ]ᵐ ]ᵃ
  (S Z) ![t: Z ] [ [ S (S Z) ]>: (Z ∷ [ S (S Z) ]ᵐ) ]ᵃ
  (S Z) ![t: S Z ] [ [ Z ]>: [ S (S Z) ]ᵐ ]ᵃ
  (strengthen [])

