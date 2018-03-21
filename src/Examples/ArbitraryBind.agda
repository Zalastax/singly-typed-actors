module Examples.ArbitraryBind where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [])
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)

open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; _∷_ ; [] ; ⊆-refl)

ArbitraryBox : InboxShape
ArbitraryBox = []

ifSelf : (Lift {lzero} {lsuc lzero} Bool) → TypingContext
ifSelf (lift false) = []
ifSelf (lift true) = ArbitraryBox ∷ []

arbitraryActor : ∀{i} → Bool → ∞ActorM i ArbitraryBox (Lift Bool) [] ifSelf
arbitraryActor false = return false >>= return₁
arbitraryActor true  = self >>= λ _ → return true
