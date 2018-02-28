module Examples.InfiniteBind where

open import ActorMonad public
open import Data.List using (List ; _∷_ ; [])
open import Coinduction
open import Level using (Lift ; lift) renaming (zero to lzero ; suc to lsuc)
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership using (_∈_ ; _⊆_ ; S ; Z ; InList ; SubNil ; xs⊆xs)
open import Data.Unit using (⊤ ; tt)

open InboxShape

Box : InboxShape
Box = record { value-types = [] ; reference-types = [] }

binder : ActorM Box ⊤₁ [] (λ _ → [])
binder = ♯ binder >>= λ _ → ♯ binder

