module Prelude where

-- Simple data
open import Data.Bool public
  using (Bool ; false ; true)
open import Data.Empty public
  using (⊥ ; ⊥-elim)
open import Data.Nat public
  using (
  ℕ ; zero ; suc
  ; _+_ ; _*_
  ; _≤_ ; z≤n ; s≤s
  ; _<_ ; _≟_ ; pred
  )
open import Data.Maybe public
  using (Maybe ; just ; nothing)
open import Data.Unit public
  using (⊤ ; tt)
open import Data.String public
  using (String)
  renaming (_++_ to _||_)

-- List-like modules

open import Data.List public
  using (
    List ; [] ; _∷_
    ; _++_ ; map ; drop
    ; reverse ; _∷ʳ_ ; length
    )
open import Data.List.All public
  using (All ; [] ; _∷_ ; lookup)
  renaming (map to ∀map)
open import Membership public
  using (
  _∈_ ; S ; Z
  ; _⊆_ ; _∷_ ; []
  ; ⊆-refl ; ⊆-suc ; find-∈
  ; lookup-parallel ; lookup-parallel-≡ ; translate-∈
  ; translate-⊆ ; ⊆-trans ; All-⊆
  ; ⊆++-l-refl ; lookup-all
  ; ∈-inc ; ⊆++-refl ; ⊆++comm'
  ; ⊆++comm ; ⊆-move ; ⊆-inc
  ; ⊆-skip
  )
open import Data.List.Any public
  using (Any ; here ; there)

open import Singleton public
  using ([_]ˡ ; [_]ᵃ ; [_]ᵐ)

-- Propositions and properties
open import Relation.Binary.PropositionalEquality public
  using (
    _≡_ ; refl ; sym
    ; cong ; cong₂ ; trans
    ; inspect ; [_]
    )
open import Relation.Nullary public
  using (Dec ; yes ; no ; ¬_)
open import Relation.Nullary.Decidable public
  using (⌊_⌋)

-- Other
open import Level public
  using    (Level; _⊔_ ; Lift ; lift)
  renaming (zero to lzero; suc to lsuc)
open import Size public
  using (Size ; Size<_ ; ↑_ ; ∞)
