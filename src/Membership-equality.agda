module Membership-equality where

import Membership
open import Relation.Binary.PropositionalEquality as PropEq
open import Data.List
open import Data.List.Any
open import Relation.Binary
import Relation.Binary.InducedPreorders as Ind
open import Function.Related as Related hiding (_∼[_]_)

private
  open module M {a} {A : Set a} = Membership (PropEq.setoid A) public
    hiding (lift-resp; lose; ⊆-preorder; module ⊆-Reasoning)

lose : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} →
         x M.∈ xs → P x → Any P xs
lose {P = P} = M.lose (PropEq.subst P)

-- _⊆_ is a preorder.

⊆-preorder : ∀ {a} → Set a → Preorder _ _ _
⊆-preorder A = Ind.InducedPreorder₂ (PropEq.setoid (List A)) _∈_
                                      (PropEq.subst (_∈_ _))

  -- Set and bag equality and related preorders.

open Related public
  using (Kind; Symmetric-kind)
  renaming ( implication         to subset
           ; reverse-implication to superset
           ; equivalence         to set
           ; injection           to subbag
           ; reverse-injection   to superbag
           ; bijection           to bag
           )

[_]-Order : Kind → ∀ {a} → Set a → Preorder _ _ _
[ k ]-Order A = Related.InducedPreorder₂ k (_∈_ {A = A})

[_]-Equality : Symmetric-kind → ∀ {a} → Set a → Setoid _ _
[ k ]-Equality A = Related.InducedEquivalence₂ k (_∈_ {A = A})

infix 4 _∼[_]_

_∼[_]_ : ∀ {a} {A : Set a} → List A → Kind → List A → Set _
_∼[_]_ {A = A} xs k ys = Preorder._∼_ ([ k ]-Order A) xs ys

-- Bag equality implies the other relations.

bag-=⇒ : ∀ {k a} {A : Set a} {xs ys : List A} →
         xs ∼[ bag ] ys → xs ∼[ k ] ys
bag-=⇒ xs≈ys = ↔⇒ xs≈ys
