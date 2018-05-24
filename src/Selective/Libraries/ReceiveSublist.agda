module Selective.Libraries.ReceiveSublist where

open import Selective.ActorMonad public
open import Prelude

accept-sublist-unwrapped : (xs ys zs : InboxShape) → ∀{MT} → MT ∈ (xs ++ ys ++ zs) → Bool
accept-sublist-unwrapped [] [] zs p = false
accept-sublist-unwrapped [] (y ∷ ys) zs Z = true
accept-sublist-unwrapped [] (y ∷ ys) zs (S p) = accept-sublist-unwrapped [] ys zs p
accept-sublist-unwrapped (x ∷ xs) ys zs Z = false
accept-sublist-unwrapped (x ∷ xs) ys zs (S p) = accept-sublist-unwrapped xs ys zs p


accept-sublist : (xs ys zs : InboxShape) → MessageFilter (xs ++ ys ++ zs)
accept-sublist xs ys zs (Msg received-message-type received-fields) = accept-sublist-unwrapped xs ys zs received-message-type

record AcceptSublistDependent (IS : InboxShape) (accepted-type : MessageType) : Set₁ where
  field
    accepted-which : accepted-type ∈ IS
    fields : All receive-field-content accepted-type

receive-sublist : {i : Size} →
                  {Γ : TypingContext} →
                  (xs ys zs : InboxShape) →
                  ∞ActorM i (xs ++ ys ++ zs)
                            (Message ys)
                            Γ
                            (add-references Γ)
receive-sublist xs ys zs = do
    record { msg = Msg {MT} p f ; msg-ok = msg-ok } ← selective-receive (accept-sublist xs ys zs)
    let record {accepted-which = aw ; fields = fields } = rewrap-message xs ys zs p f msg-ok
    return₁ (Msg {MT = MT} aw fields)
  where
    rewrap-message : ∀{MT} →
                     (xs ys zs : InboxShape) →
                     (p : MT ∈ (xs ++ ys ++ zs)) →
                     All receive-field-content MT →
                     (accept-sublist-unwrapped xs ys zs p) ≡ true →
                     AcceptSublistDependent ys MT
    rewrap-message [] [] zs p f ()
    rewrap-message [] (x ∷ ys) zs Z f q = record { accepted-which = Z ; fields = f }
    rewrap-message [] (x ∷ ys) zs (S p) f q =
      let
        rec = rewrap-message [] ys zs p f q
        open AcceptSublistDependent
      in record { accepted-which = S (rec .accepted-which) ; fields = rec .fields }
    rewrap-message (x ∷ xs) ys zs Z f ()
    rewrap-message (x ∷ xs) ys zs (S p) f q = rewrap-message xs ys zs p f q
