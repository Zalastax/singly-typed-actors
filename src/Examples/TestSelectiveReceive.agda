module Examples.TestSelectiveReceive where

open import Prelude
open import Libraries.SelectiveReceive

open SelRec

BoolMessage = [ ValueType Bool ]ˡ
SelectiveTestBox : InboxShape
SelectiveTestBox = [ BoolMessage ]ˡ

testActor : ∀ {i} → ActorM i SelectiveTestBox (Lift Bool) [] (λ _ → [])
testActor = selective-receive [] only-true ∞>>= after-receive
  where
    only-true : Message SelectiveTestBox → Bool
    only-true (Msg Z (b ∷ [])) = b
    only-true (Msg (S ()) x₁)
    after-receive : ∀ {i}
                    (x : SelRec SelectiveTestBox only-true) →
                    ∞ActorM i SelectiveTestBox (Lift Bool)
                      (add-references [] (msg x) ++ waiting-refs (waiting x))
                      (λ _ → [])
    after-receive record { msg = (Msg Z (.true ∷ [])) ; msg-ok = refl } =
      strengthen [] >>
      return true
    after-receive record { msg = (Msg (S ()) _) }

spawner : ∀ {i} → ActorM i [] ⊤₁ [] (λ _ → [])
spawner = begin do
  spawn testActor
  Z ![t: Z ] [ lift true ]ᵃ
  strengthen []
