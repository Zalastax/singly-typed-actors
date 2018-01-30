module FileIOEffect where

open import Effect
import IO.Primitive as IO
open import Data.String using (String)
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Unit using (⊤ ; tt)
open import Category.Monad using (RawMonad)
open import Level using (zero)
open import Data.List using (_∷_ ; [])
open import Data.List.All using (All ; lookup ; _∷_ ; [])
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership-≡ using (_∈_)

data FileIOState : Set where
  opened closed : FileIOState

data FileIOEff : Effect FileIOState where
  `openFile  : String → FileIOEff Bool closed (λ ok → if ok then opened else closed)
  `closeFile : FileIOEff ⊤ opened (λ _ → closed)

FileIO : EFFECT
FileIO = mkEff FileIOState FileIOEff

IOMonad : RawMonad IO.IO
IOMonad = record { return = IO.return ; _>>=_ = IO._>>=_ {zero} {zero}}

openFile : ∀ {M Es i} (mem : FileIO ∈ Es) → lookup i mem ≡ closed → String →
           ⟨ M ⟩Eff Es [ ok ∶ Bool ] i ==> set i mem (if ok then opened else closed)
openFile mem prf file = effect mem prf (`openFile file)

closeFile : ∀ {M Es i} (mem : FileIO ∈ Es) → lookup i mem ≡ opened →
            ⟨ M ⟩Eff Es [ _ ∶ ⊤ ] i ==> set i mem closed
closeFile mem prf = effect mem prf `closeFile

openAndClose : ∀ {M} → String → ⟨ M ⟩Eff (FileIO ∷ []) [ _ ∶ ⊤ ] (closed ∷ []) ==> (closed ∷ [])
openAndClose file =
  openFile (here refl) refl file >>= λ
  { true  → closeFile (here refl) refl
  ; false → return _
  }

main : IO.IO ⊤
main = run IOMonad evalers (openAndClose ".gitignore")
  where
    fileEval : Evaluator IO.IO FileIO
    fileEval (`openFile x) = IO.return false -- Let's not open any files ever, since we can't catch exceptions
    fileEval `closeFile = IO.return tt
    evalers : All (Evaluator IO.IO) (FileIO ∷ [])
    evalers = fileEval ∷ []
