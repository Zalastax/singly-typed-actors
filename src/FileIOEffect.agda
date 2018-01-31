module FileIOEffect where

open import Effect
import IO.Primitive as IO
open import Data.String using (String)
open import Data.Bool using (Bool ; if_then_else_ ; false ; true)
open import Data.Unit using (⊤ ; tt)
open import Category.Monad using (RawMonad)
open import Level using (zero)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.All using (All ; lookup ; _∷_ ; [])
open import Data.List.Any using (here ; there)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Membership-≡ using (_∈_)
open import Data.Product using (Σ ; _,_ ; _×_)

data FileIOState : Set where
  opened closed : FileIOState

data FileHandle : Set where
  FH : String → FileHandle

data FileIOEff : Effect zero where
  `openFile  : String → FileIOEff Bool ⊤ λ ok → if ok then FileHandle else ⊤
  `closeFile : FileIOEff ⊤ FileHandle λ h → ⊤

-- Should we really use this now?
FileIO : EFFECT zero
FileIO = mkEff ⊤ FileIOEff

IOMonad : RawMonad IO.IO
IOMonad = record { return = IO.return ; _>>=_ = IO._>>=_ {zero} {zero}}

myOpClose : ∀ {m} → String → EffM m ⊤ (FileIO ∷ []) λ _ → (FileIO ∷ [])
myOpClose file = effect (here refl) (`openFile file) >>= λ
  { true → effect (here refl) `closeFile
  ; false → return tt}

main : IO.IO ⊤
main = run IO.IO (record { return = IO.return ; _>>=_ = IO._>>=_ }) (myOpClose ".gitignore") myEnv
  where
    FileIOHandler : Handler IO.IO FileIOEff
    FileIOHandler v (`openFile x) k = k true (FH x)
    FileIOHandler (FH x) `closeFile k = k tt tt
    myEnv : Env IO.IO (FileIO ∷ [])
    myEnv = (FileIOHandler , tt) ∷ []
