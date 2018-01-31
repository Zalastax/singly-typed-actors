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
  `openFile  : String → FileIOEff Bool ⊤ λ ok → if ok then FileHandle else ⊤ -- FileIOEff Bool ? -- closed (λ ok → if ok then opened else closed)
  `closeFile : FileIOEff ⊤ FileHandle λ h → ⊤ -- FileIOEff ⊤ opened (λ _ → closed)

-- Should we really use this now?
FileIO : EFFECT zero
FileIO = mkEff ⊤ FileIOEff

IOMonad : RawMonad IO.IO
IOMonad = record { return = IO.return ; _>>=_ = IO._>>=_ {zero} {zero}}

{-
openFile : ∀ {es m} → (mem : FileIO ∈ es) →
  (file : String) → EffM m Bool es (λ ok → updateResTy ok es mem (`openFile file))
openFile mem file = effect mem (`openFile file) -- (`openFile file)

closeFile : ∀ {m es } (mem : FileIO ∈ es) →
            EffM m FileHandle es (λ h → updateResTy h es mem `closeFile)
closeFile mem = effect mem `closeFile

openAndClose : ∀ {m} → String → EffM m ⊤ (FileIO ∷ []) λ _ → (FileIO ∷ [])
openAndClose file = openFile (here refl) file >>= λ
  { true → closeFile (here {!!}) >>= {!!}
  ; false → closeFile {!!} >>= {!!}
  }
-}


myOpClose : ∀ {m} → String → EffM m ⊤ (FileIO ∷ []) λ _ → (FileIO ∷ [])
myOpClose file = effect (here refl) (`openFile file) >>= λ
  { true → effect (here refl) `closeFile
  ; false → return tt}

{-
openFile : ∀ {f M i} (mem : FileIO ∈ i) → String → -- lookup i mem ≡ closed → String →
             EffM {f} M ? ? -- (λ ok → if ok then ? else ?)
-- ⟨ M ⟩Eff[ ok ∶ Bool ] i ==> (if ok then FileHandle else ⊤)
openFile = ? -- mem file = effect mem {!`openFile ?!} -- effect mem prf (`openFile file)

closeFile : ∀ {M Es i} (mem : FileIO ∈ Es) → lookup i mem ≡ opened →
            ⟨ M ⟩Eff Es [ _ ∶ ⊤ ] i ==> set i mem closed
closeFile mem prf = effect mem prf `closeFile

openAndClose : ∀ {M} → String → ⟨ M ⟩Eff (FileIO ∷ []) [ _ ∶ ⊤ ] (closed ∷ []) ==> (closed ∷ [])
openAndClose file =
  openFile (here refl) refl file >>= λ
  { true  → closeFile (here refl) refl
  ; false → return _
  }
-}


main : IO.IO ⊤
main = run IO.IO (record { return = IO.return ; _>>=_ = IO._>>=_ }) (myOpClose ".gitignore") myEnv
  where
    FileIOHandler : Handler IO.IO FileIOEff
    FileIOHandler v (`openFile x) k = k true (FH x)
    FileIOHandler (FH x) `closeFile k = k tt tt
    myEnv : Env IO.IO (FileIO ∷ [])
    myEnv = (FileIOHandler , tt) ∷ []

-- IOMonad evalers (openAndClose ".gitignore")
  -- where
    -- fileEval : Handler  IO.IO FileIO
    -- fileEval = ? -- (`openFile x) = IO.return false -- Let's not open any files ever, since we can't catch exceptions
    -- fileEval `closeFile = IO.return tt
    -- evalers : All (Handler IO.IO) (FileIO ∷ [])
    -- evalers = fileEval ∷ []
