module AocUtil where
open import Data.Maybe
open import Data.String as String
open import Foreign.Haskell using (Unit)
open import Data.List as List
open import Data.Nat
open import Data.Char
open import Data.Bool.Base
open import AocIO

void : ∀ {a} {A : Set a} → IO A → IO Unit
void m = m >>= λ _ → return Unit.unit

printString : String → IO Unit
printString s = putStrLn (toCostring s)

mainBuilder : (String → (List String) → IO Unit) → IO Unit
mainBuilder main' = getProgName >>= λ name → getArgs >>= main' name

readFileMain : (String → IO Unit) → String → (List String) → IO Unit
readFileMain f name (file ∷ []) = readFiniteFile file >>= f
readFileMain f name _ = putStrLn (toCostring ("Usage: " String.++ name String.++ " FILE"))

splitWhen : ∀ {a} {A : Set a} → (A → Bool) → List A → List (List A)
splitWhen pred [] = []
splitWhen pred (x ∷ ls) with (pred x) | splitWhen pred ls
... | false | [] =  List.[ List.[ x ] ]
splitWhen pred (x ∷ ls) | false | top-list ∷ rest = (x ∷ top-list) ∷ rest
... | true | rec = [] ∷ rec

lines : List Char → List (List Char)
lines = splitWhen isNewline
  where
    isNewline : Char → Bool
    isNewline '\n' = true
    isNewline _ = false

words : List Char → List (List Char)
words = splitWhen isWhitespace
  where
    isWhitespace : Char → Bool
    isWhitespace ' ' = true
    isWhitespace '\t' = true
    isWhitespace _ = false

sequence-io-prim : ∀ {a} {A : Set a} → List (IO A) → IO (List A)
sequence-io-prim [] = return []
sequence-io-prim (m ∷ ms) = m >>= λ x → sequence-io-prim ms >>= λ xs → return (x ∷ xs)

toDigit : Char → Maybe ℕ
toDigit '0' = just 0
toDigit '1' = just 1
toDigit '2' = just 2
toDigit '3' = just 3
toDigit '4' = just 4
toDigit '5' = just 5
toDigit '6' = just 6
toDigit '7' = just 7
toDigit '8' = just 8
toDigit '9' = just 9
toDigit _ = nothing

unsafeParseNat : List Char → ℕ
unsafeParseNat ls = unsafeParseNat' 0 ls
  where
    unsafeParseNat' : ℕ → List Char → ℕ
    unsafeParseNat' acc [] = acc
    unsafeParseNat' acc (x ∷ ls) with (toDigit x)
    ... | nothing = acc * 10
    ... | just n = unsafeParseNat' (n + (acc * 10)) ls
