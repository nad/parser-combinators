------------------------------------------------------------------------
-- A very small library of derived parser combinators
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Parser.Lib where

open import Data.List
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import StructurallyRecursiveDescentParsing.Coinduction
open import StructurallyRecursiveDescentParsing.Parser
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  hiding (sound; complete)

-- A parser for a given token.

module Token
         (Tok : Set)
         (_≟_ : Decidable (_≡_ {A = Tok}))
         where

  private
    okIndex : Tok → Tok → List Tok
    okIndex tok tok′ with tok ≟ tok′
    ... | yes _ = tok′ ∷ []
    ... | no  _ = []

    ok : (tok tok′ : Tok) → Parser Tok Tok (okIndex tok tok′)
    ok tok tok′ with tok ≟ tok′
    ... | yes _ = return tok′
    ... | no  _ = fail

  theToken : Tok → Parser Tok Tok []
  theToken tok = token >>= λ tok′ → ♯? (ok tok tok′)

  sound : ∀ {t t′ s} →
          t′ ∈ theToken t · s →
          t ≡ t′ × s ≡ [ t′ ]
  sound {t} (_>>=_ {x = t″} token t′∈) with t ≟ t″
  sound (token >>= return) | yes t≈t″ = (t≈t″ , refl)
  sound (token >>= ())     | no  t≉t″

  complete : ∀ {t} → t ∈ theToken t · [ t ]
  complete {t} = token >>= ok-lemma
    where
    ok-lemma : t ∈ ok t t · []
    ok-lemma with t ≟ t
    ... | yes refl = return
    ... | no  t≢t  with t≢t refl
    ...   | ()
