------------------------------------------------------------------------
-- An example
------------------------------------------------------------------------

module Mixfix.Acyclic.Example where

open import Coinduction
open import Data.Vec using ([]; _∷_; [_])
open import Data.List as List
  using (List; []; _∷_) renaming ([_] to L[_])
open import Data.List.Any using (here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
import Data.Colist as Colist
open import Data.Product using (∃₂; ,_)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (zero; suc)
open import Data.Fin using (#_)
import Data.String as String
open String using (String; _++_)
open import Relation.Binary
import Relation.Binary.List.Pointwise as ListEq
open DecSetoid (ListEq.decSetoid String.decSetoid) using (_≟_)
open import Function using (_∘_; _$_)
open import Data.Bool using (Bool; if_then_else_)
import Data.Bool.Show as Bool
open import Relation.Nullary.Decidable using (⌊_⌋)
import Relation.Binary.PropositionalEquality as P
open import IO

open import Mixfix.Fixity hiding (_≟_)
open import Mixfix.Operator
open import Mixfix.Expr
open import Mixfix.Acyclic.PrecedenceGraph
import Mixfix.Acyclic.Grammar as Grammar
import Mixfix.Acyclic.Show as Show
import StructurallyRecursiveDescentParsing.Simplified as Simplified
open Simplified using (Parser)
import StructurallyRecursiveDescentParsing.DepthFirst as DepthFirst
import TotalParserCombinators.BreadthFirst as BreadthFirst

------------------------------------------------------------------------
-- Operators

atom : Operator closed 0
atom = record { nameParts = "•" ∷ [] }

plus : Operator (infx left) 0
plus = record { nameParts = "+" ∷ [] }

ifThen : Operator prefx 1
ifThen = record { nameParts = "i" ∷ "t" ∷ [] }

ifThenElse : Operator prefx 2
ifThenElse = record { nameParts = "i" ∷ "t" ∷ "e" ∷ [] }

comma : Operator (infx left) 0
comma = record { nameParts = "," ∷ [] }

wellTyped : Operator postfx 1
wellTyped = record { nameParts = "⊢" ∷ "∶" ∷ [] }

------------------------------------------------------------------------
-- Precedence graph

prec : List (∃₂ Operator) → List Precedence → Precedence
prec ops = precedence (λ fix → List.gfilter (hasFixity fix) ops)

mutual

  a  = prec ((, , atom) ∷ [])                       []
  pl = prec ((, , plus) ∷ [])                       (a ∷ [])
  ii = prec ((, , ifThen) ∷ (, , ifThenElse) ∷ [])  (pl ∷ a ∷ [])
  c  = prec ((, , comma) ∷ [])                      (ii ∷ pl ∷ a ∷ [])
  wt = prec ((, , wellTyped) ∷ [])                  (c ∷ a ∷ [])

g : PrecedenceGraph
g = wt ∷ c ∷ ii ∷ pl ∷ a ∷ []

------------------------------------------------------------------------
-- Expressions

open PrecedenceCorrect acyclic g

• : ExprIn a non
• = ⟪ here P.refl ∙ [] ⟫

_+_ : Outer pl left → Expr (a ∷ []) → ExprIn pl left
e₁ + e₂ = e₁ ⟨ here P.refl ∙ [] ⟩ˡ e₂

i_t_ : Expr g → Outer ii right → ExprIn ii right
i e₁ t e₂ = ⟪ here P.refl ∙ e₁ ∷ [] ⟩ e₂

i_t_e_ : Expr g → Expr g → Outer ii right → ExprIn ii right
i e₁ t e₂ e e₃ = ⟪ there (here P.refl) ∙ e₁ ∷ e₂ ∷ [] ⟩ e₃

_,_ : Outer c left → Expr (ii ∷ pl ∷ a ∷ []) → ExprIn c left
e₁ , e₂ = e₁ ⟨ here P.refl ∙ [] ⟩ˡ e₂

_⊢_∶ : Outer wt left → Expr g → Expr g
e₁ ⊢ e₂ ∶ = here P.refl ∙ (e₁ ⟨ here P.refl ∙ [ e₂ ] ⟫)

------------------------------------------------------------------------
-- Some tests

open Show g

fromNameParts : List NamePart → String
fromNameParts = List.foldr _++_ ""

toNameParts : String → List NamePart
toNameParts = List.map (String.fromList ∘ L[_]) ∘ String.toList

data Backend : Set where
  depthFirst   : Backend
  breadthFirst : Backend

parse : ∀ {Tok e R} → Backend → Parser Tok e R → List Tok → List R
parse depthFirst   p = DepthFirst.parseComplete p
parse breadthFirst p = BreadthFirst.parse (Simplified.⟦_⟧ p)

parseExpr : Backend → String → List String
parseExpr backend = List.map (fromNameParts ∘ show) ∘
                    parse backend (Grammar.expression g) ∘
                    toNameParts

-- The breadth-first backend is considerably slower than the
-- depth-first one on these examples.
backend = depthFirst

runTest : String → List String → IO ⊤
runTest s₁ s₂ = ♯
  putStrLn ("Testing: " ++ s₁)                          >> ♯ (♯
  mapM′ putStrLn (Colist.fromList p₁)                   >> ♯
  putStrLn (if ⌊ p₁ ≟ s₂ ⌋ then "Passed" else "Failed") )
  where p₁ = parseExpr backend s₁

main = run (♯
  runTest "•+•⊢•∶"      []                               >> ♯ (♯
  runTest "•,•⊢∶"       []                               >> ♯ (♯
  runTest "•⊢•∶"        L[ "•⊢•∶" ]                      >> ♯ (♯
  runTest "•,i•t•+•⊢•∶" L[ "•,i•t•+•⊢•∶" ]               >> ♯
  runTest "i•ti•t•e•"   ("i•ti•t•e•" ∷ "i•ti•t•e•" ∷ []) ))))
