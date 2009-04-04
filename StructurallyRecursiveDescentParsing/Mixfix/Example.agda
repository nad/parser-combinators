------------------------------------------------------------------------
-- An example
------------------------------------------------------------------------

module StructurallyRecursiveDescentParsing.Mixfix.Example where

open import Coinduction
open import Data.Vec using ([]; _∷_; [_])
import Data.List as List
open List using (List; []; _∷_; _∈_; here; there)
          renaming ([_] to L[_])
import Data.Colist as Colist
open import Data.Product using (∃₂; ,_)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (zero; suc)
open import Data.Fin using (#_)
import Data.String as String
open String using (String; _++_)
import Data.List.Equality as ListEq
open import Relation.Binary
open DecSetoid (ListEq.DecidableEquality.decSetoid String.decSetoid)
  using (_≟_)
open import Data.Function using (_∘_; _$_)
open import Data.Bool using (Bool; if_then_else_)
import Data.Bool.Show as Bool
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary.Decidable using (decToBool)
open import Relation.Binary.PropositionalEquality
open import IO

open import StructurallyRecursiveDescentParsing.Mixfix.Expr as Expr
open import StructurallyRecursiveDescentParsing.Mixfix.Fixity
  hiding (_≟_)
import StructurallyRecursiveDescentParsing.Mixfix as Mixfix
import StructurallyRecursiveDescentParsing.Mixfix.Show as Show
import StructurallyRecursiveDescentParsing.Simplified as Simplified
open Simplified using (Parser)
import StructurallyRecursiveDescentParsing.Backend.DepthFirst
  as DepthFirst
import StructurallyRecursiveDescentParsing.Backend.BreadthFirst
  as BreadthFirst

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

abstract  -- To speed up type-checking.

  prec : List (∃₂ Operator) → PrecedenceGraph → Precedence
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

  open Expr.PrecedenceCorrect g

  • : ExprIn a nothing
  • = ⟪ here ∙ [] ⟫

  _+_ : Outer pl left → Expr (a ∷ []) → ExprIn pl (just left)
  e₁ + e₂ = e₁ ⟨ here ∙ [] ⟩ˡ e₂

  i_t_ : Expr g → Outer ii right → ExprIn ii (just right)
  i e₁ t e₂ = ⟪ here ∙ e₁ ∷ [] ⟩ e₂

  i_t_e_ : Expr g → Expr g → Outer ii right → ExprIn ii (just right)
  i e₁ t e₂ e e₃ = ⟪ there here ∙ e₁ ∷ e₂ ∷ [] ⟩ e₃

  _,_ : Outer c left → Expr (ii ∷ pl ∷ a ∷ []) → ExprIn c (just left)
  e₁ , e₂ = e₁ ⟨ here ∙ [] ⟩ˡ e₂

  _⊢_∶ : Outer wt left → Expr g → Expr g
  e₁ ⊢ e₂ ∶ = here ∙ (e₁ ⟨ here ∙ [ e₂ ] ⟫)

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
parse breadthFirst p = BreadthFirst.parseComplete (Simplified.⟦_⟧ p)

parseExpr : Backend → String → List String
parseExpr backend = List.map (fromNameParts ∘ show) ∘
                    parse backend (Mixfix.expression g) ∘
                    toNameParts

-- The breadth-first backend is considerably slower than the
-- depth-first one on these examples.
backend = depthFirst

runTest : String → List String → IO ⊤
runTest s₁ s₂ = ♯₁
  putStrLn ("Testing: " ++ s₁)           >> ♯₁ (♯₁
  mapM′ putStrLn (Colist.fromList p₁)    >> ♯₁
  putStrLn (if decToBool (p₁ ≟ s₂)
            then "Passed" else "Failed") )
  where p₁ = parseExpr backend s₁

main = run (♯₁
  runTest "•+•⊢•∶"      []                               >> ♯₁ (♯₁
  runTest "•,•⊢∶"       []                               >> ♯₁ (♯₁
  runTest "•⊢•∶"        L[ "•⊢•∶" ]                      >> ♯₁ (♯₁
  runTest "•,i•t•+•⊢•∶" L[ "•,i•t•+•⊢•∶" ]               >> ♯₁
  runTest "i•ti•t•e•"   ("i•ti•t•e•" ∷ "i•ti•t•e•" ∷ []) ))))
