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

------------------------------------------------------------------------
-- Operators

atom : Operator closed 0
atom = operator ("•" ∷ [])

parens : Operator closed 1
parens = operator ("(" ∷ ")" ∷ [])

plus : Operator (infx left) 0
plus = operator ("+" ∷ [])

minus : Operator (infx left) 0
minus = operator ("-" ∷ [])

times : Operator (infx left) 0
times = operator ("*" ∷ [])

comma : Operator (infx left) 0
comma = operator ("," ∷ [])

wellTyped : Operator postfx 1
wellTyped = operator ("⊢" ∷ "∶" ∷ [])

------------------------------------------------------------------------
-- Precedence graph

abstract  -- To speed up type-checking.

  prec : List (∃₂ Operator) → PrecedenceGraph → Precedence
  prec ops = precedence (λ fix → List.gfilter (hasFixity fix) ops)

  mutual

    ap = prec ((, , atom) ∷ (, , parens) ∷ []) []
    t  = prec ((, , times) ∷ [])               (ap ∷ [])
    pm = prec ((, , plus) ∷ (, , minus) ∷ [])  (t ∷ ap ∷ [])
    c  = prec ((, , comma) ∷ [])               (pm ∷ t ∷ ap ∷ [])
    wt = prec ((, , wellTyped) ∷ [])           (c ∷ ap ∷ [])

  g : PrecedenceGraph
  g = wt ∷ c ∷ pm ∷ t ∷ ap ∷ []

------------------------------------------------------------------------
-- Expressions

  open Expr.PrecedenceCorrect g

  • : ExprIn ap nothing
  • = ⟪ here ∙ [] ⟫

  ⟦_⟧ : Expr g → ExprIn ap nothing
  ⟦ e ⟧ = ⟪ there here ∙ [ e ] ⟫

  _+_ : Outer pm left → Expr (t ∷ ap ∷ []) → ExprIn pm (just left)
  e₁ + e₂ = e₁ ⟨ here ∙ [] ⟩ˡ e₂

  _-_ : Outer pm left → Expr (t ∷ ap ∷ []) → ExprIn pm (just left)
  e₁ - e₂ = e₁ ⟨ there here ∙ [] ⟩ˡ e₂

  _*_ : Outer t left → Expr (ap ∷ []) → ExprIn t (just left)
  e₁ * e₂ = e₁ ⟨ here ∙ [] ⟩ˡ e₂

  _,_ : Outer c left → Expr (pm ∷ t ∷ ap ∷ []) → ExprIn c (just left)
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

parse : String → List String
parse = List.map (fromNameParts ∘ show) ∘
        Mixfix.parseExpr g ∘
        toNameParts

test : String → List String → Bool
test s₁ s₂ = decToBool (parse s₁ ≟ s₂)

runTest : String → List String → IO ⊤
runTest s₁ s₂ = ♯₁
  putStrLn ("Testing: " ++ s₁)                         >> ♯₁ (♯₁
  mapM′ putStrLn (Colist.fromList $ parse s₁)          >> ♯₁
  putStrLn (if test s₁ s₂ then "Passed" else "Failed") )

main = run (♯₁
  runTest "•⊢•"             []                     >> ♯₁ (♯₁
  runTest "(•,•)⊢∶"         []                     >> ♯₁ (♯₁
  runTest "•⊢•∶"            L[ "•⊢•∶" ]            >> ♯₁
  runTest "•,•+•*•⊢(•⊢•∶)∶" L[ "•,•+•*•⊢(•⊢•∶)∶" ] )))
