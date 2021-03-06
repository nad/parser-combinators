------------------------------------------------------------------------
-- An example
------------------------------------------------------------------------

module Mixfix.Cyclic.Example where

open import Codata.Musical.Notation
open import Data.Vec using ([]; _∷_; [_])
open import Data.List as List
  using (List; []; _∷_) renaming ([_] to L[_])
open import Data.List.Relation.Unary.Any as Any using (here; there)
import Codata.Musical.Colist as Colist
open import Data.Product using (∃₂; -,_)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; #_; zero; suc)
import Data.List.Relation.Binary.Pointwise as ListEq
import Data.String as String
open String using (String; _++_)
import Data.String.Properties as String
open import Relation.Binary
open DecSetoid (ListEq.decSetoid String.≡-decSetoid) using (_≟_)
open import Function using (_∘_)
open import Data.Bool using (Bool; if_then_else_)
open import Relation.Nullary.Decidable using (⌊_⌋)
import Relation.Binary.PropositionalEquality as P
open import IO
import Level

open import Mixfix.Fixity hiding (_≟_)
open import Mixfix.Operator
open import Mixfix.Expr
open import Mixfix.Cyclic.PrecedenceGraph
  hiding (module PrecedenceGraph)
import Mixfix.Cyclic.Grammar as Grammar
import Mixfix.Cyclic.Show as Show
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

mutual

  private

    levels : ℕ
    levels = 5

    a  = # 0
    pl = # 1
    ii = # 2
    c  = # 3
    wt = #_ 4 {n = levels}

  g : PrecedenceGraph
  g = record
    { levels = levels
    ; ops    = λ p fix → List.mapMaybe (hasFixity fix) (ops p)
    ; ↑      = ↑
    }
    where
    Precedence : Set
    Precedence = Fin levels

    ops : Precedence → List (∃₂ Operator)
    ops zero                             = (-, -, atom)       ∷ []
    ops (suc zero)                       = (-, -, plus)       ∷ []
    ops (suc (suc zero))                 = (-, -, ifThen)     ∷
                                           (-, -, ifThenElse) ∷ []
    ops (suc (suc (suc zero)))           = (-, -, comma)      ∷ []
    ops (suc (suc (suc (suc zero))))     = (-, -, wellTyped)  ∷ []
    ops (suc (suc (suc (suc (suc ())))))

    ↑ : Precedence → List (Precedence)
    ↑ zero                             = []
    ↑ (suc zero)                       = a ∷ []
    ↑ (suc (suc zero))                 = pl ∷ a ∷ []
    ↑ (suc (suc (suc zero)))           = ii ∷ pl ∷ a ∷ []
    ↑ (suc (suc (suc (suc zero))))     = c ∷ a ∷ []
    ↑ (suc (suc (suc (suc (suc ())))))

------------------------------------------------------------------------
-- Expressions

open PrecedenceCorrect cyclic g

• : ExprIn a non
• = ⟪ here P.refl ∙ [] ⟫

_+_ : Outer pl left → Expr (a ∷ []) → ExprIn pl left
e₁ + e₂ = e₁ ⟨ here P.refl ∙ [] ⟩ˡ e₂

i_t_ : Expr anyPrecedence → Outer ii right → ExprIn ii right
i e₁ t e₂ = ⟪ here P.refl ∙ e₁ ∷ [] ⟩ e₂

i_t_e_ : Expr anyPrecedence → Expr anyPrecedence → Outer ii right →
         ExprIn ii right
i e₁ t e₂ e e₃ = ⟪ there (here P.refl) ∙ e₁ ∷ e₂ ∷ [] ⟩ e₃

_,_ : Outer c left → Expr (ii ∷ pl ∷ a ∷ []) → ExprIn c left
e₁ , e₂ = e₁ ⟨ here P.refl ∙ [] ⟩ˡ e₂

_⊢_∶ : Outer wt left → Expr anyPrecedence → ExprIn wt left
e₁ ⊢ e₂ ∶ = e₁ ⟨ here P.refl ∙ [ e₂ ] ⟫

------------------------------------------------------------------------
-- Some tests

open Show cyclic g

fromNameParts : List NamePart → String
fromNameParts = List.foldr _++_ ""

toNameParts : String → List NamePart
toNameParts = List.map (String.fromList ∘ L[_]) ∘ String.toList

parseExpr : String → List String
parseExpr = List.map (fromNameParts ∘ show) ∘
            BreadthFirst.parse (Grammar.expression cyclic g) ∘
            toNameParts

runTest : String → List String → IO (⊤ {ℓ = Level.zero})
runTest s₁ s₂ = do
  putStrLn ("Testing: " ++ s₁)
  Colist.mapM′ putStrLn (Colist.fromList p₁)
  putStrLn (if ⌊ p₁ ≟ s₂ ⌋ then "Passed" else "Failed")
  where p₁ = parseExpr s₁

main = run do
  runTest "•+•⊢•∶"      []
  runTest "•,•⊢∶"       []
  runTest "•⊢•∶"        L[ "•⊢•∶" ]
  runTest "•,i•t•+•⊢•∶" L[ "•,i•t•+•⊢•∶" ]
  runTest "i•ti•t•e•"   ("i•ti•t•e•" ∷ "i•ti•t•e•" ∷ [])
