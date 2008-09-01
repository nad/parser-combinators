------------------------------------------------------------------------
-- An example
------------------------------------------------------------------------

module RecursiveDescent.Hybrid.Mixfix.Example where

open import Data.Vec using ([]; _∷_; [_])
open import Data.List renaming ([_] to L[_])
open import Data.Product using (∃₂; ,_)
open import Data.Nat using (zero; suc)
open import Data.Fin using (#_)
open import Data.String
open import Data.Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import RecursiveDescent.Hybrid.Mixfix.Expr
open import RecursiveDescent.Hybrid.Mixfix.Fixity
import RecursiveDescent.Hybrid.Mixfix as Mixfix
open import RecursiveDescent.Hybrid
open import RecursiveDescent.Hybrid.Simple

------------------------------------------------------------------------
-- Operators

atom : Operator closed 0
atom = operator ("•" ∷ [])

• : Expr
• = ⟪ atom ∙ [] ⟫

parens : Operator closed 1
parens = operator ("(" ∷ ")" ∷ [])

⟦_⟧ : Expr -> Expr
⟦ e ⟧ = ⟪ parens ∙ [ e ] ⟫

plus : Operator (infx left) 0
plus = operator ("+" ∷ [])

_+_ : Expr -> Expr -> Expr
e₁ + e₂ = e₁ ⟨ plus ∙ [] ⟩ e₂

minus : Operator (infx left) 0
minus = operator ("-" ∷ [])

_-_ : Expr -> Expr -> Expr
e₁ - e₂ = e₁ ⟨ minus ∙ [] ⟩ e₂

times : Operator (infx left) 0
times = operator ("*" ∷ [])

_*_ : Expr -> Expr -> Expr
e₁ * e₂ = e₁ ⟨ times ∙ [] ⟩ e₂

comma : Operator (infx left) 0
comma = operator ("," ∷ [])

_,_ : Expr -> Expr -> Expr
e₁ , e₂ = e₁ ⟨ comma ∙ [] ⟩ e₂

wellTyped : Operator postfx 1
wellTyped = operator ("⊢" ∷ "∶" ∷ [])

_⊢_∶ : Expr -> Expr -> Expr
e₁ ⊢ e₂ ∶ = e₁ ⟨ wellTyped ∙ [ e₂ ] ⟫

------------------------------------------------------------------------
-- Precedence graph

prec : List (∃₂ Operator) -> PrecedenceGraph -> PrecedenceTree
prec ops = precedence (\fix -> gfilter (hasFixity fix) ops)

g : PrecedenceGraph
g = wt ∷ c ∷ pm ∷ t ∷ ap ∷ []
  where
  ap = prec ((, , atom) ∷ (, , parens) ∷ []) []
  t  = prec ((, , times) ∷ [])               (ap ∷ [])
  pm = prec ((, , plus) ∷ (, , minus) ∷ [])  (t ∷ ap ∷ [])
  c  = prec ((, , comma) ∷ [])               (pm ∷ t ∷ ap ∷ [])
  wt = prec ((, , wellTyped) ∷ [])           (c ∷ ap ∷ [])

open Mixfix g

------------------------------------------------------------------------
-- Some tests

test : String -> List Expr
test s = parse-complete (! expr) grammar
                        (map (fromList ∘ L[_]) (toList s))

-- Using an unoptimised type checker to run an inefficient parser can
-- take ages… The following examples have been converted into
-- postulates since I have not had the patience to wait long enough to
-- see whether the left- and right-hand sides actually match.

postulate
  ex₁ : test "•⊢•" ≡ []
  ex₂ : test "(•,•)⊢∶" ≡ []
  ex₃ : test "•⊢•∶" ≡ L[ • ⊢ • ∶ ]
  ex₄ : test "•,•+•*•⊢(•⊢•∶)∶" ≡
        L[ (• , (• + (• * •))) ⊢ ⟦ • ⊢ • ∶ ⟧ ∶ ]
