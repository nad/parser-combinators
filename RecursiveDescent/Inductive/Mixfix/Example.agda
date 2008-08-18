------------------------------------------------------------------------
-- An example
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix.Example where

open import Data.Graph.Acyclic hiding (map)
open import Data.Vec using ([]; _∷_; [_])
open import Data.List renaming ([_] to L[_])
open import Data.Product using (,_)
open import Data.Nat using (zero; suc)
open import Data.Fin using (#_)
open import Data.String
open import Data.Function using (_∘_)
open import Relation.Binary.PropositionalEquality

open import RecursiveDescent.Inductive.Mixfix.Expr
open import RecursiveDescent.Inductive.Mixfix.FA
open import RecursiveDescent.Inductive.Mixfix
open import RecursiveDescent.Inductive

------------------------------------------------------------------------
-- Operators

atom : Operator closed 0
atom = oper ("•" ∷ [])

• : Expr
• = _ ⟨ atom ⟨ [] ⟩ ⟩ _

parens : Operator closed 1
parens = oper ("(" ∷ ")" ∷ [])

⟦_⟧ : Expr -> Expr
⟦ e ⟧ = _ ⟨ parens ⟨ [ e ] ⟩ ⟩ _

plus : Operator (infx left) 0
plus = oper ("+" ∷ [])

_+_ : Expr -> Expr -> Expr
e₁ + e₂ = e₁ ⟨ plus ⟨ [] ⟩ ⟩ e₂

minus : Operator (infx left) 0
minus = oper ("-" ∷ [])

_-_ : Expr -> Expr -> Expr
e₁ - e₂ = e₁ ⟨ minus ⟨ [] ⟩ ⟩ e₂

times : Operator (infx left) 0
times = oper ("*" ∷ [])

_*_ : Expr -> Expr -> Expr
e₁ * e₂ = e₁ ⟨ times ⟨ [] ⟩ ⟩ e₂

comma : Operator (infx left) 0
comma = oper ("," ∷ [])

_,_ : Expr -> Expr -> Expr
e₁ , e₂ = e₁ ⟨ comma ⟨ [] ⟩ ⟩ e₂

wellTyped : Operator postfx 1
wellTyped = oper ("⊢" ∷ "∶" ∷ [])

_⊢_∶ : Expr -> Expr -> Expr
e₁ ⊢ e₂ ∶ = e₁ ⟨ wellTyped ⟨ [ e₂ ] ⟩ ⟩ _

------------------------------------------------------------------------
-- Precedence graph

g : PrecedenceGraph 5
g = context ((, , wellTyped) ∷ [])           ((, # 0) ∷ (, # 3) ∷ [])           &
    context ((, , comma) ∷ [])               ((, # 0) ∷ (, # 1) ∷ (, # 2) ∷ []) &
    context ((, , plus) ∷ (, , minus) ∷ [])  ((, # 0) ∷ (, # 1) ∷ [])           &
    context ((, , times) ∷ [])               ((, # 0) ∷ [])                     &
    context ((, , atom) ∷ (, , parens) ∷ []) []                                 &
    ∅

------------------------------------------------------------------------
-- Some tests

test : String -> List Expr
test s = parse-complete (! expr g) grammar
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
