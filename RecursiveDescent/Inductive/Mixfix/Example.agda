------------------------------------------------------------------------
-- An example
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix.Example where

open import Data.Graph.Acyclic
open import Data.Vec
open import Data.List as List
open import Data.Product
open import Data.Fin
open import Relation.Binary.PropositionalEquality

open import RecursiveDescent.Inductive.Mixfix.Expr
  renaming (⟨_⟩ to ⟪_⟫)
open import RecursiveDescent.Inductive.Mixfix.FA
open import RecursiveDescent.Inductive.Mixfix.Token
  renaming (namePart to np)
open import RecursiveDescent.Inductive.Mixfix
open import RecursiveDescent.Inductive

⊕ : Operator (infx left) 0
⊕ = oper ("+" ∷ [])

⊖ : Operator (infx left) 0
⊖ = oper ("-" ∷ [])

⊛ : Operator (infx left) 0
⊛ = oper ("*" ∷ [])

⊙ : Operator (infx left) 0
⊙ = oper ("," ∷ [])

⊢ : Operator postfx 1
⊢ = oper ("⊢" ∷ ":" ∷ [])

g : PrecedenceGraph 4
g = context ((, , ⊢) ∷ [])           ((, # 0) ∷ [])           &
    context ((, , ⊙) ∷ [])           ((, # 0) ∷ (, # 1) ∷ []) &
    context ((, , ⊕) ∷ (, , ⊖) ∷ []) ((, # 0) ∷ [])           &
    context ((, , ⊛) ∷ [])           []                       &
    ∅

-- Note: This example takes very long time to type check (I have not
-- type checked it), so it has been converted into a postulate.

postulate
  test : parse-complete (! expr g) grammar
           (atom ∷
            np "," ∷
            atom ∷ np "+" ∷ atom ∷ np "*" ∷ atom ∷
            np "⊢" ∷
            ⟨ ∷ atom ∷ np "⊢" ∷ atom ∷ np ":" ∷ ⟩ ∷
            np ":" ∷ [])
           ≡ List.singleton
               (⊢ ∙ (⊙ ∙ atom ∷
                         (⊕ ∙ atom ∷ (⊛ ∙ atom ∷ atom ∷ []) ∷ []) ∷ []) ∷
                    ⟪ ⊢ ∙ atom ∷ atom ∷ [] ⟫ ∷ [])
  -- test = ≡-refl
