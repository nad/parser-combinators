------------------------------------------------------------------------
-- Precedence-correct expressions
------------------------------------------------------------------------

module Mixfix.Expr where

open import Data.Vec  using (Vec)
open import Data.List using (List; []; _∷_)
open import Data.List.Any as Any using (here; there)
open Any.Membership-≡ using (_∈_)
open import Data.Product using (∃; _,_)

open import Mixfix.Fixity
open import Mixfix.Operator

------------------------------------------------------------------------
-- An abstract definition of precedence graphs

-- The interface of precedence graphs.

record PrecedenceGraphInterface : Set₁ where
  field
    -- Precedence graphs.
    PrecedenceGraph : Set

    -- Precedence levels.
    Precedence : PrecedenceGraph → Set

    -- The operators of the given precedence.
    ops : (g : PrecedenceGraph) →
          Precedence g → (fix : Fixity) → List (∃ (Operator fix))

    -- The immediate successors of the precedence level.
    ↑ : (g : PrecedenceGraph) → Precedence g → List (Precedence g)

    -- All precedence levels in the graph.
    anyPrecedence : (g : PrecedenceGraph) → List (Precedence g)

-- When a precedence graph is given the following module may be
-- convenient to avoid having to write "g" all the time.

module PrecedenceGraph
         (i : PrecedenceGraphInterface)
         (g : PrecedenceGraphInterface.PrecedenceGraph i)
         where

  PrecedenceGraph : Set
  PrecedenceGraph = PrecedenceGraphInterface.PrecedenceGraph i

  Precedence : Set
  Precedence = PrecedenceGraphInterface.Precedence i g

  ops : Precedence → (fix : Fixity) → List (∃ (Operator fix))
  ops = PrecedenceGraphInterface.ops i g

  ↑ : Precedence → List Precedence
  ↑ = PrecedenceGraphInterface.↑ i g

  anyPrecedence : List Precedence
  anyPrecedence = PrecedenceGraphInterface.anyPrecedence i g

------------------------------------------------------------------------
-- Precedence-correct operator applications

-- Parameterised on a precedence graph.

module PrecedenceCorrect
         (i : PrecedenceGraphInterface)
         (g : PrecedenceGraphInterface.PrecedenceGraph i)
         where

  open PrecedenceGraph i g public

  mutual

    infixl 4 _⟨_⟩ˡ_
    infixr 4 _⟨_⟩ʳ_
    infix  4 _⟨_⟩_ _⟨_⟫ ⟪_⟩_ _∙_

    -- Expr ps contains expressions where the outermost operator has
    -- one of the precedences in ps.

    data Expr (ps : List Precedence) : Set where
      _∙_ : ∀ {p assoc} (p∈ps : p ∈ ps) (e : ExprIn p assoc) → Expr ps

    -- ExprIn p assoc contains expressions where the outermost
    -- operator has precedence p (is /in/ precedence level p) and the
    -- associativity assoc.

    data ExprIn (p : Precedence) : Associativity → Set where
      ⟪_⟫    :                    (op : Inner (ops p closed      ))                     → ExprIn p non
      _⟨_⟫   : (l : Outer p left) (op : Inner (ops p postfx      ))                     → ExprIn p left
      ⟪_⟩_   :                    (op : Inner (ops p prefx       )) (r : Outer p right) → ExprIn p right
      _⟨_⟩_  : (l : Expr (↑ p)  ) (op : Inner (ops p (infx non  ))) (r : Expr (↑ p)   ) → ExprIn p non
      _⟨_⟩ˡ_ : (l : Outer p left) (op : Inner (ops p (infx left ))) (r : Expr (↑ p)   ) → ExprIn p left
      _⟨_⟩ʳ_ : (l : Expr (↑ p)  ) (op : Inner (ops p (infx right))) (r : Outer p right) → ExprIn p right

    -- Outer p fix contains expressions where the head operator either
    --   ⑴ has precedence p and associativity assoc or
    --   ⑵ binds strictly tighter than p.

    data Outer (p : Precedence) (assoc : Associativity) : Set where
      similar : (e : ExprIn p assoc) → Outer p assoc
      tighter : (e : Expr (↑ p))     → Outer p assoc

    -- Inner ops contains the internal parts (operator plus
    -- internal arguments) of operator applications. The operators
    -- have to be members of ops.

    data Inner {fix} (ops : List (∃ (Operator fix))) : Set where
      _∙_ : ∀ {arity op}
            (op∈ops : (arity , op) ∈ ops)
            (args : Vec (Expr anyPrecedence) arity) →
            Inner ops

  -- "Weakening".

  weakenE : ∀ {p ps} → Expr ps → Expr (p ∷ ps)
  weakenE (p∈ps ∙ e) = there p∈ps ∙ e

  weakenI : ∀ {fix ops} {op : ∃ (Operator fix)} →
            Inner ops → Inner (op ∷ ops)
  weakenI (op∈ops ∙ args) = there op∈ops ∙ args
