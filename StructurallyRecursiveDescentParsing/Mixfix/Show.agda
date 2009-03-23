------------------------------------------------------------------------
-- Linearisation of mixfix operators
------------------------------------------------------------------------

-- Note: The code assumes that the grammar is unambiguous.

open import StructurallyRecursiveDescentParsing.Mixfix.Expr as Expr

module StructurallyRecursiveDescentParsing.Mixfix.Show
         (g : PrecedenceGraph)
         where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
import Data.Vec as Vec; open Vec using (Vec; []; _∷_)
import Data.DifferenceList as DiffList
open DiffList using (DiffList; [_]; _++_) renaming (_∷_ to cons)
open import Data.Product using (∃)
open import Data.Function using (_∘_)

open Expr.PrecedenceCorrect g

mutual

  showE : ∀ {ps} → Expr ps → DiffList NamePart
  showE (_ ∙ e) = showIn e

  showIn : ∀ {p fix} → ExprIn p fix → DiffList NamePart
  showIn    ⟪ op ⟫     =                  showInner op
  showIn (l ⟨ op ⟫)    = showOuter l ++ showInner op
  showIn (  ⟪ op ⟩  r) =                  showInner op ++ showOuter r
  showIn (l ⟨ op ⟩  r) = showE     l ++ showInner op ++ showE     r
  showIn (l ⟨ op ⟩ˡ r) = showOuter l ++ showInner op ++ showE     r
  showIn (l ⟨ op ⟩ʳ r) = showE     l ++ showInner op ++ showOuter r

  showOuter : ∀ {p fix} → Outer p fix → DiffList NamePart
  showOuter (similar e) = showIn e
  showOuter (tighter e) = showE  e

  showInner : ∀ {fix} {ops : List (∃ (Operator fix))} →
                Inner ops → DiffList NamePart
  showInner (_∙_ {op = operator ns} _ args) = showInner′ ns args

  showInner′ : ∀ {arity} →
                 Vec NamePart (1 + arity) → Vec (Expr g) arity →
                 DiffList NamePart
  showInner′ (n ∷ []) []           = [ n ]
  showInner′ (n ∷ ns) (arg ∷ args) =
    cons n (showE arg ++ showInner′ ns args)

show : ∀ {ps} → Expr ps → List NamePart
show = DiffList.toList ∘ showE
