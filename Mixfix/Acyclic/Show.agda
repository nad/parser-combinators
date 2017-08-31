------------------------------------------------------------------------
-- Linearisation of mixfix operators
------------------------------------------------------------------------

open import Mixfix.Expr
open import Mixfix.Acyclic.PrecedenceGraph
  using (acyclic; precedence)

module Mixfix.Acyclic.Show
         (g : PrecedenceGraphInterface.PrecedenceGraph acyclic)
         where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List)
open import Data.List.Any using (here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Vec using (Vec; []; _∷_)
import Data.DifferenceList as DiffList
open DiffList using (DiffList; _++_)
              renaming (_∷_ to cons; [_] to singleton)
open import Data.Product using (∃; _,_; ,_)
open import Function using (_∘_; flip)
open import Data.Maybe using (Maybe; nothing; just)
import Data.String as String
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open PrecedenceCorrect acyclic g
open import StructurallyRecursiveDescentParsing.Simplified
open import StructurallyRecursiveDescentParsing.Simplified.Semantics
  as Semantics
open import Mixfix.Fixity
open import Mixfix.Operator
open import Mixfix.Acyclic.Lib as Lib
open Lib.Semantics-⊕
import Mixfix.Acyclic.Grammar
import Mixfix.Acyclic.Lemma
private
  module Grammar = Mixfix.Acyclic.Grammar g
  module Lemma   = Mixfix.Acyclic.Lemma   g

------------------------------------------------------------------------
-- Linearisation

-- Note: The code assumes that the grammar is unambiguous.

module Show where

  mutual

    expr : ∀ {ps} → Expr ps → DiffList NamePart
    expr (_ ∙ e) = exprIn e

    exprIn : ∀ {p assoc} → ExprIn p assoc → DiffList NamePart
    exprIn    ⟪ op ⟫     =            inner op
    exprIn (l ⟨ op ⟫   ) = outer l ++ inner op
    exprIn (  ⟪ op ⟩  r) =            inner op ++ outer r
    exprIn (l ⟨ op ⟩  r) = expr  l ++ inner op ++ expr  r
    exprIn (l ⟨ op ⟩ˡ r) = outer l ++ inner op ++ expr  r
    exprIn (l ⟨ op ⟩ʳ r) = expr  l ++ inner op ++ outer r

    outer : ∀ {p assoc} → Outer p assoc → DiffList NamePart
    outer (similar e) = exprIn e
    outer (tighter e) = expr   e

    inner : ∀ {fix} {ops : List (∃ (Operator fix))} →
            Inner ops → DiffList NamePart
    inner (_∙_ {op = op} _ args) = inner′ (nameParts op) args

    inner′ : ∀ {arity} → Vec NamePart (1 + arity) → Vec (Expr g) arity →
             DiffList NamePart
    inner′ (n ∷ []) []           = singleton n
    inner′ (n ∷ ns) (arg ∷ args) = cons n (expr arg ++ inner′ ns args)

show : ∀ {ps} → Expr ps → List NamePart
show = DiffList.toList ∘ Show.expr

------------------------------------------------------------------------
-- Correctness

module Correctness where

  mutual

    expr : ∀ {ps s} (e : Expr ps) →
           e ⊕ s ∈⟦ Grammar.precs ps ⟧· Show.expr e s
    expr (here refl  ∙ e) = ∣ˡ (<$> exprIn e)
    expr (there x∈xs ∙ e) = ∣ʳ (<$> expr (x∈xs ∙ e))

    exprIn : ∀ {p assoc s} (e : ExprIn p assoc) →
             (, e) ⊕ s ∈⟦ Grammar.prec p ⟧· Show.exprIn e s
    exprIn {precedence ops sucs} e = exprIn′ _ e
      where
      p        = precedence ops sucs
      module N = Grammar.Prec ops sucs

      lemmaʳ : ∀ {f : Outer p right → ExprIn p right} {s e} {g : DiffList NamePart} →
               (∀ {s} → f ⊕ s ∈⟦ N.preRight ⟧· g s) →
                          e  ⊕ s ∈⟦ N.appʳ <$> N.preRight + ⊛ N.p↑ ⟧·    Show.exprIn e s →
               f (similar e) ⊕ s ∈⟦ N.appʳ <$> N.preRight + ⊛ N.p↑ ⟧· g (Show.exprIn e s)
      lemmaʳ f∈ (<$> fs∈ ⊛ e∈) = <$> +-∷ f∈ fs∈ ⊛ e∈

      preRight : ∀ {s} (e : ExprIn p right) →
                 e ⊕ s ∈⟦ N.appʳ <$> N.preRight + ⊛ N.p↑ ⟧· Show.exprIn e s
      preRight (  ⟪ op ⟩  tighter e) = <$> +-[] (∣ˡ (<$> inner op)) ⊛ expr e
      preRight (  ⟪ op ⟩  similar e) = lemmaʳ   (∣ˡ (<$> inner op)) (preRight e)
      preRight (l ⟨ op ⟩ʳ tighter e) = <$> +-[] (∣ʳ (<$> expr l ⊛ inner op)) ⊛ expr e
      preRight (l ⟨ op ⟩ʳ similar e) = lemmaʳ   (∣ʳ (<$> expr l ⊛ inner op)) (preRight e)

      lemmaˡ : ∀ {f : Outer p left → ExprIn p left} {s e} {g : DiffList NamePart} →
               (∀ {s} → f ⊕ s ∈⟦ N.postLeft ⟧· g s) →
                          e  ⊕ g s ∈⟦ N.appˡ <$> N.p↑ ⊛ N.postLeft + ⟧· Show.exprIn e (g s) →
               f (similar e) ⊕   s ∈⟦ N.appˡ <$> N.p↑ ⊛ N.postLeft + ⟧· Show.exprIn e (g s)
      lemmaˡ {f} f∈ (_⊛_ {x = fs} (<$>_ {x = e} e∈) fs∈) =
        Lib.Semantics-⊕.cast∈ (Lemma.appˡ-∷ʳ (tighter e) fs f) (<$> e∈ ⊛ +-∷ʳ fs∈ f∈)

      postLeft : ∀ {s} (e : ExprIn p left) →
                 e ⊕ s ∈⟦ N.appˡ <$> N.p↑ ⊛ N.postLeft + ⟧· Show.exprIn e s
      postLeft (tighter e ⟨ op ⟫   ) = <$> expr e ⊛ +-[] (∣ˡ (<$> inner op))
      postLeft (similar e ⟨ op ⟫   ) = lemmaˡ            (∣ˡ (<$> inner op)) (postLeft e)
      postLeft (tighter e ⟨ op ⟩ˡ r) = <$> expr e ⊛
                                         +-[] (∣ʳ (<$> inner op ⊛ expr r))
      postLeft (similar e ⟨ op ⟩ˡ r) = lemmaˡ (∣ʳ (<$> inner op ⊛ expr r)) (postLeft e)

      exprIn′ : ∀ assoc {s} (e : ExprIn p assoc) →
                (, e) ⊕ s ∈⟦ Grammar.prec p ⟧· Show.exprIn e s
      exprIn′ non      ⟪ op ⟫    = ∥ˡ (<$> inner op)
      exprIn′ non   (l ⟨ op ⟩ r) = ∥ʳ (∥ˡ (<$> expr l ⊛ inner op ⊛ expr r))
      exprIn′ right e            = ∥ʳ (∥ʳ (∥ˡ (preRight e)))
      exprIn′ left  e            = ∥ʳ (∥ʳ (∥ʳ (∥ˡ (postLeft e))))

    inner : ∀ {fix s ops} (i : Inner {fix} ops) →
            i ⊕ s ∈⟦ Grammar.inner ops ⟧· Show.inner i s
    inner {fix} {s} (_∙_ {arity} {op} op∈ops args) =
      helper op∈ops args
      where
      helper : {ops : List (∃ (Operator fix))}
               (op∈ : (arity , op) ∈ ops) (args : Vec (Expr g) arity) →
               let i = op∈ ∙ args in
               i ⊕ s ∈⟦ Grammar.inner ops ⟧· Show.inner i s
      helper (here refl) args = ∣ˡ (<$> inner′ (nameParts op) args)
      helper (there {x = _ , _} op∈) args =
        ∣ʳ (<$> helper op∈ args)

    inner′ : ∀ {arity s} (ns : Vec NamePart (1 + arity)) args →
             args ⊕ s ∈⟦ Grammar.expr between ns ⟧· Show.inner′ ns args s
    inner′ (n ∷ [])      []           = between-[]
    inner′ (n ∷ n′ ∷ ns) (arg ∷ args) =
      between-∷ (expr arg) (inner′ (n′ ∷ ns) args)

-- All generated strings are syntactically correct (but possibly
-- ambiguous). Note that this result implies that all
-- precedence-correct expressions are generated by the grammar.

correct : (e : Expr g) → e ∈ Grammar.expression · show e
correct e =
  Semantics.⊕-sound (Lib.Semantics-⊕.sound (Correctness.expr e))
