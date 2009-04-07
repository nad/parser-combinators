------------------------------------------------------------------------
-- Linearisation of mixfix operators
------------------------------------------------------------------------

open import StructurallyRecursiveDescentParsing.Mixfix.Expr as Expr

module StructurallyRecursiveDescentParsing.Mixfix.Show
         (g : PrecedenceGraph)
         where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; _∈_; here; there)
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; foldl; _∷ʳ_)
open import Data.Vec using (Vec; []; _∷_)
import Data.DifferenceList as DiffList
open DiffList using (DiffList; _++_)
              renaming (_∷_ to cons; [_] to singleton)
open import Data.Product using (∃; _,_; ,_)
open import Data.Function using (_∘_; flip)
open import Data.Maybe using (Maybe; nothing; just)
import Data.String as String
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)

open Expr.PrecedenceCorrect g
open import StructurallyRecursiveDescentParsing.Simplified
open import StructurallyRecursiveDescentParsing.Simplified.Semantics
  as Semantics
open import StructurallyRecursiveDescentParsing.Mixfix.Fixity
open import StructurallyRecursiveDescentParsing.Mixfix.Lib as Lib
import StructurallyRecursiveDescentParsing.Mixfix
private
  module Mixfix = StructurallyRecursiveDescentParsing.Mixfix g

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

  -- A generalisation of Mixfix.Prec.appˡ.

  appˡ′ : ∀ {p} → Outer p left → List⁺ (Outer p left → ExprIn p left) →
          ExprIn p left
  appˡ′ e fs = foldl (λ e f → f (similar e)) (λ f → f e) fs

  appˡ′-lemma : ∀ {p} (e : Outer p left) fs f →
                appˡ′ e (fs ∷ʳ f) ≡ f (similar (appˡ′ e fs))
  appˡ′-lemma e [ f′ ]    f = refl
  appˡ′-lemma e (f′ ∷ fs) f = appˡ′-lemma (similar (f′ e)) fs f

  mutual

    expr : ∀ {ps s} (e : Expr ps) →
           e ⊕ s ∈⟦ Mixfix.precs ps ⟧· Show.expr e s
    expr (here       ∙ e) = ∣ˡ (_ <$> exprIn e)
    expr (there x∈xs ∙ e) = ∣ʳ (_ <$> expr (x∈xs ∙ e))

    exprIn : ∀ {p assoc s} (e : ExprIn p assoc) →
             (, e) ⊕ s ∈⟦ Mixfix.prec p ⟧· Show.exprIn e s
    exprIn {precedence ops sucs} e = exprIn′ _ e
      where
      p        = precedence ops sucs
      module N = Mixfix.Prec ops sucs

      lemmaʳ : ∀ {f : Outer p right → ExprIn p right} {s e} {g : DiffList NamePart} →
               (∀ {s} → f ⊕ s ∈⟦ N.preRight ⟧· g s) →
                          e  ⊕ s ∈⟦ N.appʳ <$> N.preRight + ⊛ N.p↑ ⟧·    Show.exprIn e s →
               f (similar e) ⊕ s ∈⟦ N.appʳ <$> N.preRight + ⊛ N.p↑ ⟧· g (Show.exprIn e s)
      lemmaʳ f∈ (.N.appʳ <$> fs∈ ⊛ e∈) = N.appʳ <$> +-∷ f∈ fs∈ ⊛ e∈

      preRight : ∀ {s} (e : ExprIn p right) →
                 e ⊕ s ∈⟦ N.appʳ <$> N.preRight + ⊛ N.p↑ ⟧· Show.exprIn e s
      preRight (  ⟪ op ⟩  tighter e) = _ <$> +-[] (∣ˡ (⟪_⟩_ <$> inner op)) ⊛ expr e
      preRight (  ⟪ op ⟩  similar e) = lemmaʳ     (∣ˡ (⟪_⟩_ <$> inner op)) (preRight e)
      preRight (l ⟨ op ⟩ʳ tighter e) = _ <$> +-[] (∣ʳ (_⟨_⟩ʳ_ <$> expr l ⊛ inner op)) ⊛ expr e
      preRight (l ⟨ op ⟩ʳ similar e) = lemmaʳ     (∣ʳ (_⟨_⟩ʳ_ <$> expr l ⊛ inner op)) (preRight e)

      lemmaˡ : ∀ {f : Outer p left → ExprIn p left} {s e} {g : DiffList NamePart} →
               (∀ {s} → f ⊕ s ∈⟦ N.postLeft ⟧· g s) →
                          e  ⊕ g s ∈⟦ N.appˡ <$> N.p↑ ⊛ N.postLeft + ⟧· Show.exprIn e (g s) →
               f (similar e) ⊕   s ∈⟦ N.appˡ <$> N.p↑ ⊛ N.postLeft + ⟧· Show.exprIn e (g s)
      lemmaˡ {f} f∈ (_⊛_ {x = fs} (_<$>_ {x = e} .N.appˡ e∈) fs∈) =
        Lib.cast∈ (appˡ′-lemma (tighter e) fs f) (N.appˡ <$> e∈ ⊛ +-∷ʳ fs∈ f∈)

      postLeft : ∀ {s} (e : ExprIn p left) →
                 e ⊕ s ∈⟦ N.appˡ <$> N.p↑ ⊛ N.postLeft + ⟧· Show.exprIn e s
      postLeft (tighter e ⟨ op ⟫   ) = _ <$> expr e ⊛ +-[] (∣ˡ (flip _⟨_⟫ <$> inner op))
      postLeft (similar e ⟨ op ⟫   ) = lemmaˡ              (∣ˡ (flip _⟨_⟫ <$> inner op)) (postLeft e)
      postLeft (tighter e ⟨ op ⟩ˡ r) = _ <$> expr e ⊛
                                         +-[] (∣ʳ ((λ op r l → l ⟨ op ⟩ˡ r) <$> inner op ⊛ expr r))
      postLeft (similar e ⟨ op ⟩ˡ r) = lemmaˡ (∣ʳ ((λ op r l → l ⟨ op ⟩ˡ r) <$> inner op ⊛ expr r)) (postLeft e)

      exprIn′ : ∀ assoc {s} (e : ExprIn p assoc) →
                (, e) ⊕ s ∈⟦ Mixfix.prec p ⟧· Show.exprIn e s
      exprIn′ non      ⟪ op ⟫    = ∥ˡ (_ <$> inner op)
      exprIn′ non   (l ⟨ op ⟩ r) = ∥ʳ (∥ˡ (_ <$> expr l ⊛ inner op ⊛ expr r))
      exprIn′ right e            = ∥ʳ (∥ʳ (∥ˡ (preRight e)))
      exprIn′ left  e            = ∥ʳ (∥ʳ (∥ʳ (∥ˡ (postLeft e))))

    inner : ∀ {fix s ops} (i : Inner {fix} ops) →
            i ⊕ s ∈⟦ Mixfix.inner ops ⟧· Show.inner i s
    inner {fix} {s} (_∙_ {arity} {op} op∈ops args) =
      helper op∈ops args
      where
      helper : {ops : List (∃ (Operator fix))}
               (op∈ : (arity , op) ∈ ops) (args : Vec (Expr g) arity) →
               let i = op∈ ∙ args in
               i ⊕ s ∈⟦ Mixfix.inner ops ⟧· Show.inner i s
      helper here args = ∣ˡ (_ <$> inner′ (nameParts op) args)
      helper (there {y = _ , _} op∈) args =
        ∣ʳ (_ <$> helper op∈ args)

    inner′ : ∀ {arity s} (ns : Vec NamePart (1 + arity)) args →
             args ⊕ s ∈⟦ Mixfix.expr between ns ⟧· Show.inner′ ns args s
    inner′ (n ∷ [])      []           = between-[]
    inner′ (n ∷ n′ ∷ ns) (arg ∷ args) =
      between-∷ (expr arg) (inner′ (n′ ∷ ns) args)

-- All generated strings are syntactically correct (but possibly
-- ambiguous). Note that this result implies that all
-- precedence-correct expressions are generated by the grammar.

correct : (e : Expr g) → e ∈ Mixfix.expression · show e
correct e = Semantics.⊕-sound (Lib.sound (Correctness.expr e))
