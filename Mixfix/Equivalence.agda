------------------------------------------------------------------------
-- The two methods used to specify the grammars are (language)
-- equivalent (for acyclic graphs)
------------------------------------------------------------------------

open import Mixfix.Expr
open import Mixfix.Acyclic.PrecedenceGraph
  using (acyclic; precedence)

module Mixfix.Equivalence
  (g : PrecedenceGraphInterface.PrecedenceGraph acyclic)
  where

open import Function using (_∘_)
open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
open import Data.Vec using (Vec; []; _∷_)
open import Level using (lift)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics hiding (_≅_)
open import TotalParserCombinators.Semantics.Continuation as ContSem
import StructurallyRecursiveDescentParsing.Simplified as Simplified
import StructurallyRecursiveDescentParsing.Simplified.Semantics as SSem

open import Mixfix.Fixity
open import Mixfix.Operator
import Mixfix.Acyclic.Grammar
import Mixfix.Cyclic.Grammar
import Mixfix.Acyclic.Lemma
private
  module Acyclic = Mixfix.Acyclic.Grammar        g
  module ALemma  = Mixfix.Acyclic.Lemma          g
  module Cyclic  = Mixfix.Cyclic.Grammar acyclic g
open import Mixfix.Acyclic.Lib as ALib
open ALib.Semantics-⊕ renaming (_⊕_∈⟦_⟧·_ to _⊕_∈⟦_⟧A·_)
open import Mixfix.Cyclic.Lib as CLib renaming (⟦_⟧ to ⟦_⟧C)
open CLib.Semantics-⊕ renaming (_⊕_∈⟦_⟧·_ to _⊕_∈⟦_⟧C·_)

open PrecedenceCorrect acyclic g

⟦_⟧A : ∀ {R} → ALib.ParserProg R → Parser NamePart R []
⟦ p ⟧A = Simplified.⟦_⟧ (ALib.⟦_⟧ p)

module AcyclicToCyclic where

  mutual

    precs : ∀ ps {s s′ e} →
            e ⊕ s′ ∈⟦ Acyclic.precs ps ⟧A· s →
            e ⊕ s′ ∈⟦  Cyclic.precs ps ⟧C· s
    precs []       ()
    precs (p ∷ ps) (∣ˡ (<$> e∈p))  = ∣ˡ (<$> prec  p  e∈p)
    precs (p ∷ ps) (∣ʳ (<$> e∈ps)) = ∣ʳ (<$> precs ps e∈ps)

    prec : ∀ p {s s′ e} →
           e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s →
           e ⊕ s′ ∈⟦  Cyclic.prec p ⟧C· s
    prec (precedence ops sucs) e∈ = prec′ e∈
      where
      p = precedence ops sucs

      module A = Acyclic.Prec ops sucs
      module C =  Cyclic.Prec p

      preRight : ∀ {s s′ f} →
                 f ⊕ s′ ∈⟦ A.preRight ⟧A· s →
                 f ⊕ s′ ∈⟦ C.preRight ⟧C· s
      preRight (∣ˡ (<$>      i∈)) = ∣ˡ (<$>              inner _ i∈)
      preRight (∣ʳ (<$> ↑∈ ⊛ i∈)) = ∣ʳ (<$> precs _ ↑∈ ⊛ inner _ i∈)

      preRight⁺ : ∀ {s s′ s″ fs e} →
                  fs          ⊕ s′ ∈⟦ A.preRight +       ⟧A· s  →
                  e           ⊕ s″ ∈⟦ Acyclic.precs sucs ⟧A· s′ →
                  A.appʳ fs e ⊕ s″ ∈⟦ C.preRight⁺        ⟧C· s
      preRight⁺ {s′ = s′} {s″ = s″} {e = e} fs∈ ↑∈ =
        pr fs∈ refl refl refl
        where
        pr : ∀ {R′ s fs fs′} {p′ : ALib.ParserProg R′} →
             fs′ ⊕ s′ ∈⟦ p′ ⟧A· s →
             R′  ≡ List⁺ (Outer p right → ExprIn p right) →
             fs′ ≅ fs →
             p′  ≅ A.preRight ALib.+ →
             A.appʳ fs e ⊕ s″ ∈⟦ C.preRight⁺ ⟧C· s
        pr fs∈             R′≡ fs′≅ p′≅ with ALib.no-confusion R′≡ p′≅
        pr (+-[] f∈)       _   refl _ | refl , refl = preRight f∈ ⊛∞ ∣ʳ (<$> precs _ ↑∈)
        pr (+-∷ f∈ fs∈)    _   refl _ | refl , refl = preRight f∈ ⊛∞ ∣ˡ (<$> preRight⁺ fs∈ ↑∈)
        pr (∣ˡ _)          _   _    _ | lift ()
        pr (∣ʳ _)          _   _    _ | lift ()
        pr (_ ⊛ _)         _   _    _ | lift ()
        pr (<$> _)         _   _    _ | lift ()
        pr between-[]      _   _    _ | lift ()
        pr (between-∷ _ _) _   _    _ | lift ()
        pr (∥ˡ _)          _   _    _ | lift ()
        pr (∥ʳ _)          _   _    _ | lift ()

      postLeft : ∀ {s s′ f} →
                 f ⊕ s′ ∈⟦ A.postLeft ⟧A· s →
                 f ⊕ s′ ∈⟦ C.postLeft ⟧C· s
      postLeft (∣ˡ (<$> i∈     )) = ∣ˡ (<$> inner _ i∈)
      postLeft (∣ʳ (<$> i∈ ⊛ ↑∈)) = ∣ʳ (<$> inner _ i∈ ⊛ precs _ ↑∈)

      postLeft⁺ : ∀ {s s′ s″ o fs} →
                  o                ⊕ s′ ∈⟦ similar <$> C.postLeft⁺
                                         ∣ tighter <$> C.p↑ ⟧C· s  →
                  fs               ⊕ s″ ∈⟦ A.postLeft +     ⟧A· s′ →
                  ALemma.appˡ o fs ⊕ s″ ∈⟦ C.postLeft⁺      ⟧C· s
      postLeft⁺ o∈ fs∈ = pl o∈ fs∈ refl refl refl
        where
        pl : ∀ {R′ s s′ s″ o fs fs′} {p′ : ALib.ParserProg R′} →
             o   ⊕ s′ ∈⟦ similar <$> C.postLeft⁺
                       ∣ tighter <$> C.p↑ ⟧C· s  →
             fs′ ⊕ s″ ∈⟦ p′               ⟧A· s′ →
             R′  ≡ List⁺ (Outer p left → ExprIn p left) →
             fs′ ≅ fs →
             p′  ≅ A.postLeft ALib.+ →
             ALemma.appˡ o fs ⊕ s″ ∈⟦ C.postLeft⁺ ⟧C· s
        pl o∈ fs∈             R′≡ fs′≅ p′≅ with ALib.no-confusion R′≡ p′≅
        pl o∈ (+-[] f∈)       _   refl _   | refl , refl =                     <$> o∈ ⊛∞ postLeft f∈
        pl o∈ (+-∷ f∈ fs∈)    _   refl _   | refl , refl = postLeft⁺ (∣ˡ (<$> (<$> o∈ ⊛∞ postLeft f∈))) fs∈
        pl _  (∣ˡ _)          _   _    _   | lift ()
        pl _  (∣ʳ _)          _   _    _   | lift ()
        pl _  (_ ⊛ _)         _   _    _   | lift ()
        pl _  (<$> _)         _   _    _   | lift ()
        pl _  between-[]      _   _    _   | lift ()
        pl _  (between-∷ _ _) _   _    _   | lift ()
        pl _  (∥ˡ _)          _   _    _   | lift ()
        pl _  (∥ʳ _)          _   _    _   | lift ()

      prec′ : ∀ {s s′} {e : ∃ (ExprIn p)} →
              e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s →
              e ⊕ s′ ∈⟦  Cyclic.prec p ⟧C· s
      prec′ {s′ = s′} e∈ = pr₁ e∈ refl refl refl
        where
        pr₄ : ∀ {R′ s e′} {e : ∃ (ExprIn p)} {p′ : ALib.ParserProg R′} →
              e′ ⊕ s′ ∈⟦ p′ ⟧A· s →
              R′ ≡ ∃ (ExprIn p) →
              e′ ≅ e →
              p′ ≅   A.appˡ <$>  A.p↑ ⊛ A.postLeft +
                   ∥ fail →
              e ⊕ s′ ∈⟦ Cyclic.prec p ⟧C· s
        pr₄ e∈                  R′≡ e′≅  p′≅ with ALib.no-confusion R′≡ p′≅
        pr₄ (∥ˡ (<$> ↑∈ ⊛ fs∈)) _   refl _   | refl , refl , refl , refl , refl = ∥ʳ (∥ʳ (∥ʳ (∥ˡ (postLeft⁺ (∣ʳ (<$> precs _ ↑∈)) fs∈))))
        pr₄ (∥ʳ ())             _   refl _   | refl , refl , refl , refl , refl
        pr₄ (∣ˡ _)              _   _    _   | lift ()
        pr₄ (∣ʳ _)              _   _    _   | lift ()
        pr₄ (_ ⊛ _)             _   _    _   | lift ()
        pr₄ (<$> _)             _   _    _   | lift ()
        pr₄ (+-[] _)            _   _    _   | lift ()
        pr₄ (+-∷ _ _)           _   _    _   | lift ()
        pr₄ between-[]          _   _    _   | lift ()
        pr₄ (between-∷ _ _)     _   _    _   | lift ()

        pr₃ : ∀ {R′ s e′} {e : ∃ (ExprIn p)} {p′ : ALib.ParserProg R′} →
              e′ ⊕ s′ ∈⟦ p′ ⟧A· s →
              R′ ≡ ∃ (ExprIn p) →
              e′ ≅ e →
              p′ ≅   A.appʳ <$>         A.preRight +   ⊛ A.p↑
                   ∥ A.appˡ <$>  A.p↑ ⊛ A.postLeft +
                   ∥ fail →
              e ⊕ s′ ∈⟦ Cyclic.prec p ⟧C· s
        pr₃ e∈                  R′≡ e′≅  p′≅ with ALib.no-confusion R′≡ p′≅
        pr₃ (∥ˡ (<$> fs∈ ⊛ ↑∈)) _   refl _   | refl , refl , refl , refl , refl = ∥ʳ (∥ʳ (∥ˡ (preRight⁺ fs∈ ↑∈)))
        pr₃ (∥ʳ e∈)             _   refl _   | refl , refl , refl , refl , refl = pr₄ e∈ refl refl refl
        pr₃ (∣ˡ _)              _   _    _   | lift ()
        pr₃ (∣ʳ _)              _   _    _   | lift ()
        pr₃ (_ ⊛ _)             _   _    _   | lift ()
        pr₃ (<$> _)             _   _    _   | lift ()
        pr₃ (+-[] _)            _   _    _   | lift ()
        pr₃ (+-∷ _ _)           _   _    _   | lift ()
        pr₃ between-[]          _   _    _   | lift ()
        pr₃ (between-∷ _ _)     _   _    _   | lift ()

        pr₂ : ∀ {R′ s e′} {e : ∃ (ExprIn p)} {p′ : ALib.ParserProg R′} →
              e′ ⊕ s′ ∈⟦ p′ ⟧A· s →
              R′ ≡ ∃ (ExprIn p) →
              e′ ≅ e →
              p′ ≅   _⟨_⟩_  <$>  A.p↑ ⊛ A.[ infx non ] ⊛ A.p↑
                   ∥ A.appʳ <$>         A.preRight +   ⊛ A.p↑
                   ∥ A.appˡ <$>  A.p↑ ⊛ A.postLeft +
                   ∥ fail →
              e ⊕ s′ ∈⟦ Cyclic.prec p ⟧C· s
        pr₂ e∈                        R′≡ e′≅  p′≅ with ALib.no-confusion R′≡ p′≅
        pr₂ (∥ˡ (<$> ↑₁∈ ⊛ i∈ ⊛ ↑₂∈)) _   refl _   | refl , refl , refl , refl , refl = ∥ʳ (∥ˡ (<$> precs _ ↑₁∈ ⊛ inner _ i∈ ⊛∞ precs _ ↑₂∈ ))
        pr₂ (∥ʳ e∈)                   _   refl _   | refl , refl , refl , refl , refl = pr₃ e∈ refl refl refl
        pr₂ (∣ˡ _)                    _   _    _   | lift ()
        pr₂ (∣ʳ _)                    _   _    _   | lift ()
        pr₂ (_ ⊛ _)                   _   _    _   | lift ()
        pr₂ (<$> _)                   _   _    _   | lift ()
        pr₂ (+-[] _)                  _   _    _   | lift ()
        pr₂ (+-∷ _ _)                 _   _    _   | lift ()
        pr₂ between-[]                _   _    _   | lift ()
        pr₂ (between-∷ _ _)           _   _    _   | lift ()

        pr₁ : ∀ {R′ s e′} {e : ∃ (ExprIn p)} {p′ : ALib.ParserProg R′} →
              e′ ⊕ s′ ∈⟦ p′ ⟧A· s →
              R′ ≡ ∃ (ExprIn p) →
              e′ ≅ e →
              p′ ≅ Acyclic.prec p →
              e ⊕ s′ ∈⟦ Cyclic.prec p ⟧C· s
        pr₁ e∈              R′≡ e′≅  p′≅ with ALib.no-confusion R′≡ p′≅
        pr₁ (∥ˡ (<$> i∈))   _   refl _   | refl , refl , refl , refl , refl = ∥ˡ (<$> inner _ i∈)
        pr₁ (∥ʳ e∈)         _   refl _   | refl , refl , refl , refl , refl = pr₂ e∈ refl refl refl
        pr₁ (∣ˡ _)          _   _    _   | lift ()
        pr₁ (∣ʳ _)          _   _    _   | lift ()
        pr₁ (_ ⊛ _)         _   _    _   | lift ()
        pr₁ (<$> _)         _   _    _   | lift ()
        pr₁ (+-[] _)        _   _    _   | lift ()
        pr₁ (+-∷ _ _)       _   _    _   | lift ()
        pr₁ between-[]      _   _    _   | lift ()
        pr₁ (between-∷ _ _) _   _    _   | lift ()

    inner : ∀ {fix} (ops : List (∃ (Operator fix))) {s s′ i} →
            i ⊕ s′ ∈⟦ Acyclic.inner ops ⟧A· s →
            i ⊕ s′ ∈⟦  Cyclic.inner ops ⟧C· s
    inner []               ()
    inner ((_ , op) ∷ ops) (∣ˡ (<$> i∈)) = ∣ˡ (<$> inner′ i∈)
    inner ((_ , op) ∷ ops) (∣ʳ (<$> i∈)) = ∣ʳ (<$> inner ops i∈)

    inner′ : ∀ {arity} {ns : Vec NamePart (1 + arity)} {s s′ i} →
             i ⊕ s′ ∈⟦ Acyclic.expr between ns ⟧A· s →
             i ⊕ s′ ∈⟦  Cyclic.expr between ns ⟧C· s
    inner′ i∈ = in′ i∈ refl refl refl
      where
      in′ : ∀ {arity} {ns : Vec NamePart (1 + arity)} {s s′ i R′ i′}
              {p′ : ALib.ParserProg R′} →
            i′ ⊕ s′ ∈⟦ p′ ⟧A· s →
            R′ ≡ Vec (Expr g) arity →
            i′ ≅ i →
            p′ ≅ Acyclic.expr ALib.between ns →
            i ⊕ s′ ∈⟦ Cyclic.expr between ns ⟧C· s
      in′ es∈                R′≡ i′≅  p′≅ with ALib.no-confusion R′≡ p′≅
      in′ between-[]         _   refl _   | refl , refl , refl , refl = between-[]
      in′ (between-∷ e∈ es∈) _   refl _   | refl , refl , refl , refl = between-∷ (precs g e∈) (inner′ es∈)
      in′ (∣ˡ _)             _   _    _   | lift ()
      in′ (∣ʳ _)             _   _    _   | lift ()
      in′ (_ ⊛ _)            _   _    _   | lift ()
      in′ (<$> _)            _   _    _   | lift ()
      in′ (+-[] _)           _   _    _   | lift ()
      in′ (+-∷ _ _)          _   _    _   | lift ()
      in′ (∥ˡ _)             _   _    _   | lift ()
      in′ (∥ʳ _)             _   _    _   | lift ()

module CyclicToAcyclic where

  mutual

    precs : ∀ ps {s s′ e} →
            e ⊕ s′ ∈⟦  Cyclic.precs ps ⟧C· s →
            e ⊕ s′ ∈⟦ Acyclic.precs ps ⟧A· s
    precs []       ()
    precs (p ∷ ps) (∣ˡ (<$> e∈p))  = ∣ˡ (<$> prec  p  e∈p)
    precs (p ∷ ps) (∣ʳ (<$> e∈ps)) = ∣ʳ (<$> precs ps e∈ps)

    prec : ∀ p {s s′ e} →
           e ⊕ s′ ∈⟦  Cyclic.prec p ⟧C· s →
           e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s
    prec (precedence ops sucs) e∈ = prec′ e∈
      where
      p = precedence ops sucs

      module A = Acyclic.Prec ops sucs
      module C =  Cyclic.Prec p

      preRight : ∀ {s s′ f} →
                 f ⊕ s′ ∈⟦ C.preRight ⟧C· s →
                 f ⊕ s′ ∈⟦ A.preRight ⟧A· s
      preRight (∣ˡ (<$>      i∈)) = ∣ˡ (<$>              inner _ i∈)
      preRight (∣ʳ (<$> ↑∈ ⊛ i∈)) = ∣ʳ (<$> precs _ ↑∈ ⊛ inner _ i∈)

      preRight⁺ : ∀ {s s′ e} →
                  e ⊕ s′ ∈⟦ C.preRight⁺                    ⟧C· s →
                  e ⊕ s′ ∈⟦ A.appʳ <$> A.preRight + ⊛ A.p↑ ⟧A· s
      preRight⁺ (f∈ ⊛∞ ∣ˡ (<$> pre∈)) with preRight⁺ pre∈
      preRight⁺ (f∈ ⊛∞ ∣ˡ (<$> pre∈)) | <$> fs∈ ⊛ ↑∈ = <$> +-∷  (preRight f∈) fs∈ ⊛ ↑∈
      preRight⁺ (f∈ ⊛∞ ∣ʳ (<$> ↑∈)  ) =                <$> +-[] (preRight f∈)     ⊛ precs _ ↑∈

      postLeft : ∀ {s s′ f} →
                 f ⊕ s′ ∈⟦ C.postLeft ⟧C· s →
                 f ⊕ s′ ∈⟦ A.postLeft ⟧A· s
      postLeft (∣ˡ (<$> i∈     )) = ∣ˡ (<$> inner _ i∈)
      postLeft (∣ʳ (<$> i∈ ⊛ ↑∈)) = ∣ʳ (<$> inner _ i∈ ⊛ precs _ ↑∈)

      postLeft⁺ : ∀ {s s′ e} →
                  e ⊕ s′ ∈⟦ C.postLeft⁺                    ⟧C· s →
                  e ⊕ s′ ∈⟦ A.appˡ <$> A.p↑ ⊛ A.postLeft + ⟧A· s
      postLeft⁺ (<$> ∣ˡ (<$> post∈) ⊛∞ f∈) with postLeft⁺ post∈
      postLeft⁺ (<$> ∣ˡ (<$> post∈) ⊛∞ f∈)
        | _⊛_ {x = fs} (<$> ↑∈) fs∈ = AS.cast∈ (ALemma.appˡ-∷ʳ _ fs _) (
                                             <$>         ↑∈ ⊛ AS.+-∷ʳ fs∈ (postLeft f∈))
        where module AS = ALib.Semantics-⊕
      postLeft⁺ (<$> ∣ʳ (<$> ↑∈)    ⊛∞ f∈) = <$> precs _ ↑∈ ⊛    +-[]     (postLeft f∈)

      prec′ : ∀ {s s′} {e : ∃ (ExprIn p)} →
              e ⊕ s′ ∈⟦  Cyclic.prec p ⟧C· s →
              e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s
      prec′ {s′ = s′} e∈ = pr₁ e∈ refl refl refl
        where
        pr₄ : ∀ {R′ s e′} {e : ∃ (ExprIn p)} {p′ : CLib.ParserProg R′} →
              e′ ⊕ s′ ∈⟦ p′ ⟧C· s →
              R′ ≡ ∃ (ExprIn p) →
              e′ ≅ e →
              p′ ≅ C.postLeft⁺ ∥ fail →
              e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s
        pr₄ e∈              R′≡ e′≅  p′≅ with CLib.no-confusion R′≡ p′≅
        pr₄ (∥ˡ post∈)      _   refl _   | refl , refl , refl , refl , refl = ∥ʳ (∥ʳ (∥ʳ (∥ˡ (postLeft⁺ post∈))))
        pr₄ (∥ʳ ())         _   refl _   | refl , refl , refl , refl , refl
        pr₄ (∣ˡ _)          _   _    _   | lift ()
        pr₄ (∣ʳ _)          _   _    _   | lift ()
        pr₄ (_ ⊛ _)         _   _    _   | lift ()
        pr₄ (_ ⊛∞ _)        _   _    _   | lift ()
        pr₄ (<$> _)         _   _    _   | lift ()
        pr₄ (+-[] _)        _   _    _   | lift ()
        pr₄ (+-∷ _ _)       _   _    _   | lift ()
        pr₄ between-[]      _   _    _   | lift ()
        pr₄ (between-∷ _ _) _   _    _   | lift ()

        pr₃ : ∀ {R′ s e′} {e : ∃ (ExprIn p)} {p′ : CLib.ParserProg R′} →
              e′ ⊕ s′ ∈⟦ p′ ⟧C· s →
              R′ ≡ ∃ (ExprIn p) →
              e′ ≅ e →
              p′ ≅ C.preRight⁺ ∥ C.postLeft⁺ ∥ fail →
              e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s
        pr₃ e∈              R′≡ e′≅  p′≅ with CLib.no-confusion R′≡ p′≅
        pr₃ (∥ˡ pre∈)       _   refl _   | refl , refl , refl , refl , refl = ∥ʳ (∥ʳ (∥ˡ (preRight⁺ pre∈)))
        pr₃ (∥ʳ e∈)         _   refl _   | refl , refl , refl , refl , refl = pr₄ e∈ refl refl refl
        pr₃ (∣ˡ _)          _   _    _   | lift ()
        pr₃ (∣ʳ _)          _   _    _   | lift ()
        pr₃ (_ ⊛ _)         _   _    _   | lift ()
        pr₃ (_ ⊛∞ _)        _   _    _   | lift ()
        pr₃ (<$> _)         _   _    _   | lift ()
        pr₃ (+-[] _)        _   _    _   | lift ()
        pr₃ (+-∷ _ _)       _   _    _   | lift ()
        pr₃ between-[]      _   _    _   | lift ()
        pr₃ (between-∷ _ _) _   _    _   | lift ()

        pr₂ : ∀ {R′ s e′} {e : ∃ (ExprIn p)} {p′ : CLib.ParserProg R′} →
              e′ ⊕ s′ ∈⟦ p′ ⟧C· s →
              R′ ≡ ∃ (ExprIn p) →
              e′ ≅ e →
              p′ ≅ C.nonAssoc ∥ C.preRight⁺ ∥ C.postLeft⁺ ∥ fail →
              e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s
        pr₂ e∈                         R′≡ e′≅  p′≅ with CLib.no-confusion R′≡ p′≅
        pr₂ (∥ˡ (<$> ↑₁∈ ⊛ i∈ ⊛∞ ↑₂∈)) _   refl _   | refl , refl , refl , refl , refl = ∥ʳ (∥ˡ (<$> precs _ ↑₁∈ ⊛ inner _ i∈ ⊛ precs _ ↑₂∈ ))
        pr₂ (∥ʳ e∈)                    _   refl _   | refl , refl , refl , refl , refl = pr₃ e∈ refl refl refl
        pr₂ (∣ˡ _)                     _   _    _   | lift ()
        pr₂ (∣ʳ _)                     _   _    _   | lift ()
        pr₂ (_ ⊛ _)                    _   _    _   | lift ()
        pr₂ (_ ⊛∞ _)                   _   _    _   | lift ()
        pr₂ (<$> _)                    _   _    _   | lift ()
        pr₂ (+-[] _)                   _   _    _   | lift ()
        pr₂ (+-∷ _ _)                  _   _    _   | lift ()
        pr₂ between-[]                 _   _    _   | lift ()
        pr₂ (between-∷ _ _)            _   _    _   | lift ()

        pr₁ : ∀ {R′ s e′} {e : ∃ (ExprIn p)} {p′ : CLib.ParserProg R′} →
              e′ ⊕ s′ ∈⟦ p′ ⟧C· s →
              R′ ≡ ∃ (ExprIn p) →
              e′ ≅ e →
              p′ ≅ Cyclic.prec p →
              e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s
        pr₁ e∈              R′≡ e′≅  p′≅ with CLib.no-confusion R′≡ p′≅
        pr₁ (∥ˡ (<$> i∈))   _   refl _   | refl , refl , refl , refl , refl = ∥ˡ (<$> inner _ i∈)
        pr₁ (∥ʳ e∈)         _   refl _   | refl , refl , refl , refl , refl = pr₂ e∈ refl refl refl
        pr₁ (∣ˡ _)          _   _    _   | lift ()
        pr₁ (∣ʳ _)          _   _    _   | lift ()
        pr₁ (_ ⊛ _)         _   _    _   | lift ()
        pr₁ (_ ⊛∞ _)        _   _    _   | lift ()
        pr₁ (<$> _)         _   _    _   | lift ()
        pr₁ (+-[] _)        _   _    _   | lift ()
        pr₁ (+-∷ _ _)       _   _    _   | lift ()
        pr₁ between-[]      _   _    _   | lift ()
        pr₁ (between-∷ _ _) _   _    _   | lift ()

    inner : ∀ {fix} (ops : List (∃ (Operator fix))) {s s′ i} →
            i ⊕ s′ ∈⟦  Cyclic.inner ops ⟧C· s →
            i ⊕ s′ ∈⟦ Acyclic.inner ops ⟧A· s
    inner []               ()
    inner ((_ , op) ∷ ops) (∣ˡ (<$> i∈)) = ∣ˡ (<$> inner′ i∈)
    inner ((_ , op) ∷ ops) (∣ʳ (<$> i∈)) = ∣ʳ (<$> inner ops i∈)

    inner′ : ∀ {arity} {ns : Vec NamePart (1 + arity)} {s s′ i} →
             i ⊕ s′ ∈⟦  Cyclic.expr between ns ⟧C· s →
             i ⊕ s′ ∈⟦ Acyclic.expr between ns ⟧A· s
    inner′ i∈ = in′ i∈ refl refl refl
      where
      in′ : ∀ {arity} {ns : Vec NamePart (1 + arity)} {s s′ i R′ i′}
              {p′ : CLib.ParserProg R′} →
            i′ ⊕ s′ ∈⟦ p′ ⟧C· s →
            R′ ≡ Vec (Expr g) arity →
            i′ ≅ i →
            p′ ≅ Cyclic.expr CLib.between ns →
            i ⊕ s′ ∈⟦ Acyclic.expr between ns ⟧A· s
      in′ es∈                R′≡ i′≅  p′≅ with CLib.no-confusion R′≡ p′≅
      in′ between-[]         _   refl _   | refl , refl , refl , refl = between-[]
      in′ (between-∷ e∈ es∈) _   refl _   | refl , refl , refl , refl = between-∷ (precs g e∈) (inner′ es∈)
      in′ (∣ˡ _)             _   _    _   | lift ()
      in′ (∣ʳ _)             _   _    _   | lift ()
      in′ (_ ⊛ _)            _   _    _   | lift ()
      in′ (_ ⊛∞ _)           _   _    _   | lift ()
      in′ (<$> _)            _   _    _   | lift ()
      in′ (+-[] _)           _   _    _   | lift ()
      in′ (+-∷ _ _)          _   _    _   | lift ()
      in′ (∥ˡ _)             _   _    _   | lift ()
      in′ (∥ʳ _)             _   _    _   | lift ()

acyclicToCyclic
  : ∀ {e s} → e ∈ Simplified.⟦_⟧ Acyclic.expression · s →
              e ∈                 Cyclic.expression · s
acyclicToCyclic =
  ContSem.sound               ∘
  CLib.Semantics-⊕.sound      ∘
  AcyclicToCyclic.precs _     ∘
  ALib.Semantics-⊕.complete _ ∘
  SSem.⊕-complete             ∘
  SSem.complete _

cyclicToAcyclic
  : ∀ {e s} → e ∈                 Cyclic.expression · s →
              e ∈ Simplified.⟦_⟧ Acyclic.expression · s
cyclicToAcyclic =
  SSem.sound                  ∘
  SSem.⊕-sound                ∘
  ALib.Semantics-⊕.sound      ∘
  CyclicToAcyclic.precs _     ∘
  CLib.Semantics-⊕.complete _ ∘
  ContSem.complete
