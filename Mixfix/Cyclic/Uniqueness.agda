------------------------------------------------------------------------
-- An expression can be derived from at most one string
------------------------------------------------------------------------

open import Mixfix.Expr

module Mixfix.Cyclic.Uniqueness
         (i : PrecedenceGraphInterface)
         (g : PrecedenceGraphInterface.PrecedenceGraph i)
         where

open import Coinduction using (♭)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.List.Any using (here)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (∃; _,_; ,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (lift)
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_)

open PrecedenceCorrect i g
open import TotalParserCombinators.Semantics hiding (_≅_)
open import Mixfix.Fixity
open import Mixfix.Operator
open import Mixfix.Cyclic.Lib as Lib
open Lib.Semantics
import Mixfix.Cyclic.Grammar
private module Grammar = Mixfix.Cyclic.Grammar i g

module Unique where

 data _≋_ {A₁ : Set} {x₁ : A₁} {s₁ p₁} (∈ : x₁ ∈⟦ p₁ ⟧· s₁) :
        ∀ {A₂ : Set} {x₂ : A₂} {s₂ p₂} →    x₂ ∈⟦ p₂ ⟧· s₂ → Set₁ where
   refl : ∈ ≋ ∈

 mutual

  precs : ∀ ps {s₁ s₂} {e₁ e₂ : Expr ps}
          (∈₁ : e₁ ∈⟦ Grammar.precs ps ⟧· s₁)
          (∈₂ : e₂ ∈⟦ Grammar.precs ps ⟧· s₂) →
          e₁ ≡ e₂ → ∈₁ ≋ ∈₂
  precs [] () () _
  precs (p ∷ ps) (∣ʳ (<$>_ {x = ( _ ∙  _)}  ∈₁))
                 (∣ʳ (<$>_ {x = (._ ∙ ._)}  ∈₂)) refl with precs ps ∈₁ ∈₂ refl
  precs (p ∷ ps) (∣ʳ (<$>_ {x = ( _ ∙  _)}  ∈₁))
                 (∣ʳ (<$>_ {x = (._ ∙ ._)} .∈₁)) refl | refl = refl
  precs (p ∷ ps) (∣ˡ (<$> ∈₁)) (∣ʳ (<$>_ {x = _ ∙ _} ∈₂)) ()
  precs (p ∷ ps) (∣ʳ (<$>_ {x = _ ∙ _} ∈₁)) (∣ˡ (<$> ∈₂)) ()
  precs (p ∷ ps) (∣ˡ (<$>_ {x = e₁} ∈₁)) (∣ˡ (<$>_ {x = e₂} ∈₂)) eq =
    helper (lemma₁ eq) (lemma₂ eq) ∈₁ ∈₂
    where
    lemma₁ : ∀ {assoc₁ assoc₂}
               {e₁ : ExprIn p assoc₁} {e₂ : ExprIn p assoc₂} →
             (Expr._∙_ (here {xs = ps} refl) e₁) ≡ (here refl ∙ e₂) →
             assoc₁ ≡ assoc₂
    lemma₁ refl = refl

    lemma₂ : ∀ {assoc₁ assoc₂}
               {e₁ : ExprIn p assoc₁} {e₂ : ExprIn p assoc₂} →
             (Expr._∙_ (here {xs = ps} refl) e₁) ≡ (here refl ∙ e₂) →
             e₁ ≅ e₂
    lemma₂ refl = refl

    helper : ∀ {assoc₁ assoc₂ s₁ s₂}
             {e₁ : ExprIn p assoc₁} {e₂ : ExprIn p assoc₂} →
             assoc₁ ≡ assoc₂ → e₁ ≅ e₂ →
             (∈₁ : (, e₁) ∈⟦ Grammar.prec p ⟧· s₁) →
             (∈₂ : (, e₂) ∈⟦ Grammar.prec p ⟧· s₂) →
             ∣ˡ {p₁ = (λ e → here refl ∙ proj₂ e) <$> Grammar.prec p}
                {p₂ = weakenE <$> Grammar.precs ps} (<$> ∈₁) ≋
             ∣ˡ {p₁ = (λ e → here refl ∙ proj₂ e) <$> Grammar.prec p}
                {p₂ = weakenE <$> Grammar.precs ps} (<$> ∈₂)
    helper refl refl ∈₁ ∈₂ with prec ∈₁ ∈₂
    helper refl refl ∈ .∈  | refl = refl

  prec : ∀ {p assoc s₁ s₂} {e : ExprIn p assoc}
         (∈₁ : (, e) ∈⟦ Grammar.prec p ⟧· s₁)
         (∈₂ : (, e) ∈⟦ Grammar.prec p ⟧· s₂) →
         ∈₁ ≋ ∈₂
  prec {p} ∈₁′ ∈₂′ = prec′ ∈₁′ ∈₂′ refl
    where
    module P = Grammar.Prec p

    preRight⁺ : ∀ {s₁ s₂} {e₁ e₂ : ExprIn p right}
                (∈₁ : e₁ ∈⟦ P.preRight⁺ ⟧· s₁)
                (∈₂ : e₂ ∈⟦ P.preRight⁺ ⟧· s₂) →
                e₁ ≡ e₂ → ∈₁ ≋ ∈₂
    preRight⁺ (∣ˡ (<$>  ∈₁)       ⊛∞ ∣ˡ (<$>  ∈₂))
              (∣ˡ (<$> ∈₁′)       ⊛∞ ∣ˡ (<$> ∈₂′)) refl with inner _   ∈₁ ∈₁′ refl | preRight⁺ ∈₂ ∈₂′ refl
    preRight⁺ (∣ˡ (<$>  ∈₁)       ⊛∞ ∣ˡ (<$>  ∈₂))
              (∣ˡ (<$> .∈₁)       ⊛∞ ∣ˡ (<$> .∈₂)) refl | refl | refl = refl
    preRight⁺ (∣ˡ (<$>  ∈₁)       ⊛∞ ∣ʳ (<$>  ∈₂))
              (∣ˡ (<$> ∈₁′)       ⊛∞ ∣ʳ (<$> ∈₂′)) refl with inner _ ∈₁ ∈₁′ refl | precs _ ∈₂ ∈₂′ refl
    preRight⁺ (∣ˡ (<$>  ∈₁)       ⊛∞ ∣ʳ (<$>  ∈₂))
              (∣ˡ (<$> .∈₁)       ⊛∞ ∣ʳ (<$> .∈₂)) refl | refl | refl = refl
    preRight⁺ (∣ʳ (<$>  ∈₁ ⊛  ∈₃) ⊛∞ ∣ˡ (<$>  ∈₂))
              (∣ʳ (<$> ∈₁′ ⊛ ∈₃′) ⊛∞ ∣ˡ (<$> ∈₂′)) refl with precs _   ∈₁ ∈₁′ refl | preRight⁺ ∈₂ ∈₂′ refl | inner _   ∈₃ ∈₃′ refl
    preRight⁺ (∣ʳ (<$>  ∈₁ ⊛  ∈₃) ⊛∞ ∣ˡ (<$>  ∈₂))
              (∣ʳ (<$> .∈₁ ⊛ .∈₃) ⊛∞ ∣ˡ (<$> .∈₂)) refl | refl | refl | refl = refl
    preRight⁺ (∣ʳ (<$>  ∈₁ ⊛  ∈₃) ⊛∞ ∣ʳ (<$>  ∈₂))
              (∣ʳ (<$> ∈₁′ ⊛ ∈₃′) ⊛∞ ∣ʳ (<$> ∈₂′)) refl with precs _ ∈₁ ∈₁′ refl | precs _ ∈₂ ∈₂′ refl | inner _ ∈₃ ∈₃′ refl
    preRight⁺ (∣ʳ (<$>  ∈₁ ⊛  ∈₃) ⊛∞ ∣ʳ (<$>  ∈₂))
              (∣ʳ (<$> .∈₁ ⊛ .∈₃) ⊛∞ ∣ʳ (<$> .∈₂)) refl | refl | refl | refl = refl

    preRight⁺ (∣ˡ (<$> _)     ⊛∞ _)
              (∣ʳ (<$> _ ⊛ _) ⊛∞ _)          ()
    preRight⁺ (∣ʳ (<$> _ ⊛ _) ⊛∞ _)
              (∣ˡ (<$> _)     ⊛∞ _)          ()
    preRight⁺ (∣ˡ (<$> _)     ⊛∞ ∣ˡ (<$> _))
              (∣ˡ (<$> _)     ⊛∞ ∣ʳ (<$> _)) ()
    preRight⁺ (∣ˡ (<$> _)     ⊛∞ ∣ʳ (<$> _))
              (∣ˡ (<$> _)     ⊛∞ ∣ˡ (<$> _)) ()
    preRight⁺ (∣ʳ (<$> _ ⊛ _) ⊛∞ ∣ˡ (<$> _))
              (∣ʳ (<$> _ ⊛ _) ⊛∞ ∣ʳ (<$> _)) ()
    preRight⁺ (∣ʳ (<$> _ ⊛ _) ⊛∞ ∣ʳ (<$> _))
              (∣ʳ (<$> _ ⊛ _) ⊛∞ ∣ˡ (<$> _)) ()

    postLeft⁺ : ∀ {s₁ s₂} {e₁ e₂ : ExprIn p left}
                (∈₁ : e₁ ∈⟦ P.postLeft⁺ ⟧· s₁)
                (∈₂ : e₂ ∈⟦ P.postLeft⁺ ⟧· s₂) →
                e₁ ≡ e₂ → ∈₁ ≋ ∈₂
    postLeft⁺ (<$> (∣ˡ (<$>  ∈₁)) ⊛∞ ∣ˡ (<$>  ∈₂))
              (<$> (∣ˡ (<$> ∈₁′)) ⊛∞ ∣ˡ (<$> ∈₂′))       refl with postLeft⁺ ∈₁ ∈₁′ refl | inner _ ∈₂ ∈₂′ refl
    postLeft⁺ (<$> (∣ˡ (<$>  ∈₁)) ⊛∞ ∣ˡ (<$>  ∈₂))
              (<$> (∣ˡ (<$> .∈₁)) ⊛∞ ∣ˡ (<$> .∈₂))       refl | refl | refl = refl
    postLeft⁺ (<$> (∣ʳ (<$>  ∈₁)) ⊛∞ ∣ˡ (<$>  ∈₂))
              (<$> (∣ʳ (<$> ∈₁′)) ⊛∞ ∣ˡ (<$> ∈₂′))       refl with precs _ ∈₁ ∈₁′ refl | inner _ ∈₂ ∈₂′ refl
    postLeft⁺ (<$> (∣ʳ (<$>  ∈₁)) ⊛∞ ∣ˡ (<$>  ∈₂))
              (<$> (∣ʳ (<$> .∈₁)) ⊛∞ ∣ˡ (<$> .∈₂))       refl | refl | refl = refl
    postLeft⁺ (<$> (∣ˡ (<$>  ∈₁)) ⊛∞ ∣ʳ (<$>  ∈₂ ⊛  ∈₃))
              (<$> (∣ˡ (<$> ∈₁′)) ⊛∞ ∣ʳ (<$> ∈₂′ ⊛ ∈₃′)) refl with postLeft⁺ ∈₁ ∈₁′ refl | inner _ ∈₂ ∈₂′ refl | precs _ ∈₃ ∈₃′ refl
    postLeft⁺ (<$> (∣ˡ (<$>  ∈₁)) ⊛∞ ∣ʳ (<$>  ∈₂ ⊛  ∈₃))
              (<$> (∣ˡ (<$> .∈₁)) ⊛∞ ∣ʳ (<$> .∈₂ ⊛ .∈₃)) refl | refl | refl | refl = refl
    postLeft⁺ (<$> (∣ʳ (<$>  ∈₁)) ⊛∞ ∣ʳ (<$>  ∈₂ ⊛  ∈₃))
              (<$> (∣ʳ (<$> ∈₁′)) ⊛∞ ∣ʳ (<$> ∈₂′ ⊛ ∈₃′)) refl with precs _ ∈₁ ∈₁′ refl | inner _ ∈₂ ∈₂′ refl | precs _ ∈₃ ∈₃′ refl
    postLeft⁺ (<$> (∣ʳ (<$>  ∈₁)) ⊛∞ ∣ʳ (<$>  ∈₂ ⊛  ∈₃))
              (<$> (∣ʳ (<$> .∈₁)) ⊛∞ ∣ʳ (<$> .∈₂ ⊛ .∈₃)) refl | refl | refl | refl = refl

    postLeft⁺ (<$> _            ⊛∞ ∣ˡ (<$> _))
              (<$> _            ⊛∞ ∣ʳ (<$> _ ⊛ _)) ()
    postLeft⁺ (<$> _            ⊛∞ ∣ʳ (<$> _ ⊛ _))
              (<$> _            ⊛∞ ∣ˡ (<$> _))     ()
    postLeft⁺ (<$> (∣ˡ (<$> _)) ⊛∞ ∣ˡ (<$> _))
              (<$> (∣ʳ (<$> _)) ⊛∞ ∣ˡ (<$> _))     ()
    postLeft⁺ (<$> (∣ʳ (<$> _)) ⊛∞ ∣ˡ (<$> _))
              (<$> (∣ˡ (<$> _)) ⊛∞ ∣ˡ (<$> _))     ()
    postLeft⁺ (<$> (∣ˡ (<$> _)) ⊛∞ ∣ʳ (<$> _ ⊛ _))
              (<$> (∣ʳ (<$> _)) ⊛∞ ∣ʳ (<$> _ ⊛ _)) ()
    postLeft⁺ (<$> (∣ʳ (<$> _)) ⊛∞ ∣ʳ (<$> _ ⊛ _))
              (<$> (∣ˡ (<$> _)) ⊛∞ ∣ʳ (<$> _ ⊛ _)) ()

    prec′ : ∀ {assoc s₁ s₂} {e₁ e₂ : ExprIn p assoc} →
            (∈₁ : (, e₁) ∈⟦ Grammar.prec p ⟧· s₁)
            (∈₂ : (, e₂) ∈⟦ Grammar.prec p ⟧· s₂) →
            e₁ ≡ e₂ → ∈₁ ≋ ∈₂
    prec′ ∈₁ ∈₂ refl = pr₁ ∈₁ ∈₂ refl refl refl refl refl
      where
      disjoint₃ :
        ∀ {R x} {p′ : ParserProg R} {assoc e s} →
        x ∈⟦ p′ ⟧· s →
        R  ≡ ∃ (ExprIn p) →
        x  ≅ _,_ {B = ExprIn p} assoc e →
        p′ ≅ P.postLeft⁺ ∥ fail →
        ¬ (assoc ≡ non ⊎ assoc ≡ right)
      disjoint₃ e₂∈                              R≡ x≅   p′≅ non≡      with no-confusion R≡ p′≅
      disjoint₃ (∥ˡ (<$> _ ⊛∞ (∣ˡ (<$> _))))     _  refl _   (inj₁ ()) | refl , refl , refl , refl , refl
      disjoint₃ (∥ˡ (<$> _ ⊛∞ (∣ˡ (<$> _))))     _  refl _   (inj₂ ()) | refl , refl , refl , refl , refl
      disjoint₃ (∥ˡ (<$> _ ⊛∞ (∣ʳ (<$> _ ⊛ _)))) _  refl _   (inj₁ ()) | refl , refl , refl , refl , refl
      disjoint₃ (∥ˡ (<$> _ ⊛∞ (∣ʳ (<$> _ ⊛ _)))) _  refl _   (inj₂ ()) | refl , refl , refl , refl , refl
      disjoint₃ (∥ʳ ())                          _  refl _   _         | refl , refl , refl , refl , refl
      disjoint₃ (∣ˡ _)                           _  _    _   _         | lift ()
      disjoint₃ (∣ʳ _)                           _  _    _   _         | lift ()
      disjoint₃ (_ ⊛ _)                          _  _    _   _         | lift ()
      disjoint₃ (_ ⊛∞ _)                         _  _    _   _         | lift ()
      disjoint₃ (<$> _)                          _  _    _   _         | lift ()
      disjoint₃ (+-[] _)                         _  _    _   _         | lift ()
      disjoint₃ (+-∷ _ _)                        _  _    _   _         | lift ()
      disjoint₃ between-[]                       _  _    _   _         | lift ()
      disjoint₃ (between-∷ _ _)                  _  _    _   _         | lift ()

      disjoint₂ :
        ∀ {R x} {p′ : ParserProg R} {assoc e s} →
        x ∈⟦ p′ ⟧· s →
        R  ≡ ∃ (ExprIn p) →
        x  ≅ _,_ {B = ExprIn p} assoc e →
        p′ ≅ P.preRight⁺ ∥ P.postLeft⁺ ∥ fail →
        assoc ≢ non
      disjoint₂ e₂∈                        R≡ x≅   p′≅ non≡ with no-confusion R≡ p′≅
      disjoint₂ (∥ˡ (∣ˡ (<$> _)     ⊛∞ _)) _  refl _   ()   | refl , refl , refl , refl , refl
      disjoint₂ (∥ˡ (∣ʳ (<$> _ ⊛ _) ⊛∞ _)) _  refl _   ()   | refl , refl , refl , refl , refl
      disjoint₂ (∥ʳ e₂∈)                   _  refl _   non≡ | refl , refl , refl , refl , refl = disjoint₃ e₂∈ refl refl refl (inj₁ non≡)
      disjoint₂ (∣ˡ _)                     _  _    _   _    | lift ()
      disjoint₂ (∣ʳ _)                     _  _    _   _    | lift ()
      disjoint₂ (_ ⊛ _)                    _  _    _   _    | lift ()
      disjoint₂ (_ ⊛∞ _)                   _  _    _   _    | lift ()
      disjoint₂ (<$> _)                    _  _    _   _    | lift ()
      disjoint₂ (+-[] _)                   _  _    _   _    | lift ()
      disjoint₂ (+-∷ _ _)                  _  _    _   _    | lift ()
      disjoint₂ between-[]                 _  _    _   _    | lift ()
      disjoint₂ (between-∷ _ _)            _  _    _   _    | lift ()

      disjoint₁ :
        ∀ {R x} {p′ : ParserProg R} {e₁ e₂ s} →
        x ∈⟦ p′ ⟧· s →
        R  ≡ ∃ (ExprIn p) →
        x  ≅ ,_ {B = ExprIn p} e₂ →
        p′ ≅ P.nonAssoc ∥ P.preRight⁺ ∥ P.postLeft⁺ ∥ fail →
        ⟪ e₁ ⟫ ≢ e₂
      disjoint₁ e₂∈                   R≡ x≅   p′≅ ⟪⟫≡ with no-confusion R≡ p′≅
      disjoint₁ (∥ˡ (<$> _ ⊛ _ ⊛∞ _)) _  refl _   ()  | refl , refl , refl , refl , refl
      disjoint₁ (∥ʳ e₂∈)              _  refl _   _   | refl , refl , refl , refl , refl = disjoint₂ e₂∈ refl refl refl refl
      disjoint₁ (∣ˡ _)                _  _    _   _   | lift ()
      disjoint₁ (∣ʳ _)                _  _    _   _   | lift ()
      disjoint₁ (_ ⊛ _)               _  _    _   _   | lift ()
      disjoint₁ (_ ⊛∞ _)              _  _    _   _   | lift ()
      disjoint₁ (<$> _)               _  _    _   _   | lift ()
      disjoint₁ (+-[] _)              _  _    _   _   | lift ()
      disjoint₁ (+-∷ _ _)             _  _    _   _   | lift ()
      disjoint₁ between-[]            _  _    _   _   | lift ()
      disjoint₁ (between-∷ _ _)       _  _    _   _   | lift ()

      pr₄ : ∀ {s₁ s₂ R₁ R₂ e₁ e₂}
              {p₁ : ParserProg R₁} {p₂ : ParserProg R₂} →
            (∈₁ : e₁ ∈⟦ p₁ ⟧· s₁)
            (∈₂ : e₂ ∈⟦ p₂ ⟧· s₂) →
            R₁ ≡ ∃ (ExprIn p) →
            R₂ ≡ ∃ (ExprIn p) →
            p₁ ≅ P.postLeft⁺ ∥ fail →
            p₂ ≅ P.postLeft⁺ ∥ fail →
            e₁ ≅ e₂ →
            ∈₁ ≋ ∈₂
      pr₄ ∈₁              ∈₂      R₁≡ R₂≡ p₁≅ p₂≅ e₁≅  with no-confusion R₁≡ p₁≅ | no-confusion R₂≡ p₂≅
      pr₄ (∥ˡ ∈₁)         (∥ˡ ∈₂)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with postLeft⁺ ∈₁ ∈₂ refl
      pr₄ (∥ˡ ∈ )         (∥ˡ .∈)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | refl = refl
      pr₄ (∥ʳ ())         _               _ _ _ _ _    | refl , refl , refl , refl , refl | _
      pr₄ _               (∥ʳ ())         _ _ _ _ _    | _ | refl , refl , refl , refl , refl
      pr₄ (∣ˡ _)          _               _ _ _ _ _    | lift () | _
      pr₄ (∣ʳ _)          _               _ _ _ _ _    | lift () | _
      pr₄ (_ ⊛ _)         _               _ _ _ _ _    | lift () | _
      pr₄ (_ ⊛∞ _)        _               _ _ _ _ _    | lift () | _
      pr₄ (<$> _)         _               _ _ _ _ _    | lift () | _
      pr₄ (+-[] _)        _               _ _ _ _ _    | lift () | _
      pr₄ (+-∷ _ _)       _               _ _ _ _ _    | lift () | _
      pr₄ between-[]      _               _ _ _ _ _    | lift () | _
      pr₄ (between-∷ _ _) _               _ _ _ _ _    | lift () | _
      pr₄ _               (∣ˡ _)          _ _ _ _ _    | _       | lift ()
      pr₄ _               (∣ʳ _)          _ _ _ _ _    | _       | lift ()
      pr₄ _               (_ ⊛ _)         _ _ _ _ _    | _       | lift ()
      pr₄ _               (_ ⊛∞ _)        _ _ _ _ _    | _       | lift ()
      pr₄ _               (<$> _)         _ _ _ _ _    | _       | lift ()
      pr₄ _               (+-[] _)        _ _ _ _ _    | _       | lift ()
      pr₄ _               (+-∷ _ _)       _ _ _ _ _    | _       | lift ()
      pr₄ _               between-[]      _ _ _ _ _    | _       | lift ()
      pr₄ _               (between-∷ _ _) _ _ _ _ _    | _       | lift ()

      pr₃ : ∀ {s₁ s₂ R₁ R₂ e₁ e₂}
              {p₁ : ParserProg R₁} {p₂ : ParserProg R₂} →
            (∈₁ : e₁ ∈⟦ p₁ ⟧· s₁)
            (∈₂ : e₂ ∈⟦ p₂ ⟧· s₂) →
            R₁ ≡ ∃ (ExprIn p) →
            R₂ ≡ ∃ (ExprIn p) →
            p₁ ≅ P.preRight⁺ ∥ P.postLeft⁺ ∥ fail →
            p₂ ≅ P.preRight⁺ ∥ P.postLeft⁺ ∥ fail →
            e₁ ≅ e₂ →
            ∈₁ ≋ ∈₂
      pr₃ ∈₁              ∈₂      R₁≡ R₂≡ p₁≅ p₂≅ e₁≅  with no-confusion R₁≡ p₁≅ | no-confusion R₂≡ p₂≅
      pr₃ (∥ˡ ∈₁)         (∥ˡ ∈₂)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with preRight⁺ ∈₁ ∈₂ refl
      pr₃ (∥ˡ ∈ )         (∥ˡ .∈)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | refl = refl
      pr₃ (∥ʳ ∈₁)         (∥ʳ ∈₂)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with pr₄ ∈₁ ∈₂ refl refl refl refl refl
      pr₃ (∥ʳ ∈ )         (∥ʳ .∈)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | refl = refl
      pr₃ (∥ˡ _)          (∥ʳ ∈₂)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with disjoint₃ ∈₂ refl refl refl (inj₂ refl)
      pr₃ (∥ˡ _)          (∥ʳ _)          _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | ()
      pr₃ (∥ʳ ∈₁)         (∥ˡ _)          _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with disjoint₃ ∈₁ refl refl refl (inj₂ refl)
      pr₃ (∥ʳ ∈₁)         (∥ˡ _)          _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | ()
      pr₃ (∣ˡ _)          _               _ _ _ _ _    | lift () | _
      pr₃ (∣ʳ _)          _               _ _ _ _ _    | lift () | _
      pr₃ (_ ⊛ _)         _               _ _ _ _ _    | lift () | _
      pr₃ (_ ⊛∞ _)        _               _ _ _ _ _    | lift () | _
      pr₃ (<$> _)         _               _ _ _ _ _    | lift () | _
      pr₃ (+-[] _)        _               _ _ _ _ _    | lift () | _
      pr₃ (+-∷ _ _)       _               _ _ _ _ _    | lift () | _
      pr₃ between-[]      _               _ _ _ _ _    | lift () | _
      pr₃ (between-∷ _ _) _               _ _ _ _ _    | lift () | _
      pr₃ _               (∣ˡ _)          _ _ _ _ _    | _       | lift ()
      pr₃ _               (∣ʳ _)          _ _ _ _ _    | _       | lift ()
      pr₃ _               (_ ⊛ _)         _ _ _ _ _    | _       | lift ()
      pr₃ _               (_ ⊛∞ _)        _ _ _ _ _    | _       | lift ()
      pr₃ _               (<$> _)         _ _ _ _ _    | _       | lift ()
      pr₃ _               (+-[] _)        _ _ _ _ _    | _       | lift ()
      pr₃ _               (+-∷ _ _)       _ _ _ _ _    | _       | lift ()
      pr₃ _               between-[]      _ _ _ _ _    | _       | lift ()
      pr₃ _               (between-∷ _ _) _ _ _ _ _    | _       | lift ()

      pr₂ : ∀ {s₁ s₂ R₁ R₂ e₁ e₂}
              {p₁ : ParserProg R₁} {p₂ : ParserProg R₂} →
            (∈₁ : e₁ ∈⟦ p₁ ⟧· s₁)
            (∈₂ : e₂ ∈⟦ p₂ ⟧· s₂) →
            R₁ ≡ ∃ (ExprIn p) →
            R₂ ≡ ∃ (ExprIn p) →
            p₁ ≅ P.nonAssoc ∥ P.preRight⁺ ∥ P.postLeft⁺ ∥ fail →
            p₂ ≅ P.nonAssoc ∥ P.preRight⁺ ∥ P.postLeft⁺ ∥ fail →
            e₁ ≅ e₂ →
            ∈₁ ≋ ∈₂
      pr₂ ∈₁ ∈₂                   R₁≡ R₂≡ p₁≅ p₂≅ e₁≅  with no-confusion R₁≡ p₁≅ | no-confusion R₂≡ p₂≅
      pr₂ (∥ˡ (<$> ∈₁  ⊛ ∈₂  ⊛∞ ∈₃ ))
          (∥ˡ (<$> ∈₁′ ⊛ ∈₂′ ⊛∞ ∈₃′))     _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with precs _ ∈₁ ∈₁′ refl
                                                                                             | inner _ ∈₂ ∈₂′ refl
                                                                                             | precs _ ∈₃ ∈₃′ refl
      pr₂ (∥ˡ (<$>  ∈₁ ⊛  ∈₂ ⊛∞  ∈₃))
          (∥ˡ (<$> .∈₁ ⊛ .∈₂ ⊛∞ .∈₃))     _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | refl | refl | refl = refl
      pr₂ (∥ʳ ∈₁)         (∥ʳ ∈₂)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with pr₃ ∈₁ ∈₂ refl refl refl refl refl
      pr₂ (∥ʳ ∈ )         (∥ʳ .∈)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | refl = refl
      pr₂ (∥ˡ _)          (∥ʳ ∈₂)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with disjoint₂ ∈₂ refl refl refl refl
      pr₂ (∥ˡ _)          (∥ʳ _)          _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | ()
      pr₂ (∥ʳ ∈₁)         (∥ˡ _)          _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with disjoint₂ ∈₁ refl refl refl refl
      pr₂ (∥ʳ ∈₁)         (∥ˡ _)          _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | ()
      pr₂ (∣ˡ _)          _               _ _ _ _ _    | lift () | _
      pr₂ (∣ʳ _)          _               _ _ _ _ _    | lift () | _
      pr₂ (_ ⊛ _)         _               _ _ _ _ _    | lift () | _
      pr₂ (_ ⊛∞ _)        _               _ _ _ _ _    | lift () | _
      pr₂ (<$> _)         _               _ _ _ _ _    | lift () | _
      pr₂ (+-[] _)        _               _ _ _ _ _    | lift () | _
      pr₂ (+-∷ _ _)       _               _ _ _ _ _    | lift () | _
      pr₂ between-[]      _               _ _ _ _ _    | lift () | _
      pr₂ (between-∷ _ _) _               _ _ _ _ _    | lift () | _
      pr₂ _               (∣ˡ _)          _ _ _ _ _    | _       | lift ()
      pr₂ _               (∣ʳ _)          _ _ _ _ _    | _       | lift ()
      pr₂ _               (_ ⊛ _)         _ _ _ _ _    | _       | lift ()
      pr₂ _               (_ ⊛∞ _)        _ _ _ _ _    | _       | lift ()
      pr₂ _               (<$> _)         _ _ _ _ _    | _       | lift ()
      pr₂ _               (+-[] _)        _ _ _ _ _    | _       | lift ()
      pr₂ _               (+-∷ _ _)       _ _ _ _ _    | _       | lift ()
      pr₂ _               between-[]      _ _ _ _ _    | _       | lift ()
      pr₂ _               (between-∷ _ _) _ _ _ _ _    | _       | lift ()

      pr₁ : ∀ {s₁ s₂ R₁ R₂ e₁ e₂}
              {p₁ : ParserProg R₁} {p₂ : ParserProg R₂} →
            (∈₁ : e₁ ∈⟦ p₁ ⟧· s₁)
            (∈₂ : e₂ ∈⟦ p₂ ⟧· s₂) →
            R₁ ≡ ∃ (ExprIn p) →
            R₂ ≡ ∃ (ExprIn p) →
            p₁ ≅ Grammar.prec p →
            p₂ ≅ Grammar.prec p →
            e₁ ≅ e₂ →
            ∈₁ ≋ ∈₂
      pr₁ ∈₁              ∈₂      R₁≡ R₂≡ p₁≅ p₂≅ e₁≅  with no-confusion R₁≡ p₁≅ | no-confusion R₂≡ p₂≅
      pr₁ (∥ˡ (<$> ∈₁))   (∥ˡ (<$> ∈₂))   _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with inner _ ∈₁ ∈₂ refl
      pr₁ (∥ˡ (<$> ∈ ))   (∥ˡ (<$> .∈))   _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | refl = refl
      pr₁ (∥ʳ ∈₁)         (∥ʳ ∈₂)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with pr₂ ∈₁ ∈₂ refl refl refl refl refl
      pr₁ (∥ʳ ∈ )         (∥ʳ .∈)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | refl = refl
      pr₁ (∥ˡ (<$> _))    (∥ʳ ∈₂)         _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with disjoint₁ ∈₂ refl refl refl refl
      pr₁ (∥ˡ (<$> _))    (∥ʳ _)          _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | ()
      pr₁ (∥ʳ ∈₁)         (∥ˡ (<$> _))    _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl with disjoint₁ ∈₁ refl refl refl refl
      pr₁ (∥ʳ _)          (∥ˡ (<$> _))    _ _ _ _ refl | refl , refl , refl , refl , refl
                                                       | refl , refl , refl , refl , refl | ()
      pr₁ (∣ˡ _)          _               _ _ _ _ _    | lift () | _
      pr₁ (∣ʳ _)          _               _ _ _ _ _    | lift () | _
      pr₁ (_ ⊛ _)         _               _ _ _ _ _    | lift () | _
      pr₁ (_ ⊛∞ _)        _               _ _ _ _ _    | lift () | _
      pr₁ (<$> _)         _               _ _ _ _ _    | lift () | _
      pr₁ (+-[] _)        _               _ _ _ _ _    | lift () | _
      pr₁ (+-∷ _ _)       _               _ _ _ _ _    | lift () | _
      pr₁ between-[]      _               _ _ _ _ _    | lift () | _
      pr₁ (between-∷ _ _) _               _ _ _ _ _    | lift () | _
      pr₁ _               (∣ˡ _)          _ _ _ _ _    | _       | lift ()
      pr₁ _               (∣ʳ _)          _ _ _ _ _    | _       | lift ()
      pr₁ _               (_ ⊛ _)         _ _ _ _ _    | _       | lift ()
      pr₁ _               (_ ⊛∞ _)        _ _ _ _ _    | _       | lift ()
      pr₁ _               (<$> _)         _ _ _ _ _    | _       | lift ()
      pr₁ _               (+-[] _)        _ _ _ _ _    | _       | lift ()
      pr₁ _               (+-∷ _ _)       _ _ _ _ _    | _       | lift ()
      pr₁ _               between-[]      _ _ _ _ _    | _       | lift ()
      pr₁ _               (between-∷ _ _) _ _ _ _ _    | _       | lift ()

  inner : ∀ {fix s₁ s₂} ops {e₁ e₂ : Inner {fix} ops}
          (∈₁ : e₁ ∈⟦ Grammar.inner ops ⟧· s₁)
          (∈₂ : e₂ ∈⟦ Grammar.inner ops ⟧· s₂) →
          e₁ ≡ e₂ → ∈₁ ≋ ∈₂
  inner [] () () _
  inner ((_ , op) ∷ ops) (∣ˡ (<$>  ∈₁))
                         (∣ˡ (<$>  ∈₂)) refl with inner′ ∈₁ ∈₂
  inner ((_ , op) ∷ ops) (∣ˡ (<$>  ∈₁))
                         (∣ˡ (<$> .∈₁)) refl | refl = refl
  inner ((_ , op) ∷ ops) (∣ʳ (<$>_ {x = ( _ ∙  _)}  ∈₁))
                         (∣ʳ (<$>_ {x = (._ ∙ ._)}  ∈₂)) refl with inner ops ∈₁ ∈₂ refl
  inner ((_ , op) ∷ ops) (∣ʳ (<$>_ {x = ( _ ∙  _)}  ∈₁))
                         (∣ʳ (<$>_ {x = (._ ∙ ._)} .∈₁)) refl | refl = refl
  inner ((_ , op) ∷ ops) (∣ˡ (<$> ∈₁)) (∣ʳ (<$>_ {x = (_ ∙ _)} ∈₂)) ()
  inner ((_ , op) ∷ ops) (∣ʳ (<$>_ {x = (_ ∙ _)} ∈₁)) (∣ˡ (<$> ∈₂)) ()

  inner′ : ∀ {arity s₁ s₂}
             {ns : Vec NamePart (1 + arity)}
             {args : Vec (Expr anyPrecedence) arity}
           (∈₁ : args ∈⟦ Grammar.expr between ns ⟧· s₁)
           (∈₂ : args ∈⟦ Grammar.expr between ns ⟧· s₂) →
           ∈₁ ≋ ∈₂
  inner′ ∈₁ ∈₂ = in′ ∈₁ ∈₂ refl refl refl refl refl
    where
    in′ : ∀ {arity s₁ s₂ R₁ R₂ args₁ args₂}
            {p₁ : ParserProg R₁}
            {p₂ : ParserProg R₂}
            {ns : Vec NamePart (1 + arity)}
          (∈₁ : args₁ ∈⟦ p₁ ⟧· s₁)
          (∈₂ : args₂ ∈⟦ p₂ ⟧· s₂) →
          R₁ ≡ Vec (Expr anyPrecedence) arity →
          R₂ ≡ Vec (Expr anyPrecedence) arity →
          p₁ ≅ Grammar.expr between ns →
          p₂ ≅ Grammar.expr between ns →
          args₁ ≅ args₂ →
          ∈₁ ≋ ∈₂
    in′ ∈₁                 ∈₂         R₁≡ R₂≡ p₁≅ p₂≅ args₁≅ with no-confusion R₁≡ p₁≅ | no-confusion R₂≡ p₂≅
    in′ between-[]         between-[]         _ _ _ _ refl   | refl , refl , refl , refl
                                                             | refl , refl , refl , refl = refl
    in′ (between-∷ ∈₁ ∈⋯₁) (between-∷ ∈₂ ∈⋯₂) _ _ _ _ refl   | refl , refl , refl , refl
                                                             | refl , refl , refl , refl with precs _ ∈₁ ∈₂ refl | inner′ ∈⋯₁ ∈⋯₂
    in′ (between-∷ ∈  ∈⋯)  (between-∷ .∈ .∈⋯) _ _ _ _ refl   | refl , refl , refl , refl
                                                             | refl , refl , refl , refl | refl | refl = refl
    in′ between-[]         (between-∷ _ _)    _ _ _ _ ()     | refl , _ | refl , _
    in′ (between-∷ _ _)    between-[]         _ _ _ _ ()     | refl , _ | refl , _
    in′ (∣ˡ _)             _                  _ _ _ _ _      | lift ()  | _
    in′ (∣ʳ _)             _                  _ _ _ _ _      | lift ()  | _
    in′ (_ ⊛ _)            _                  _ _ _ _ _      | lift ()  | _
    in′ (_ ⊛∞ _)           _                  _ _ _ _ _      | lift ()  | _
    in′ (<$> _)            _                  _ _ _ _ _      | lift ()  | _
    in′ (+-[] _)           _                  _ _ _ _ _      | lift ()  | _
    in′ (+-∷ _ _)          _                  _ _ _ _ _      | lift ()  | _
    in′ (∥ˡ _)             _                  _ _ _ _ _      | lift ()  | _
    in′ (∥ʳ _)             _                  _ _ _ _ _      | lift ()  | _
    in′ _                  (∣ˡ _)             _ _ _ _ _      | _        | lift ()
    in′ _                  (∣ʳ _)             _ _ _ _ _      | _        | lift ()
    in′ _                  (_ ⊛ _)            _ _ _ _ _      | _        | lift ()
    in′ _                  (_ ⊛∞ _)           _ _ _ _ _      | _        | lift ()
    in′ _                  (<$> _)            _ _ _ _ _      | _        | lift ()
    in′ _                  (+-[] _)           _ _ _ _ _      | _        | lift ()
    in′ _                  (+-∷ _ _)          _ _ _ _ _      | _        | lift ()
    in′ _                  (∥ˡ _)             _ _ _ _ _      | _        | lift ()
    in′ _                  (∥ʳ _)             _ _ _ _ _      | _        | lift ()

-- There is at most one string representing a given expression.

unique : ∀ {e s₁ s₂} →
         e ∈ Grammar.expression · s₁ →
         e ∈ Grammar.expression · s₂ →
         s₁ ≡ s₂
unique ∈₁ ∈₂ with ∈₁′ | ∈₂′ | Unique.precs _ ∈₁′ ∈₂′ refl
  where
  ∈₁′ = Lib.Semantics.complete (♭ Grammar.expr) ∈₁
  ∈₂′ = Lib.Semantics.complete (♭ Grammar.expr) ∈₂
... | ∈ | .∈ | Unique.refl = refl
