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
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_,_; ,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open PrecedenceCorrect i g
open import TotalParserCombinators.Semantics
open import Mixfix.Fixity
open import Mixfix.Operator
open import Mixfix.Cyclic.Lib as Lib
open Lib.Semantics
import Mixfix.Cyclic.Grammar
private module Grammar = Mixfix.Cyclic.Grammar i g

module Unique where

 data _≋_ {A : Set} {x₁ : A} {s₁ p₁} (∈ : x₁ ∈⟦ p₁ ⟧· s₁) :
          ∀ {x₂ : A} {s₂ p₂} → x₂ ∈⟦ p₂ ⟧· s₂ → Set where
   refl : ∈ ≋ ∈

 mutual

  precs : ∀ ps {s₁ s₂} {e₁ e₂ : Expr ps}
          (∈₁ : e₁ ∈⟦ Grammar.precs ps ⟧· s₁)
          (∈₂ : e₂ ∈⟦ Grammar.precs ps ⟧· s₂) →
          e₁ ≡ e₂ → ∈₁ ≋ ∈₂
  precs [] () () _
  precs (p ∷ ps) (∣ˡ (<$>_ {x = ( _ ,  _)}  ∈₁))
                 (∣ˡ (<$>_ {x = (._ , ._)}  ∈₂)) refl with prec ∈₁ ∈₂
  precs (p ∷ ps) (∣ˡ (<$>_ {x = ( _ ,  _)}  ∈₁))
                 (∣ˡ (<$>_ {x = (._ , ._)} .∈₁)) refl | refl = refl
  precs (p ∷ ps) (∣ʳ (<$>_ {x = ( _ ∙  _)}  ∈₁))
                 (∣ʳ (<$>_ {x = (._ ∙ ._)}  ∈₂)) refl with precs ps ∈₁ ∈₂ refl
  precs (p ∷ ps) (∣ʳ (<$>_ {x = ( _ ∙  _)}  ∈₁))
                 (∣ʳ (<$>_ {x = (._ ∙ ._)} .∈₁)) refl | refl = refl
  precs (p ∷ ps) (∣ˡ (<$> ∈₁)) (∣ʳ (<$>_ {x = _ ∙ _} ∈₂)) ()
  precs (p ∷ ps) (∣ʳ (<$>_ {x = _ ∙ _} ∈₁)) (∣ˡ (<$> ∈₂)) ()

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
    prec′ (∥ˡ (<$> ∈₁)) (∥ˡ (<$>  ∈₂)) refl with inner _ ∈₁ ∈₂ refl
    prec′ (∥ˡ (<$> ∈₁)) (∥ˡ (<$> .∈₁)) refl | refl = refl

    prec′ (∥ʳ (∥ˡ (<$> ∈₁  ⊛ ∈₂  ⊛∞ ∈₃ )))
          (∥ʳ (∥ˡ (<$> ∈₁′ ⊛ ∈₂′ ⊛∞ ∈₃′))) refl
      with precs _ ∈₁ ∈₁′ refl | inner _ ∈₂ ∈₂′ refl | precs _ ∈₃ ∈₃′ refl
    prec′ (∥ʳ (∥ˡ (<$>  ∈₁ ⊛  ∈₂ ⊛∞  ∈₃)))
          (∥ʳ (∥ˡ (<$> .∈₁ ⊛ .∈₂ ⊛∞ .∈₃))) refl | refl | refl | refl = refl

    prec′ (∥ʳ (∥ʳ (∥ˡ ∈₁))) (∥ʳ (∥ʳ (∥ˡ  ∈₂))) refl with preRight⁺ ∈₁ ∈₂ refl
    prec′ (∥ʳ (∥ʳ (∥ˡ ∈₁))) (∥ʳ (∥ʳ (∥ˡ .∈₁))) refl | refl = refl

    prec′ (∥ʳ (∥ʳ (∥ʳ (∥ˡ ∈₁)))) (∥ʳ (∥ʳ (∥ʳ (∥ˡ  ∈₂)))) refl with postLeft⁺ ∈₁ ∈₂ refl
    prec′ (∥ʳ (∥ʳ (∥ʳ (∥ˡ ∈₁)))) (∥ʳ (∥ʳ (∥ʳ (∥ˡ .∈₁)))) refl | refl = refl

    prec′ (∥ˡ (<$> _)) (∥ʳ (∥ˡ (<$> _ ⊛ _ ⊛∞ _))) ()
    prec′ (∥ʳ (∥ˡ (<$> _ ⊛ _ ⊛∞ _))) (∥ˡ (<$> _)) ()
    prec′ (∥ʳ (∥ʳ (∥ʳ (∥ʳ ())))) _ _
    prec′ _ (∥ʳ (∥ʳ (∥ʳ (∥ʳ ())))) _

  inner : ∀ {fix s₁ s₂} ops {e₁ e₂ : Inner {fix} ops}
          (∈₁ : e₁ ∈⟦ Grammar.inner ops ⟧· s₁)
          (∈₂ : e₂ ∈⟦ Grammar.inner ops ⟧· s₂) →
          e₁ ≡ e₂ → ∈₁ ≋ ∈₂
  inner [] () () _
  inner ((_ , op) ∷ ops) (∣ˡ (<$>  ∈₁))
                         (∣ˡ (<$>  ∈₂)) refl with inner′ _ _ ∈₁ ∈₂
  inner ((_ , op) ∷ ops) (∣ˡ (<$>  ∈₁))
                         (∣ˡ (<$> .∈₁)) refl | refl = refl
  inner ((_ , op) ∷ ops) (∣ʳ (<$>_ {x = ( _ ∙  _)}  ∈₁))
                         (∣ʳ (<$>_ {x = (._ ∙ ._)}  ∈₂)) refl with inner ops ∈₁ ∈₂ refl
  inner ((_ , op) ∷ ops) (∣ʳ (<$>_ {x = ( _ ∙  _)}  ∈₁))
                         (∣ʳ (<$>_ {x = (._ ∙ ._)} .∈₁)) refl | refl = refl
  inner ((_ , op) ∷ ops) (∣ˡ (<$> ∈₁)) (∣ʳ (<$>_ {x = (_ ∙ _)} ∈₂)) ()
  inner ((_ , op) ∷ ops) (∣ʳ (<$>_ {x = (_ ∙ _)} ∈₁)) (∣ˡ (<$> ∈₂)) ()

  inner′ : ∀ {arity s₁ s₂}
           (ns : Vec NamePart (1 + arity))
           (args : Vec (Expr anyPrecedence) arity)
           (∈₁ : args ∈⟦ Grammar.expr between ns ⟧· s₁)
           (∈₂ : args ∈⟦ Grammar.expr between ns ⟧· s₂) →
           ∈₁ ≋ ∈₂
  inner′ (n ∷ [])      []           between-[] between-[] = refl
  inner′ (n ∷ n′ ∷ ns) (arg ∷ args)
         (between-∷ ∈₁ ∈⋯₁) (between-∷ ∈₂ ∈⋯₂)
    with precs _ ∈₁ ∈₂ refl | inner′ (n′ ∷ ns) args ∈⋯₁ ∈⋯₂
  inner′ (n ∷ n′ ∷ ns) (arg ∷ args)
         (between-∷ ∈₁ ∈⋯₁) (between-∷ .∈₁ .∈⋯₁) | refl | refl = refl

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
