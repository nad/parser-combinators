------------------------------------------------------------------------
-- The two methods used to specify the grammars are equivalent (for
-- acyclic graphs)
------------------------------------------------------------------------

open import Mixfix.Expr
open import Mixfix.Acyclic.PrecedenceGraph
  using (acyclic; precedence)

module Mixfix.Equivalence
  (g : PrecedenceGraphInterface.PrecedenceGraph acyclic)
  where

open import Data.Function using (_∘₁_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product
open import Data.Vec using (Vec; []; _∷_)

open import StructurallyRecursiveDescentParsing.Parser
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  as Sem
import StructurallyRecursiveDescentParsing.Simplified as Simplified
import StructurallyRecursiveDescentParsing.Simplified.Semantics
  as SSem

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
      preRight⁺ (+-[] f∈)     ↑∈ = preRight f∈ ⊛∞ ∣ʳ (<$> precs _ ↑∈)
      preRight⁺ (+-∷  f∈ fs∈) ↑∈ = preRight f∈ ⊛∞ ∣ˡ (<$> preRight⁺ fs∈ ↑∈)

      postLeft : ∀ {s s′ f} →
                 f ⊕ s′ ∈⟦ A.postLeft ⟧A· s →
                 f ⊕ s′ ∈⟦ C.postLeft ⟧C· s
      postLeft (∣ˡ (<$> i∈     )) = ∣ˡ (<$> inner _ i∈)
      postLeft (∣ʳ (<$> i∈ ⊛ ↑∈)) = ∣ʳ (<$> inner _ i∈ ⊛ precs _ ↑∈)

      postLeft⁺ : ∀ {s s′ s″ o fs} →
                  o                ⊕ s′ ∈⟦ similar <$> C.postLeft⁺
                                         ∣ tighter <$> C.p↑ ⟧C· s →
                  fs               ⊕ s″ ∈⟦ A.postLeft +       ⟧A· s′ →
                  ALemma.appˡ o fs ⊕ s″ ∈⟦ C.postLeft⁺        ⟧C· s
      postLeft⁺ o∈ (+-[] f∈)     =                     <$> o∈ ⊛∞ postLeft f∈
      postLeft⁺ o∈ (+-∷  f∈ fs∈) = postLeft⁺ (∣ˡ (<$> (<$> o∈ ⊛∞ postLeft f∈))) fs∈

      prec′ : ∀ {s s′ e} →
              e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s →
              e ⊕ s′ ∈⟦  Cyclic.prec p ⟧C· s
      prec′ (∥ˡ (<$> i∈))                      = ∥ˡ (<$> inner _ i∈)
      prec′ (∥ʳ (∥ˡ (<$> ↑₁∈ ⊛ i∈ ⊛ ↑₂∈)))     = ∥ʳ (∥ˡ (<$> precs _ ↑₁∈ ⊛ inner _ i∈ ⊛∞ precs _ ↑₂∈ ))
      prec′ (∥ʳ (∥ʳ (∥ˡ (<$> fs∈ ⊛ ↑∈))))      = ∥ʳ (∥ʳ (∥ˡ (preRight⁺ fs∈ ↑∈)))
      prec′ (∥ʳ (∥ʳ (∥ʳ (∥ˡ (<$> ↑∈ ⊛ fs∈))))) = ∥ʳ (∥ʳ (∥ʳ (∥ˡ (postLeft⁺ (∣ʳ (<$> precs _ ↑∈)) fs∈))))
      prec′ (∥ʳ (∥ʳ (∥ʳ (∥ʳ ()))))

    inner : ∀ {fix} (ops : List (∃ (Operator fix))) {s s′ i} →
            i ⊕ s′ ∈⟦ Acyclic.inner ops ⟧A· s →
            i ⊕ s′ ∈⟦  Cyclic.inner ops ⟧C· s
    inner []               ()
    inner ((_ , op) ∷ ops) (∣ˡ (<$> i∈)) = ∣ˡ (<$> inner′ _ i∈)
    inner ((_ , op) ∷ ops) (∣ʳ (<$> i∈)) = ∣ʳ (<$> inner ops i∈)

    inner′ : ∀ {arity} (ns : Vec NamePart (1 + arity)) {s s′ i} →
             i ⊕ s′ ∈⟦ Acyclic.expr between ns ⟧A· s →
             i ⊕ s′ ∈⟦  Cyclic.expr between ns ⟧C· s
    inner′ (n ∷ .[]) between-[]           = between-[]
    inner′ (n ∷ ns)  (between-∷ e∈g es∈g) =
      between-∷ (precs g e∈g) (inner′ ns es∈g)

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

      prec′ : ∀ {s s′ e} →
              e ⊕ s′ ∈⟦  Cyclic.prec p ⟧C· s →
              e ⊕ s′ ∈⟦ Acyclic.prec p ⟧A· s
      prec′ (∥ˡ (<$> i∈))                   = ∥ˡ (<$> inner _ i∈)
      prec′ (∥ʳ (∥ˡ (<$> ↑₁∈ ⊛ i∈ ⊛∞ ↑₂∈))) = ∥ʳ (∥ˡ (<$> precs _ ↑₁∈ ⊛ inner _ i∈ ⊛ precs _ ↑₂∈ ))
      prec′ (∥ʳ (∥ʳ (∥ˡ pre∈)))             = ∥ʳ (∥ʳ (∥ˡ (preRight⁺ pre∈)))
      prec′ (∥ʳ (∥ʳ (∥ʳ (∥ˡ post∈))))       = ∥ʳ (∥ʳ (∥ʳ (∥ˡ (postLeft⁺ post∈))))
      prec′ (∥ʳ (∥ʳ (∥ʳ (∥ʳ ()))))

    inner : ∀ {fix} (ops : List (∃ (Operator fix))) {s s′ i} →
            i ⊕ s′ ∈⟦  Cyclic.inner ops ⟧C· s →
            i ⊕ s′ ∈⟦ Acyclic.inner ops ⟧A· s
    inner []               ()
    inner ((_ , op) ∷ ops) (∣ˡ (<$> i∈)) = ∣ˡ (<$> inner′ _ i∈)
    inner ((_ , op) ∷ ops) (∣ʳ (<$> i∈)) = ∣ʳ (<$> inner ops i∈)

    inner′ : ∀ {arity} (ns : Vec NamePart (1 + arity)) {s s′ i} →
             i ⊕ s′ ∈⟦  Cyclic.expr between ns ⟧C· s →
             i ⊕ s′ ∈⟦ Acyclic.expr between ns ⟧A· s
    inner′ (n ∷ .[]) between-[]           = between-[]
    inner′ (n ∷ ns)  (between-∷ e∈g es∈g) =
      between-∷ (precs g e∈g) (inner′ ns es∈g)

acyclicToCyclic
  : ∀ {e s} → e ∈ Simplified.⟦_⟧ Acyclic.expression · s →
              e ∈                 Cyclic.expression · s
acyclicToCyclic =
  Sem.sound                   ∘₁
  CLib.Semantics-⊕.sound      ∘₁
  AcyclicToCyclic.precs _     ∘₁
  ALib.Semantics-⊕.complete _ ∘₁
  SSem.⊕-complete             ∘₁
  SSem.complete _

cyclicToAcyclic
  : ∀ {e s} → e ∈                 Cyclic.expression · s →
              e ∈ Simplified.⟦_⟧ Acyclic.expression · s
cyclicToAcyclic =
  SSem.sound                  ∘₁
  SSem.⊕-sound                ∘₁
  ALib.Semantics-⊕.sound      ∘₁
  CyclicToAcyclic.precs _     ∘₁
  CLib.Semantics-⊕.complete _ ∘₁
  Sem.complete
