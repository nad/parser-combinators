-- An implementation of terminating parsers due to Conor McBride and
-- James McKinna, as presented in the talk Seeing and Doing at the
-- Workshop on Termination and Type Theory, Hindås, Sweden, 2002.

{-# OPTIONS --type-in-type #-}

module SeeingAndDoing where

open import Data.Unit
open import Data.Bool
open import Data.List
open import Data.Maybe as Maybe
open import Data.String renaming (_==_ to _=S=_)
open import Category.Monad
open RawMonadPlus Maybe.monadPlus
open import Data.Function using (_∘_; const)
open import Relation.Binary.PropositionalEquality

data Token : Set where
  V     : (s : String) → Token
  IF    : Token
  THEN  : Token
  ELSE  : Token
  TRUE  : Token
  FALSE : Token

_==_ : Token → Token → Bool
V s₁  == V s₂  = s₁ =S= s₂
IF    == IF    = true
THEN  == THEN  = true
ELSE  == ELSE  = true
TRUE  == TRUE  = true
FALSE == FALSE = true
_     == _     = false

data Pos : Set where
  L : Pos
  R : Pos

Memo : (Pos → Set) → Pos → Set
Memo P L = ⊤
Memo P R = P L

PosOrder : ∀ j P → (∀ i → Memo P i → P i) → P j
PosOrder L P p = p L _
PosOrder R P p = p R (p L _)

module Combinators (Rec : Set) where

  infixl 25 _∙_ _!_
  infixl 15 _+_

  data _⟨_⟩_ : Pos → Set → Pos → Set where
    rec  : R ⟨ Rec ⟩ R
    η    : ∀ {i X} (x : Maybe X) → i ⟨ X ⟩ i
    tok  : ∀ {i} (u : Token) → i ⟨ ⊤ ⟩ R
    vart : ∀ {i} → i ⟨ String ⟩ R
    _+_  : ∀ {i j X} (x y : i ⟨ X ⟩ j) → i ⟨ X ⟩ j
    _∙_  : ∀ {j i k S T}
           (f : i ⟨ (S → T) ⟩ j) (s : j ⟨ S ⟩ k) → i ⟨ T ⟩ k

  for : ∀ {i X} → X → i ⟨ X ⟩ i
  for = η ∘ just

  fail : ∀ {i X} → i ⟨ X ⟩ i
  fail = η nothing

  _!_ : ∀ {i j k S T} → i ⟨ S ⟩ j → j ⟨ T ⟩ k → i ⟨ S ⟩ k
  s ! t = for const ∙ s ∙ t

Grammar : Set → Set
Grammar Rec = L ⟨ Rec ⟩ R
  where open Combinators Rec

module Parser {Rec : Set} (grammar : Grammar Rec) where

  open Combinators Rec

  ⇓ : ∀ {i j X} → i ⟨ X ⟩ j → Maybe X
  ⇓ (η x)   = x
  ⇓ (x + y) = ⇓ x ∣ ⇓ y
  ⇓ (f ∙ s) = ⇓ f ⊛ ⇓ s
  ⇓ _       = nothing

  eat : ∀ {i X} → i ⟨ X ⟩ R → Token → R ⟨ X ⟩ R
  eat {i} x t = PosOrder i P eat′ x t
    where
    P = λ i → ∀ {X} → i ⟨ X ⟩ R → Token → R ⟨ X ⟩ R

    eat′ : ∀ i → Memo P i → P i
    eat′ _ _    (tok u)       t     with u == t
    eat′ _ _    (tok u)       t     | true  = for _
    eat′ _ _    (tok u)       t     | false = fail
    eat′ _ _    vart          (V x) = for x
    eat′ _ eat  (x + y)       t     = eat′ _ eat x t
                                    + eat′ _ eat y t
    eat′ L _    (_∙_ {L} f s) t     = η (⇓ f) ∙ eat′ L _ s t
    eat′ L _    (_∙_ {R} f s) t     = eat′ L _ f t ∙ s
    eat′ R eatL (_∙_ {R} f s) t     = η (⇓ f) ∙ eat′ R eatL s t
                                    + eat′ R eatL f t ∙ s
    eat′ R eatL rec           t     = eatL grammar t
    eat′ _ _    _             _     = fail

  parse : List Token → Maybe Rec
  parse is = ⇓ (foldr (λ t x → eat x t) rec (reverse is))

data CE : Set where
  var : (s : String) → CE
  val : (b : Bool) → CE
  if  : (i t e : CE) → CE

grammar : Grammar CE
grammar = for var ∙ vart
        + for (val true)  ! tok TRUE
        + for (val false) ! tok FALSE
        + for (λ i → if i (val true) (val true)) ! tok IF ∙ rec
        + for if ! tok IF ∙ rec ! tok THEN ∙ rec
                                ! tok ELSE ∙ rec
  where open Combinators CE

test₁ : let open Parser grammar in
        parse (IF ∷ V "x" ∷ THEN ∷ TRUE ∷ ELSE ∷ FALSE ∷ []) ≡
        just (if (var "x") (val true) (val false))
test₁ = refl

-- Takes ages to type check:

-- test₂ : let open Parser grammar in
--         parse (IF ∷ V "x" ∷
--                     THEN ∷ IF ∷ V "y" ∷ THEN ∷ V "z" ∷ ELSE ∷ V "x" ∷
--                     ELSE ∷ FALSE ∷ []) ≡
--         just (if (var "x") (if (var "y") (var "z") (var "x"))
--                            (val false))
-- test₂ = refl
