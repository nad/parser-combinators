------------------------------------------------------------------------
-- A small library of derived parser combinators
------------------------------------------------------------------------

module TotalParserCombinators.Lib where

open import Category.Monad
open import Coinduction
open import Function
open import Function.Equality using (_⟶_; _⟨$⟩_)
open import Function.Injection using (Injection; Injective)
open import Function.Inverse using (_↔_; module Inverse)
open import Data.Bool
open import Data.Char as Char using (Char; _==_)
open import Data.List as List
open import Data.List.Any as Any
import Data.List.Any.Membership as ∈
open import Data.Maybe
open import Data.Nat
open import Data.Product as Prod
open import Data.Unit using (⊤)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Level
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary
open import Relation.Nullary.Decidable

open Any.Membership-≡
private
  open module ListMonad = RawMonad {f = Level.zero} List.monad
         using () renaming (_⊛_ to _⊛′_; _>>=_ to _>>=′_)

import TotalParserCombinators.InitialBag as I
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics as S
  hiding (_≅_; return; token)

------------------------------------------------------------------------
-- Kleene star

-- The intended semantics of the Kleene star.

infixr 5 _∷_
infix  4 _∈[_]⋆·_

data _∈[_]⋆·_ {Tok R xs} :
              List R → Parser Tok R xs → List Tok → Set₁ where
  []  : ∀ {p} → [] ∈[ p ]⋆· []
  _∷_ : ∀ {x xs s₁ s₂ p} →
        (x∈p : x ∈ p · s₁) (xs∈p⋆ : xs ∈[ p ]⋆· s₂) →
        x ∷ xs ∈[ p ]⋆· s₁ ++ s₂

-- An implementation which requires that the argument parser is not
-- nullable.

infix 55 _⋆ _+

mutual

  _⋆ : ∀ {Tok R} →
       Parser Tok R        [] →
       Parser Tok (List R) [ [] ]
  p ⋆ = return [] ∣ p +

  _+ : ∀ {Tok R} →
       Parser Tok R        [] →
       Parser Tok (List R) []
  p + = _∷_ <$> p ⊛ ♯ (p ⋆)

module KleeneStar where

  -- The implementation is correct.

  mutual

    sound : ∀ {Tok R xs s} {p : Parser Tok R []} →
            xs ∈ p ⋆ · s → xs ∈[ p ]⋆· s
    sound xs∈ = sound′ xs∈ refl

    private

      sound′ : ∀ {Tok R xs ys s}
                 {p : Parser Tok R []} {p⋆ : Parser Tok (List R) ys} →
               xs ∈ p⋆ · s → p⋆ ≅ p ⋆ → xs ∈[ p ]⋆· s
      sound′ (∣-left []∈)              refl with []∈
      ... | S.return = []
      sound′ (∣-right .([ [] ]) x∷xs∈) refl with x∷xs∈
      ... | <$> x∈p ⊛ xs∈p⋆ = x∈p ∷ sound xs∈p⋆
      sound′ S.return     ()
      sound′ S.token      ()
      sound′ (<$> _)      ()
      sound′ (_ ⊛ _)      ()
      sound′ (_ >>= _)    ()
      sound′ (nonempty _) ()
      sound′ (cast _)     ()

  complete : ∀ {Tok R xs s} {p : Parser Tok R []} →
             xs ∈[ p ]⋆· s → xs ∈ p ⋆ · s
  complete []                           = ∣-left S.return
  complete (_∷_ {s₁ = []}    x∈p xs∈p⋆) with I.complete x∈p
  ... | ()
  complete (_∷_ {s₁ = _ ∷ _} x∈p xs∈p⋆) =
    ∣-right [ [] ] ([ ○ - ◌ ] <$> x∈p ⊛ complete xs∈p⋆)

  mutual

    complete∘sound :
      ∀ {Tok R xs s} {p : Parser Tok R []} (xs∈ : xs ∈ p ⋆ · s) →
      complete (sound xs∈) ≡ xs∈
    complete∘sound xs∈ = H.≅-to-≡ $ complete∘sound′ xs∈ refl

    private

      complete∘sound′ :
        ∀ {Tok R xs ys s}
          {p : Parser Tok R []} {p⋆ : Parser Tok (List R) ys}
        (xs∈ : xs ∈ p⋆ · s) (eq : p⋆ ≅ p ⋆) →
        complete (sound′ xs∈ eq) ≅ xs∈
      complete∘sound′ (∣-left []∈)              refl with []∈
      ... | S.return = refl
      complete∘sound′ (∣-right .([ [] ]) x∷xs∈) refl with x∷xs∈
      ... | _⊛_ {s₁ = _ ∷ _} (<$> x∈p) xs∈p⋆
            rewrite complete∘sound xs∈p⋆ = refl
      ... | _⊛_ {s₁ = []}    (<$> x∈p) xs∈p⋆ with I.complete x∈p
      ...   | ()
      complete∘sound′ S.return     ()
      complete∘sound′ S.token      ()
      complete∘sound′ (<$> _)      ()
      complete∘sound′ (_ ⊛ _)      ()
      complete∘sound′ (_ >>= _)    ()
      complete∘sound′ (nonempty _) ()
      complete∘sound′ (cast _)     ()

  sound∘complete : ∀ {Tok R xs s} {p : Parser Tok R []}
                   (xs∈ : xs ∈[ p ]⋆· s) →
                   sound (complete xs∈) ≡ xs∈
  sound∘complete []                           = refl
  sound∘complete (_∷_ {s₁ = []}    x∈p xs∈p⋆) with I.complete x∈p
  ... | ()
  sound∘complete (_∷_ {s₁ = _ ∷ _} x∈p xs∈p⋆) =
    P.cong (_∷_ x∈p) $ sound∘complete xs∈p⋆

  correct : ∀ {Tok R xs s} {p : Parser Tok R []} →
            xs ∈ p ⋆ · s ↔ xs ∈[ p ]⋆· s
  correct = record
    { to         = P.→-to-⟶ sound
    ; from       = P.→-to-⟶ complete
    ; inverse-of = record
      { left-inverse-of  = complete∘sound
      ; right-inverse-of = sound∘complete
      }
    }

  -- The definition of _⋆ is restricted to non-nullable parsers. This
  -- restriction cannot be removed: an unrestricted Kleene star
  -- operator would be incomplete because, in the present framework, a
  -- parser can only return a finite number of results.

  unrestricted-incomplete :
    ∀ {R Tok} →
    R →
    (f : ∀ {xs} → Parser Tok R xs → List (List R)) →
    (_⋆′ : ∀ {xs} (p : Parser Tok R xs) → Parser Tok (List R) (f p)) →
    ¬ (∀ {xs ys s} {p : Parser Tok R ys} →
         xs ∈[ p ]⋆· s → xs ∈ p ⋆′ · s)
  unrestricted-incomplete {R} x f _⋆′ complete =
    ∈.finite (record { to = to; injective = injective })
             (f (return x)) (I.complete ∘ complete ∘ lemma)
    where
    to : P.setoid ℕ ⟶ P.setoid (List R)
    to = →-to-⟶ (flip replicate x)

    helper : ∀ {xs ys} → _≡_ {A = List R} (x ∷ xs) (x ∷ ys) → xs ≡ ys
    helper refl = refl

    injective : Injective to
    injective {zero}  {zero}  _  = refl
    injective {suc m} {suc n} eq = P.cong suc $
                                     injective $ helper eq
    injective {zero}  {suc n} ()
    injective {suc m} {zero}  ()

    lemma : ∀ i → replicate i x ∈[ return x ]⋆· []
    lemma zero    = []
    lemma (suc i) = S.return ∷ lemma i

------------------------------------------------------------------------
-- A combinator for recognising a string a fixed number of times

-- The functions below are not actually mutually recursive, but are
-- placed in mutual blocks to ensure that the constraints generated by
-- the latter ones can be used to instantiate the underscores in the
-- bodies of the first ones.

infixl 55 _^_ _↑_

mutual

  ^-initial : ∀ {R} → List R → (n : ℕ) → List (Vec R n)
  ^-initial _ zero    = _
  ^-initial _ (suc _) = _

  _^_ : ∀ {Tok R xs} →
        Parser Tok R xs → (n : ℕ) → Parser Tok (Vec R n) (^-initial xs n)
  p ^ 0     = return []
  p ^ suc n = _∷_ <$> p ⊛ p ^ n

mutual

  -- A variant.

  ↑-initial : ∀ {R} → List R → ℕ → List (List R)
  ↑-initial _ _ = _

  _↑_ : ∀ {Tok R xs} →
        Parser Tok R xs → (n : ℕ) → Parser Tok (List R) (↑-initial xs n)
  p ↑ n = Vec.toList <$> p ^ n

-- Some lemmas relating _↑_ to _⋆.

module Exactly where

  ↑≲⋆ : ∀ {Tok R} {p : Parser Tok R []} n → p ↑ n ≲ p ⋆
  ↑≲⋆ {R = R} {p} n (<$> ∈pⁿ) = KleeneStar.complete $ helper n ∈pⁿ
    where
    helper : ∀ n {xs s} → xs ∈ p ^ n · s → Vec.toList xs ∈[ p ]⋆· s
    helper zero    S.return       = []
    helper (suc n) (<$> ∈p ⊛ ∈pⁿ) = ∈p ∷ helper n ∈pⁿ

  ⋆≲∃↑ : ∀ {Tok R} {p : Parser Tok R []} {xs s} →
         xs ∈ p ⋆ · s → ∃ λ i → xs ∈ p ↑ i · s
  ⋆≲∃↑ {R = R} {p} ∈p⋆ with helper $ KleeneStar.sound ∈p⋆
    where
    helper : ∀ {xs s} → xs ∈[ p ]⋆· s →
             ∃₂ λ i (ys : Vec R i) →
                  xs ≡ Vec.toList ys × ys ∈ p ^ i · s
    helper []         = (0 , [] , refl , S.return)
    helper (∈p ∷ ∈p⋆) =
      Prod.map suc (λ {i} →
        Prod.map (_∷_ _) (
          Prod.map (P.cong (_∷_ _))
                   (λ ∈pⁱ → [ ○ - ○ ] <$> ∈p ⊛ ∈pⁱ)))
       (helper ∈p⋆)
  ... | (i , ys , refl , ∈pⁱ) = (i , <$> ∈pⁱ)

------------------------------------------------------------------------
-- A parser which returns any element in a given list

return⋆ : ∀ {Tok R} (xs : List R) → Parser Tok R xs
return⋆ []       = fail
return⋆ (x ∷ xs) = return x ∣ return⋆ xs

module Return⋆ where

  sound : ∀ {Tok R x} {s : List Tok}
          (xs : List R) → x ∈ return⋆ xs · s → s ≡ [] × x ∈ xs
  sound []       ()
  sound (y ∷ ys) (∣-left S.return)       = (refl , here refl)
  sound (y ∷ ys) (∣-right .([ y ]) x∈ys) =
    Prod.map id there $ sound ys x∈ys

  complete : ∀ {Tok R x} {xs : List R} →
             x ∈ xs → x ∈ return⋆ {Tok} xs · []
  complete (here refl)  = ∣-left S.return
  complete (there x∈xs) =
    ∣-right [ _ ] (complete x∈xs)

  complete∘sound : ∀ {Tok R x} {s : List Tok}
                   (xs : List R) (x∈xs : x ∈ return⋆ xs · s) →
                   complete {Tok = Tok} (proj₂ $ sound xs x∈xs) ≅ x∈xs
  complete∘sound []       ()
  complete∘sound (y ∷ ys) (∣-left S.return)       = refl
  complete∘sound (y ∷ ys) (∣-right .([ y ]) x∈ys)
    with sound ys x∈ys | complete∘sound ys x∈ys
  complete∘sound (y ∷ ys) (∣-right .([ y ]) .(complete p))
    | (refl , p) | refl = refl

  sound∘complete : ∀ {Tok R x} {xs : List R} (x∈xs : x ∈ xs) →
                   sound {Tok = Tok} {s = []} xs (complete x∈xs) ≡
                   (refl , x∈xs)
  sound∘complete       (here refl)            = refl
  sound∘complete {Tok} (there {xs = xs} x∈xs)
    with sound {Tok = Tok} xs (complete x∈xs)
       | sound∘complete {Tok} {xs = xs} x∈xs
  sound∘complete (there x∈xs) | .(refl , x∈xs) | refl = refl

  correct : ∀ {Tok R} {xs : List R} {x s} →
            (s ≡ [] × x ∈ xs) ↔ x ∈ return⋆ {Tok} xs · s
  correct {xs = xs} {x} = record
    { to         = P.→-to-⟶ complete′
    ; from       = P.→-to-⟶ $ sound xs
    ; inverse-of = record
      { left-inverse-of  = sound∘complete′
      ; right-inverse-of = complete′∘sound xs
      }
    }
    where
    complete′ : ∀ {Tok R x} {xs : List R} {s : List Tok} →
                s ≡ [] × x ∈ xs → x ∈ return⋆ xs · s
    complete′ (refl , x∈xs) = complete x∈xs

    sound∘complete′ : ∀ {Tok R x} {xs : List R} {s : List Tok}
                      (p : s ≡ [] × x ∈ xs) → sound xs (complete′ p) ≡ p
    sound∘complete′ (refl , x∈xs) = sound∘complete x∈xs

    complete′∘sound : ∀ {Tok R x} {s : List Tok}
                      (xs : List R) (x∈xs : x ∈ return⋆ xs · s) →
                      complete′ (sound xs x∈xs) ≡ x∈xs
    complete′∘sound xs x∈ with sound xs x∈ | complete∘sound xs x∈
    complete′∘sound xs .(complete x∈xs) | (refl , x∈xs) | refl = refl

------------------------------------------------------------------------
-- The sat parser

module Sat where

  -- Helper functions for sat.

  mutual

    ok-bag : {R : Set} → Maybe R → List R
    ok-bag nothing  = _
    ok-bag (just _) = _

    ok : {Tok R : Set} → (x : Maybe R) → Parser Tok R (ok-bag x)
    ok nothing  = fail
    ok (just x) = return x

  ok-correct : ∀ {Tok R x s} (m : Maybe R) →
               (s ≡ [] × m ≡ just x) ↔ x ∈ ok {Tok} m · s
  ok-correct {Tok} {x = x} m = record
    { to         = P.→-to-⟶ (to m)
    ; from       = P.→-to-⟶ (from m)
    ; inverse-of = record
      { left-inverse-of  = from∘to m
      ; right-inverse-of = to∘from m
      }
    }
    where
    to : ∀ {s} m → (s ≡ [] × m ≡ just x) → x ∈ ok {Tok} m · s
    to (just .x) (refl , refl) = S.return
    to nothing   (refl , ())

    from : ∀ {s} m → x ∈ ok {Tok} m · s → s ≡ [] × m ≡ just x
    from (just .x) S.return = (refl , refl)
    from nothing   ()

    from∘to : ∀ {s} m (eqs : s ≡ [] × m ≡ just x) →
              from m (to m eqs) ≡ eqs
    from∘to (just .x) (refl , refl) = refl
    from∘to nothing   (refl , ())

    to∘from : ∀ {s} m (x∈ : x ∈ ok {Tok} m · s) →
              to m (from m x∈) ≡ x∈
    to∘from (just .x) S.return = refl
    to∘from nothing   ()

  -- sat p accepts a single token t iff p t ≡ just x for some x. The
  -- returned value is x.

  sat : ∀ {Tok R} → (Tok → Maybe R) → Parser Tok R _
  sat p = token >>= (ok ∘ p)

  correct : ∀ {Tok R x s} (p : Tok → Maybe R) →
            (∃ λ t → s ≡ [ t ] × p t ≡ just x) ↔ x ∈ sat p · s
  correct {x = x} p = record
    { to         = P.→-to-⟶ to
    ; from       = P.→-to-⟶ from
    ; inverse-of = record
      { left-inverse-of  = from∘to
      ; right-inverse-of = to∘from
      }
    }
    where
    to : ∀ {s} → (∃ λ t → s ≡ [ t ] × p t ≡ just x) → x ∈ sat p · s
    to (t , refl , p-t≡just-x) =
      [ ○ - ○ ] S.token >>=
                (Inverse.to (ok-correct (p t)) ⟨$⟩ (refl , p-t≡just-x))

    from : ∀ {s} → x ∈ sat p · s → ∃ λ t → s ≡ [ t ] × p t ≡ just x
    from (S.token {x = t} >>= x∈ok-p-t) =
      (t , Prod.map (P.cong (_∷_ t)) id
             (Inverse.from (ok-correct (p t)) ⟨$⟩ x∈ok-p-t))

    from∘to : ∀ {s} (eqs : ∃ λ t → s ≡ [ t ] × p t ≡ just x) →
              from (to eqs) ≡ eqs
    from∘to (t , refl , p-t≡just-x) =
      P.cong₂ (λ eq₁ eq₂ → (t , eq₁ , eq₂))
              (P.proof-irrelevance _ _)
              (P.proof-irrelevance _ _)

    to∘from : ∀ {s} (x∈ : x ∈ sat p · s) → to (from x∈) ≡ x∈
    to∘from (S.token {x = t} >>= x∈ok-p-t)
      with Inverse.from (ok-correct (p t)) ⟨$⟩ x∈ok-p-t
         | Inverse.right-inverse-of (ok-correct (p t)) x∈ok-p-t
    to∘from (S.token {x = t} >>= .(Inverse.to (ok-correct (p t)) ⟨$⟩
                                     (refl , p-t≡just-x)))
      | (refl , p-t≡just-x) | refl = refl

open Sat public using (sat)

-- A simplified variant of sat. Does not return anything interesting.

sat′ : ∀ {Tok} → (Tok → Bool) → Parser Tok ⊤ _
sat′ p = sat (boolToMaybe ∘ p)

-- Accepts a single whitespace character (from a limited set of such
-- characters).

whitespace : Parser Char ⊤ _
whitespace = sat′ isSpace
  where
  isSpace = λ c →
    (c == ' ') ∨ (c == '\t') ∨ (c == '\n') ∨ (c == '\r')

------------------------------------------------------------------------
-- A parser for a given token

module Token
         (Tok : Set)
         (_≟_ : Decidable (_≡_ {A = Tok}))
         where

  private
    p : Tok → Tok → Maybe Tok
    p t t′ = if ⌊ t ≟ t′ ⌋ then just t′ else nothing

  tok : Tok → Parser Tok Tok []
  tok t = sat (p t)

  sound : ∀ t {t′ s} →
          t′ ∈ tok t · s → t ≡ t′ × s ≡ [ t′ ]
  sound t t′∈ with Inverse.from (Sat.correct (p t)) ⟨$⟩ t′∈
  sound t t′∈ | (t″ , refl , p-t-t″≡just-t′) with t ≟ t″
  sound t t∈  | (.t , refl , refl) | yes refl = (refl , refl)
  sound t t′∈ | (t″ , refl , ())   | no  _

  private
    p-lemma : ∀ t → p t t ≡ just t
    p-lemma t with t ≟ t
    ... | yes refl = refl
    ... | no  t≢t  with t≢t refl
    ...   | ()

  complete : ∀ {t} → t ∈ tok t · [ t ]
  complete {t} =
    Inverse.to (Sat.correct (p t)) ⟨$⟩ (t , refl , p-lemma t)

  η : ∀ {t} (t∈ : t ∈ tok t · [ t ]) → t∈ ≡ complete {t = t}
  η {t = t} t∈ = H.≅-to-≡ $ helper t∈ refl
    where
    helper₂ : (t∈ : t ∈ Sat.ok {Tok = Tok} (p t t) · []) →
              t∈ ≡ Inverse.to (Sat.ok-correct (p t t)) ⟨$⟩
                     (refl , p-lemma t)
    helper₂ t∈       with t ≟ t
    helper₂ S.return | yes refl = refl
    helper₂ t∈       | no  t≢t  with t≢t refl
    helper₂ t∈       | no  t≢t  | ()

    helper : ∀ {s} (t∈ : t ∈ tok t · s) → s ≡ [ t ] →
             t∈ ≅ complete {t = t}
    helper (S.token >>= t∈) refl rewrite helper₂ t∈ = refl

------------------------------------------------------------------------
-- Map then choice

-- y ∈ ⋁ f xs · s  iff  ∃ x ∈ xs. y ∈ f x · s.

⋁ : ∀ {Tok R₁ R₂} {f : R₁ → List R₂} →
    ((x : R₁) → Parser Tok R₂ (f x)) → (xs : List R₁) →
    Parser Tok R₂ (xs >>=′ f)
⋁ f xs = return⋆ xs >>= f

module ⋁ where

  sound : ∀ {Tok R₁ R₂ y s} {i : R₁ → List R₂} →
          (f : (x : R₁) → Parser Tok R₂ (i x)) (xs : List R₁) →
          y ∈ ⋁ f xs · s → ∃ λ x → (x ∈ xs) × (y ∈ f x · s)
  sound f xs (∈ret⋆ >>= y∈fx) with Return⋆.sound xs ∈ret⋆
  ...   | (refl , x∈xs) = (_ , x∈xs , y∈fx)

  complete : ∀ {Tok R₁ R₂ x y s} {i : R₁ → List R₂} →
             (f : (x : R₁) → Parser Tok R₂ (i x)) {xs : List R₁} →
             x ∈ xs → y ∈ f x · s → y ∈ ⋁ f xs · s
  complete f x∈xs y∈fx =
    [ ○ - ○ ] Return⋆.complete x∈xs >>= y∈fx

  complete∘sound : ∀ {Tok R₁ R₂ y s} {i : R₁ → List R₂} →
                   (f : (x : R₁) → Parser Tok R₂ (i x)) (xs : List R₁)
                   (y∈⋁fxs : y ∈ ⋁ f xs · s) →
                   let p = proj₂ $ sound f xs y∈⋁fxs in
                   complete f (proj₁ p) (proj₂ p) ≡ y∈⋁fxs
  complete∘sound f xs (∈ret⋆ >>= y∈fx)
    with Return⋆.sound xs ∈ret⋆
       | Inverse.right-inverse-of Return⋆.correct ∈ret⋆
  complete∘sound f xs (.(Return⋆.complete x∈xs) >>= y∈fx)
    | (refl , x∈xs) | refl = refl

  sound∘complete :
    ∀ {Tok R₁ R₂ x y s} {i : R₁ → List R₂} →
    (f : (x : R₁) → Parser Tok R₂ (i x)) {xs : List R₁} →
    (x∈xs : x ∈ xs) (y∈fx : y ∈ f x · s) →
    sound f xs (complete f x∈xs y∈fx) ≡ (x , x∈xs , y∈fx)
  sound∘complete {Tok} f {xs} x∈xs y∈fx
    with Return⋆.sound {Tok = Tok} xs (Return⋆.complete x∈xs)
       | Inverse.left-inverse-of (Return⋆.correct {Tok = Tok})
                                 (refl , x∈xs)
  ... | (refl , .x∈xs) | refl = refl

------------------------------------------------------------------------
-- Digits and numbers

-- Digits.

digit = sat (λ t → if in-range t then just (to-number t) else nothing)
  where
  in-range : Char → Bool
  in-range t = ⌊ Char.toNat '0' ≤? Char.toNat  t  ⌋ ∧
               ⌊ Char.toNat  t  ≤? Char.toNat '9' ⌋

  to-number : Char → ℕ
  to-number t = Char.toNat t ∸ Char.toNat '0'

-- Numbers.

number : Parser Char ℕ _
number = digit + >>= (return ∘ foldl (λ n d → 10 * n + d) 0)
