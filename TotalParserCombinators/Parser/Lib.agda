------------------------------------------------------------------------
-- A very small library of derived parser combinators
------------------------------------------------------------------------

module TotalParserCombinators.Parser.Lib where

open import Coinduction
open import Data.Function
open import Data.List
open import Data.List.Any
open Membership-≡
open import Data.List.Any.Properties as AnyProp
open import Data.Nat
open import Data.Product as Prod
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Relation.Binary
open import Relation.Binary.FunctionSetoid
open import Relation.Binary.HeterogeneousEquality
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Nullary

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Parser.Semantics
  hiding (sound; sound′; complete)

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
  p + = ⟨ _∷_ <$> p ⟩ ⊛ ⟪ ♯ (p ⋆) ⟫

module KleeneStar where

  -- The implementation is correct.

  sound : ∀ {Tok R xs s} {p : Parser Tok R []} →
          xs ∈ p ⋆ · s → xs ∈[ p ]⋆· s
  sound xs∈ = sound′ xs∈ refl
    where
    sound′ : ∀ {Tok R xs ys s}
               {p : Parser Tok R []} {p⋆ : Parser Tok (List R) ys} →
             xs ∈ p⋆ · s → p⋆ ≅ p ⋆ → xs ∈[ p ]⋆· s
    sound′ (∣ˡ []∈)             refl with []∈
    ... | return = []
    sound′ (∣ʳ .([ [] ]) x∷xs∈) refl with x∷xs∈
    ... | <$> x∈p ⊛ xs∈p⋆ = x∈p ∷ sound xs∈p⋆
    sound′ return       ()
    sound′ token        ()
    sound′ (<$> _)      ()
    sound′ (_ ⊛ _)      ()
    sound′ (_ >>= _)    ()
    sound′ (_ >>=! _)   ()
    sound′ (nonempty _) ()
    sound′ (cast _)     ()

  complete : ∀ {Tok R xs s} {p : Parser Tok R []} →
             xs ∈[ p ]⋆· s → xs ∈ p ⋆ · s
  complete []                           = ∣ˡ return
  complete (_∷_ {s₁ = []}    x∈p xs∈p⋆) with initial-complete x∈p
  ... | ()
  complete (_∷_ {s₁ = _ ∷ _} x∈p xs∈p⋆) =
    ∣ʳ [ [] ] (<$> x∈p ⊛ complete xs∈p⋆)

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
    AnyProp.Membership-≡.finite
      (record { to = to; injective = injective })
      (f (return x)) (initial-complete ∘ complete ∘ lemma)
    where
    to : PropEq.setoid ℕ ⟶ PropEq.setoid (List R)
    to = →-to-⟶ (flip replicate x)

    helper : ∀ {xs ys} → _≡_ {A = List R} (x ∷ xs) (x ∷ ys) → xs ≡ ys
    helper refl = refl

    injective : Injective to
    injective {zero}  {zero}  _  = refl
    injective {suc m} {suc n} eq = PropEq.cong suc $
                                     injective $ helper eq
    injective {zero}  {suc n} ()
    injective {suc m} {zero}  ()

    lemma : ∀ i → replicate i x ∈[ return x ]⋆· []
    lemma zero    = []
    lemma (suc i) = return ∷ lemma i

------------------------------------------------------------------------
-- A combinator for recognising a string a fixed number of times

infixl 55 _^_ _↑_

^-initial : ∀ {R} → List R → (n : ℕ) → List (Vec R n)
^-initial _ zero    = _
^-initial _ (suc _) = _

_^_ : ∀ {Tok R xs} →
      Parser Tok R xs → (n : ℕ) → Parser Tok (Vec R n) (^-initial xs n)
p ^ 0     = return []
p ^ suc n = ♯? (_∷_ <$> p) ⊛ ♯? (p ^ n)

-- A variant.

↑-initial : ∀ {R} → List R → ℕ → List (List R)
↑-initial _ _ = _

_↑_ : ∀ {Tok R xs} →
      Parser Tok R xs → (n : ℕ) → Parser Tok (List R) (↑-initial xs n)
p ↑ n = Vec.toList <$> p ^ n

-- Some lemmas relating _↑_ to _⋆.

module Exactly where

  ↑⊑⋆ : ∀ {Tok R} {p : Parser Tok R []} n → p ↑ n ⊑ p ⋆
  ↑⊑⋆ {R = R} {p} n (<$> ∈pⁿ) = KleeneStar.complete $ helper n ∈pⁿ
    where
    helper : ∀ n {xs s} → xs ∈ p ^ n · s → Vec.toList xs ∈[ p ]⋆· s
    helper zero    return     = []
    helper (suc n) (∈p ⊛ ∈pⁿ) with drop-♭♯ (^-initial [] n) ∈p
    ... | <$> ∈p′ = ∈p′ ∷ helper n (drop-♭♯ (List R ∶ []) ∈pⁿ)

  ⋆⊑↑ : ∀ {Tok R} {p : Parser Tok R []} {xs s} →
        xs ∈ p ⋆ · s → ∃ λ i → xs ∈ p ↑ i · s
  ⋆⊑↑ {R = R} {p} ∈p⋆ with helper $ KleeneStar.sound ∈p⋆
    where
    helper : ∀ {xs s} → xs ∈[ p ]⋆· s →
             ∃₂ λ i (ys : Vec R i) →
                  xs ≡ Vec.toList ys × ys ∈ p ^ i · s
    helper []         = (0 , [] , refl , return)
    helper (∈p ∷ ∈p⋆) =
      Prod.map suc (λ {i} →
        Prod.map (_∷_ _) (
          Prod.map (PropEq.cong (_∷_ _))
                   (λ ∈pⁱ → add-♭♯ (^-initial [] i) (<$> ∈p) ⊛ ∈pⁱ)))
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
  sound (y ∷ ys) (∣ˡ return)        = (refl , here refl)
  sound (y ∷ ys) (∣ʳ .([ y ]) x∈ys) =
    Prod.map id there $ sound ys x∈ys

  complete : ∀ {Tok R x} {xs : List R} →
             x ∈ xs → x ∈ return⋆ {Tok} xs · []
  complete (here refl)  = ∣ˡ return
  complete (there x∈xs) =
    ∣ʳ [ _ ] (complete x∈xs)

------------------------------------------------------------------------
-- A parser for a given token

module Token
         (Tok : Set)
         (_≟_ : Decidable (_≡_ {A = Tok}))
         where

  private
    okIndex : Tok → Tok → List Tok
    okIndex tok tok′ with tok ≟ tok′
    ... | yes _ = tok′ ∷ []
    ... | no  _ = []

    ok : (tok tok′ : Tok) → Parser Tok Tok (okIndex tok tok′)
    ok tok tok′ with tok ≟ tok′
    ... | yes _ = return tok′
    ... | no  _ = fail

  tok : Tok → Parser Tok Tok []
  tok tok = token >>= ♯? (ok tok)

  sound : ∀ {t t′ s} →
          t′ ∈ tok t · s → t ≡ t′ × s ≡ [ t′ ]
  sound {t} (_>>=_ {x = t″} token t′∈) with t ≟ t″
  sound (token >>= return) | yes t≈t″ = (t≈t″ , refl)
  sound (token >>= ())     | no  t≉t″

  complete : ∀ {t} → t ∈ tok t · [ t ]
  complete {t} = token >>= ok-lemma
    where
    ok-lemma : t ∈ ok t t · []
    ok-lemma with t ≟ t
    ... | yes refl = return
    ... | no  t≢t  with t≢t refl
    ...   | ()
