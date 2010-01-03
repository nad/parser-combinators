------------------------------------------------------------------------
-- A small library of derived parser combinators
------------------------------------------------------------------------

module TotalParserCombinators.Lib where

open import Category.Monad
open import Coinduction
open import Function
open import Function.Equality using (_⟶_)
open import Function.Injection using (Injection; Injective)
open import Data.List as List
open import Data.List.Any as Any
open import Data.List.Any.Properties as AnyProp
open import Data.Nat
open import Data.Product as Prod
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Relation.Binary
open import Relation.Binary.HeterogeneousEquality as H
open import Relation.Binary.PropositionalEquality as P
open import Relation.Nullary

open Any.Membership-≡
private
  open module ListMonad = RawMonad List.monad
         using () renaming (_>>=_ to _>>=′_)

open import TotalParserCombinators.Applicative
open import TotalParserCombinators.Coinduction
import TotalParserCombinators.InitialSet as I
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics hiding (_≅_)

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
  complete (_∷_ {s₁ = []}    x∈p xs∈p⋆) with I.complete x∈p
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
    lemma (suc i) = return ∷ lemma i

------------------------------------------------------------------------
-- Variants of some of the parser combinators

-- These variants hide the use of ∞?.

private

  drop-♭♯ : ∀ {Tok R R′ xs′} {p : Parser Tok R′ xs′} (xs : List R) →
            ♭? (♯? {xs = xs} p) ⊑ p
  drop-♭♯ xs = cast∈ refl (♭?♯? xs) refl

  add-♭♯ : ∀ {Tok R R′ xs′} {p : Parser Tok R′ xs′} (xs : List R) →
           p ⊑ ♭? (♯? {xs = xs} p)
  add-♭♯ xs = cast∈ refl (P.sym $ ♭?♯? xs) refl

infixl 10 _⊙_

_⊙_ : ∀ {Tok R₁ R₂ fs xs} →
      Parser Tok (R₁ → R₂) fs → Parser Tok R₁ xs →
      Parser Tok R₂ (fs ⊛′ xs)
p₁ ⊙ p₂ = ♯? p₁ ⊛ ♯? p₂

module ⊙ {Tok R₁ R₂ : Set} where

  complete : ∀ {fs xs s₁ s₂ f x}
               {p₁ : Parser Tok (R₁ → R₂) fs}
               {p₂ : Parser Tok R₁        xs} →
             f ∈ p₁ · s₁ → x ∈ p₂ · s₂ → f x ∈ p₁ ⊙ p₂ · s₁ ++ s₂
  complete {fs} {xs} ∈p₁ ∈p₂ = add-♭♯ xs ∈p₁ ⊛ add-♭♯ fs ∈p₂

  infixl 10 _⊙′_
  infix   4 _⊙_·_∋_

  data _⊙_·_∋_ {fs xs}
               (p₁ : Parser Tok (R₁ → R₂) fs) (p₂ : Parser Tok R₁ xs) :
               List Tok → R₂ → Set₁ where
    _⊙′_ : ∀ {f x s₁ s₂} (∈p₁ : f ∈ p₁ · s₁) (∈p₂ : x ∈ p₂ · s₂) →
           p₁ ⊙ p₂ · s₁ ++ s₂ ∋ f x

  sound : ∀ {fs} xs {fx s}
            {p₁ : Parser Tok (R₁ → R₂) fs}
            {p₂ : Parser Tok R₁        xs} →
          fx ∈ p₁ ⊙ p₂ · s → p₁ ⊙ p₂ · s ∋ fx
  sound {fs} xs (∈p₁ ⊛ ∈p₂) = drop-♭♯ xs ∈p₁ ⊙′ drop-♭♯ fs ∈p₂

infixl 10 _⟫=_

_⟫=_ : ∀ {Tok R₁ R₂ xs} {f : R₁ → List R₂} →
       Parser Tok R₁ xs → ((x : R₁) → Parser Tok R₂ (f x)) →
       Parser Tok R₂ (xs >>=′ f)
p₁ ⟫= p₂ = p₁ >>= λ x → ♯? (p₂ x)

module ⟫= {Tok R₁ R₂ : Set} where

  complete : ∀ {xs} {f : R₁ → List R₂} {x y s₁ s₂}
               {p₁ : Parser Tok R₁ xs}
               {p₂ : ((x : R₁) → Parser Tok R₂ (f x))} →
             x ∈ p₁ · s₁ → y ∈ p₂ x · s₂ → y ∈ p₁ ⟫= p₂ · s₁ ++ s₂
  complete {xs} ∈p₁ ∈p₂x = ∈p₁ >>= add-♭♯ xs ∈p₂x

  infixl 10 _⟫=′_
  infix   4 _⟫=_·_∋_

  data _⟫=_·_∋_ {xs} {f : R₁ → List R₂}
                (p₁ : Parser Tok R₁ xs)
                (p₂ : ((x : R₁) → Parser Tok R₂ (f x))) :
                List Tok → R₂ → Set₁ where
    _⟫=′_ : ∀ {x y s₁ s₂} (∈p₁ : x ∈ p₁ · s₁) (∈p₂x : y ∈ p₂ x · s₂) →
            p₁ ⟫= p₂ · s₁ ++ s₂ ∋ y

  sound : ∀ xs {f : R₁ → List R₂} {y s}
            {p₁ : Parser Tok R₁ xs}
            {p₂ : ((x : R₁) → Parser Tok R₂ (f x))} →
          y ∈ p₁ ⟫= p₂ · s → p₁ ⟫= p₂ · s ∋ y
  sound xs (∈p₁ >>= ∈p₂x) = ∈p₁ ⟫=′ drop-♭♯ xs ∈p₂x

------------------------------------------------------------------------
-- A combinator for recognising a string a fixed number of times

infixl 55 _^_ _↑_

^-initial : ∀ {R} → List R → (n : ℕ) → List (Vec R n)
^-initial _ zero    = _
^-initial _ (suc _) = _

_^_ : ∀ {Tok R xs} →
      Parser Tok R xs → (n : ℕ) → Parser Tok (Vec R n) (^-initial xs n)
p ^ 0     = return []
p ^ suc n = _∷_ <$> p ⊙ p ^ n

-- A variant.

↑-initial : ∀ {R} → List R → ℕ → List (List R)
↑-initial _ _ = _

_↑_ : ∀ {Tok R xs} →
      Parser Tok R xs → (n : ℕ) → Parser Tok (List R) (↑-initial xs n)
p ↑ n = Vec.toList <$> p ^ n

-- Some lemmas relating _↑_ to _⋆.

module Exactly where

  open ⊙ using (_⊙′_)

  ↑⊑⋆ : ∀ {Tok R} {p : Parser Tok R []} n → p ↑ n ⊑ p ⋆
  ↑⊑⋆ {R = R} {p} n (<$> ∈pⁿ) = KleeneStar.complete $ helper n ∈pⁿ
    where
    helper : ∀ n {xs s} → xs ∈ p ^ n · s → Vec.toList xs ∈[ p ]⋆· s
    helper zero    return = []
    helper (suc n) ∈⊙ⁿ    with ⊙.sound (^-initial [] n) ∈⊙ⁿ
    ... | <$> ∈p ⊙′ ∈pⁿ = ∈p ∷ helper n ∈pⁿ

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
          Prod.map (P.cong (_∷_ _))
                   (λ ∈pⁱ → ⊙.complete (<$> ∈p) ∈pⁱ)))
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

  complete∘sound : ∀ {Tok R x} {s : List Tok}
                   (xs : List R) (x∈xs : x ∈ return⋆ xs · s) →
                   complete {Tok = Tok} (proj₂ $ sound xs x∈xs) ≅ x∈xs
  complete∘sound []       ()
  complete∘sound (y ∷ ys) (∣ˡ return)        = refl
  complete∘sound (y ∷ ys) (∣ʳ .([ y ]) x∈ys)
    with sound ys x∈ys | complete∘sound ys x∈ys
  complete∘sound (y ∷ ys) (∣ʳ .([ y ]) .(complete (proj₂ p)))
    | p | refl = refl

  sound∘complete : ∀ {Tok R x} {xs : List R} (x∈xs : x ∈ xs) →
                   sound {Tok = Tok} {s = []} xs (complete x∈xs) ≡
                   (refl , x∈xs)
  sound∘complete       (here refl)            = refl
  sound∘complete {Tok} (there {xs = xs} x∈xs)
    with sound {Tok = Tok} xs (complete x∈xs)
       | sound∘complete {Tok} {xs = xs} x∈xs
  sound∘complete (there x∈xs) | .(refl , x∈xs) | refl = refl

------------------------------------------------------------------------
-- A parser for a given token

module Token
         (Tok : Set)
         (_≟_ : Decidable (_≡_ {A = Tok}))
         where

  private
    ok-index : Tok → Tok → List Tok
    ok-index tok tok′ with tok ≟ tok′
    ... | yes _ = tok′ ∷ []
    ... | no  _ = []

    ok : (tok tok′ : Tok) → Parser Tok Tok (ok-index tok tok′)
    ok tok tok′ with tok ≟ tok′
    ... | yes _ = return tok′
    ... | no  _ = fail

  tok : Tok → Parser Tok Tok []
  tok tok = token >>= λ tok′ → ♯? (ok tok tok′)

  sound : ∀ {t t′ s} →
          t′ ∈ tok t · s → t ≡ t′ × s ≡ [ t′ ]
  sound {t} (_>>=_ {x = t″} token t′∈) with t ≟ t″
  sound (token >>= return) | yes t≈t″ = (t≈t″ , refl)
  sound (token >>= ())     | no  t≉t″

  private
    ok-lemma : ∀ t → t ∈ ok t t · []
    ok-lemma t with t ≟ t
    ... | yes refl = return
    ... | no  t≢t  with t≢t refl
    ...   | ()

  complete : ∀ {t} → t ∈ tok t · [ t ]
  complete {t} = token >>= ok-lemma t

  η : ∀ {t} (t∈ : t ∈ tok t · [ t ]) → t∈ ≡ complete {t = t}
  η {t = t} t∈ = H.≅-to-≡ $ helper t∈ refl
    where
    helper₂ : (t∈ : t ∈ ok t t · []) → t∈ ≡ ok-lemma t
    helper₂ t∈     with t ≟ t
    helper₂ return | yes refl = refl
    helper₂ t∈     | no  t≢t  with t≢t refl
    helper₂ t∈     | no  t≢t  | ()

    helper : ∀ {s} (t∈ : t ∈ tok t · s) → s ≡ [ t ] →
             t∈ ≅ complete {t = t}
    helper (token >>= t∈) refl rewrite helper₂ t∈ = refl

------------------------------------------------------------------------
-- Map then choice

-- y ∈ ⋁ f xs · s  iff  ∃ x ∈ xs. y ∈ f x · s.

⋁-initial : {R₁ R₂ : Set} → (R₁ → List R₂) → List R₁ → List R₂
⋁-initial e []       = _
⋁-initial e (x ∷ xs) = _

⋁ : ∀ {Tok R₁ R₂} {f : R₁ → List R₂} →
    ((x : R₁) → Parser Tok R₂ (f x)) → (xs : List R₁) →
    Parser Tok R₂ (⋁-initial f xs)
⋁ f []       = fail
⋁ f (x ∷ xs) = f x ∣ ⋁ f xs

module ⋁ where

  sound : ∀ {Tok R₁ R₂ y s} {i : R₁ → List R₂} →
          (f : (x : R₁) → Parser Tok R₂ (i x)) (xs : List R₁) →
          y ∈ ⋁ f xs · s → ∃ λ x → (x ∈ xs) × (y ∈ f x · s)
  sound f []       ()
  sound f (x ∷ xs) (∣ˡ    y∈fx)   = (x , here refl , y∈fx)
  sound f (x ∷ xs) (∣ʳ ._ y∈⋁fxs) =
    Prod.map id (Prod.map there id) (sound f xs y∈⋁fxs)

  complete : ∀ {Tok R₁ R₂ x y s} {i : R₁ → List R₂} →
             (f : (x : R₁) → Parser Tok R₂ (i x)) {xs : List R₁} →
             x ∈ xs → y ∈ f x · s → y ∈ ⋁ f xs · s
  complete         f (here  refl) y∈fx = ∣ˡ y∈fx
  complete {i = i} f (there x∈xs) y∈fx = ∣ʳ (i _) (complete f x∈xs y∈fx)

  complete∘sound : ∀ {Tok R₁ R₂ y s} {i : R₁ → List R₂} →
                   (f : (x : R₁) → Parser Tok R₂ (i x)) (xs : List R₁)
                   (y∈⋁fxs : y ∈ ⋁ f xs · s) →
                   let p = proj₂ $ sound f xs y∈⋁fxs in
                   complete f (proj₁ p) (proj₂ p) ≡ y∈⋁fxs
  complete∘sound         f []       ()
  complete∘sound         f (x ∷ xs) (∣ˡ    y∈fx)   = refl
  complete∘sound {i = i} f (x ∷ xs) (∣ʳ ._ y∈⋁fxs) =
    P.cong (∣ʳ (i x)) (complete∘sound f xs y∈⋁fxs)

  sound∘complete :
    ∀ {Tok R₁ R₂ x y s} {i : R₁ → List R₂} →
    (f : (x : R₁) → Parser Tok R₂ (i x)) {xs : List R₁} →
    (x∈xs : x ∈ xs) (y∈fx : y ∈ f x · s) →
    sound f xs (complete f x∈xs y∈fx) ≡ (x , x∈xs , y∈fx)
  sound∘complete f (here  refl) y∈fx = refl
  sound∘complete f (there x∈xs) y∈fx
    rewrite sound∘complete f x∈xs y∈fx = refl
