------------------------------------------------------------------------
-- An alternative definition of the parser type, which can lead to
-- less noisy definitions of parsers
------------------------------------------------------------------------

module TotalParserCombinators.LessNoisy where

open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Any as Any
open import Function using (const) renaming (_⟨_⟩_ to _⟨⟨_⟩⟩_)
open import Relation.Binary.PropositionalEquality as Eq
  using (_≡_; refl)

open Any.Membership-≡ renaming (_≈[_]_ to _List-≈[_]_)
open RawMonadPlus List.monadPlus
  using ()
  renaming ( return to return′
           ; ∅      to fail′
           ; _∣_    to _∣′_
           ; _>>=_  to _>>=′_
           )

open import TotalParserCombinators.Applicative using (_⊛′_)
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser as P hiding (Parser)
open import TotalParserCombinators.Semantics
  hiding (_≈_) renaming (_≈[_]_ to _P≈[_]_; _≅_ to _P≅_)

infixl 50 _⊛_ _<$>_
infixl 10 _>>=_ _∞>>=_
infixl  5 _∣_

------------------------------------------------------------------------
-- Parsers

-- This definition avoids the constructors ⟪_⟫ and ⟨_⟩, because
-- ∞⟨_⟩Parser evaluates.

mutual

  data Parser (Tok : Set) : (R : Set) → List R → Set₁ where
    return   : ∀ {R} (x : R) → Parser Tok R (return′ x)
    fail     : ∀ {R} → Parser Tok R fail′
    token    : Parser Tok Tok fail′
    _∣_      : ∀ {R xs₁ xs₂}
               (p₁ : Parser Tok R  xs₁       )
               (p₂ : Parser Tok R         xs₂) →
                     Parser Tok R (xs₁ ∣′ xs₂)
    _<$>_    : ∀ {R₁ R₂ xs}
               (f : R₁ → R₂)
               (p : Parser Tok R₁        xs) →
                    Parser Tok R₂ (map f xs)
    _⊛_      : ∀ {R₁ R₂ fs xs}
               (p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂)  fs      )
               (p₂ : ∞⟨ fs ⟩Parser Tok  R₁              xs) →
                            Parser Tok       R₂  (fs ⊛′ xs)
    _>>=_    : ∀ {R₁ R₂ xs} {f : R₁ → List R₂}
               (p₁ :                   Parser Tok R₁  xs          )
               (p₂ : (x : R₁) → ∞⟨ xs ⟩Parser Tok R₂         (f x)) →
                                       Parser Tok R₂ (xs >>=′ f)
    _∞>>=_   : ∀ {R₁ R₂ xs}
               (p₁ :      ∞     (Parser Tok R₁ xs))
               (p₂ : R₁ → ∞⟨ xs ⟩Parser Tok R₂ fail′) →
                                 Parser Tok R₂ fail′
    nonempty : ∀ {R xs} (p : Parser Tok R xs) → Parser Tok R []
    cast     : ∀ {R xs₁ xs₂} (xs₁≈xs₂ : xs₁ List-≈[ bag ] xs₂)
               (p : Parser Tok R xs₁) → Parser Tok R xs₂

  ∞⟨_⟩Parser : {R₂ : Set} → List R₂ → Set → (R₁ : Set) → List R₁ → Set₁
  ∞⟨ []    ⟩Parser Tok R₁ xs = ∞ (Parser Tok R₁ xs)
  ∞⟨ _ ∷ _ ⟩Parser Tok R₁ xs =    Parser Tok R₁ xs

-- Note that these parsers can be both left and right recursive:

private

  leftRight : ∀ {R Tok} → Parser Tok R []
  leftRight {R} = ♯ (const <$> leftRight) ⊛ ♯ leftRight {R}

------------------------------------------------------------------------
-- Semantics

-- For simplicity the semantics of Parser is defined by translation.

⟦_⟧ : ∀ {Tok R xs} → Parser Tok R xs → P.Parser Tok R xs
⟦ return x                            ⟧ = return x
⟦ fail                                ⟧ = fail
⟦ token                               ⟧ = token
⟦ p₁ ∣ p₂                             ⟧ = ⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧
⟦ f <$> p                             ⟧ = f <$> ⟦ p ⟧
⟦ _⊛_ {fs = _ ∷ _} {xs = _ ∷ _} p₁ p₂ ⟧ = ⟨   ⟦   p₁ ⟧ ⟩ ⊛ ⟨   ⟦   p₂ ⟧ ⟩
⟦ _⊛_ {fs = _ ∷ _} {xs = []   } p₁ p₂ ⟧ = ⟪ ♯ ⟦ ♭ p₁ ⟧ ⟫ ⊛ ⟨   ⟦   p₂ ⟧ ⟩
⟦ _⊛_ {fs = []   } {xs = _ ∷ _} p₁ p₂ ⟧ = ⟨   ⟦   p₁ ⟧ ⟩ ⊛ ⟪ ♯ ⟦ ♭ p₂ ⟧ ⟫
⟦ _⊛_ {fs = []   } {xs = []   } p₁ p₂ ⟧ = ⟪ ♯ ⟦ ♭ p₁ ⟧ ⟫ ⊛ ⟪ ♯ ⟦ ♭ p₂ ⟧ ⟫
⟦ _>>=_  {xs = _ ∷ _} p₁ p₂           ⟧ =    ⟦   p₁ ⟧  >>=  λ x → ⟨   ⟦    p₂ x  ⟧ ⟩
⟦ _>>=_  {xs = []   } p₁ p₂           ⟧ =    ⟦   p₁ ⟧  >>=  λ x → ⟪ ♯ ⟦ ♭ (p₂ x) ⟧ ⟫
⟦ _∞>>=_ {xs = _ ∷ _} p₁ p₂           ⟧ = (♯ ⟦ ♭ p₁ ⟧) ∞>>= λ x → ⟨   ⟦    p₂ x  ⟧ ⟩
⟦ _∞>>=_ {xs = []   } p₁ p₂           ⟧ = (♯ ⟦ ♭ p₁ ⟧) ∞>>= λ x → ⟪ ♯ ⟦ ♭ (p₂ x) ⟧ ⟫
⟦ nonempty p                          ⟧ = nonempty ⟦ p ⟧
⟦ cast xs₁≈xs₂ p                      ⟧ = cast xs₁≈xs₂ ⟦ p ⟧

-- We can also translate in the other direction.

mutual

  ⟦_⟧⁻¹ : ∀ {Tok R xs} → P.Parser Tok R xs → Parser Tok R xs
  ⟦ return x                  ⟧⁻¹ = return x
  ⟦ fail                      ⟧⁻¹ = fail
  ⟦ token                     ⟧⁻¹ = token
  ⟦ p₁ ∣ p₂                   ⟧⁻¹ = ⟦ p₁ ⟧⁻¹ ∣ ⟦ p₂ ⟧⁻¹
  ⟦ f <$> p                   ⟧⁻¹ = f <$> ⟦ p ⟧⁻¹
  ⟦ ⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩           ⟧⁻¹ =   ⟦   p₁ ⟧⁻¹ ⊛   ⟦   p₂ ⟧⁻¹
  ⟦ ⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩           ⟧⁻¹ = ♯ ⟦ ♭ p₁ ⟧⁻¹ ⊛   ⟦   p₂ ⟧⁻¹
  ⟦ ⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫           ⟧⁻¹ =   ⟦   p₁ ⟧⁻¹ ⊛ ♯ ⟦ ♭ p₂ ⟧⁻¹
  ⟦ ⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫           ⟧⁻¹ = ♯ ⟦ ♭ p₁ ⟧⁻¹ ⊛ ♯ ⟦ ♭ p₂ ⟧⁻¹
  ⟦ _>>=_  {xs = _ ∷ _} p₁ p₂ ⟧⁻¹ =   ⟦   p₁ ⟧⁻¹ >>=  λ x →   ⟦♭    p₂ x  ⟧⁻¹
  ⟦ _>>=_  {xs = []   } p₁ p₂ ⟧⁻¹ =   ⟦   p₁ ⟧⁻¹ >>=  λ x → ♯ ⟦ ♭? (p₂ x) ⟧⁻¹
  ⟦ _∞>>=_ {xs = _ ∷ _} p₁ p₂ ⟧⁻¹ = ♯ ⟦ ♭ p₁ ⟧⁻¹ ∞>>= λ x →   ⟦♭    p₂ x  ⟧⁻¹
  ⟦ _∞>>=_ {xs = []   } p₁ p₂ ⟧⁻¹ = ♯ ⟦ ♭ p₁ ⟧⁻¹ ∞>>= λ x → ♯ ⟦ ♭? (p₂ x) ⟧⁻¹
  ⟦ nonempty p                ⟧⁻¹ = nonempty ⟦ p ⟧⁻¹
  ⟦ cast xs₁≈xs₂ p            ⟧⁻¹ = cast xs₁≈xs₂ ⟦ p ⟧⁻¹

  ⟦♭_⟧⁻¹ : ∀ {Tok R₁ R₂ xs y} {ys : List R₁} →
           ∞? (P.Parser Tok R₂ xs) (y ∷ ys) → Parser Tok R₂ xs
  ⟦♭ ⟨ p ⟩ ⟧⁻¹ = ⟦ p ⟧⁻¹

infix 4 _≈[_]_ _≅_ _≈_

-- General definition of equivalence between parsers.

_≈[_]_ : ∀ {Tok R xs₁ xs₂} →
         Parser Tok R xs₁ → Kind → Parser Tok R xs₂ → Set₁
p₁ ≈[ k ] p₂ = ⟦ p₁ ⟧ P≈[ k ] ⟦ p₂ ⟧

-- Parser equivalence.

_≅_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≅ p₂ = p₁ ≈[ parser ] p₂

-- Language equivalence.

_≈_ : ∀ {Tok R xs₁ xs₂} → Parser Tok R xs₁ → Parser Tok R xs₂ → Set₁
p₁ ≈ p₂ = p₁ ≈[ language ] p₂

------------------------------------------------------------------------
-- Parser is equivalent to P.Parser

-- The two translations are inverses (for parser equivalence).

⟦⟦_⟧⁻¹⟧ : ∀ {Tok R xs} (p : P.Parser Tok R xs) → ⟦ ⟦ p ⟧⁻¹ ⟧ P≅ p
⟦⟦ p ⟧⁻¹⟧ = record
  { to         = Eq.→-to-⟶ (to p)
  ; from       = Eq.→-to-⟶ from
  ; inverse-of = record
    { left-inverse-of  = from∘to p
    ; right-inverse-of = to∘from
    }
  }
  where
  mutual

    to : ∀ {Tok R xs x s} (p : P.Parser Tok R xs) →
         x ∈ ⟦ ⟦ p ⟧⁻¹ ⟧ · s → x ∈ p · s
    to (return x)                  x∈                = x∈
    to fail                        x∈                = x∈
    to token                       x∈                = x∈
    to (p₁ ∣ p₂)                   (∣ˡ     x∈p₁)     = ∣ˡ     (to p₁ x∈p₁)
    to (p₁ ∣ p₂)                   (∣ʳ xs₁ x∈p₂)     = ∣ʳ xs₁ (to p₂ x∈p₂)
    to (f <$> p)                   (<$> x∈p)         = <$>    (to p  x∈p)
    to (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩)           (f∈p₁ ⊛ x∈p₂)     = to _ f∈p₁ ⊛ to _ x∈p₂
    to (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)           (f∈p₁ ⊛ x∈p₂)     = to _ f∈p₁ ⊛ to _ x∈p₂
    to (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫)           (f∈p₁ ⊛ x∈p₂)     = to _ f∈p₁ ⊛ to _ x∈p₂
    to (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫)           (f∈p₁ ⊛ x∈p₂)     = to _ f∈p₁ ⊛ to _ x∈p₂
    to (_>>=_  {xs = []   } p₁ p₂) (x∈p₁ >>=  y∈p₂x) = to _ x∈p₁     >>=               to  _      y∈p₂x
    to (_>>=_  {xs = _ ∷ _} p₁ p₂) (x∈p₁ >>=  y∈p₂x) = to _ x∈p₁ ⟨⟨ _>>=_ {p₂ = p₂} ⟩⟩ to♭ (p₂ _) y∈p₂x
    to (_∞>>=_ {xs = []   } p₁ p₂) (x∈p₁ ∞>>= y∈p₂x) = to _ x∈p₁     ∞>>=              to  _      y∈p₂x
    to (_∞>>=_ {xs = _ ∷ _} p₁ p₂) (x∈p₁ ∞>>= y∈p₂x) = to _ x∈p₁     ∞>>=              to♭ (p₂ _) y∈p₂x
    to (nonempty p)                (nonempty x∈p)    = nonempty (to _ x∈p)
    to (cast xs₁≈xs₂ p)            (cast x∈p)        = cast     (to _ x∈p)

    to♭ : ∀ {Tok R R′ xs x s y} {ys : List R′}
          (p : ∞? (P.Parser Tok R xs) (y ∷ ys)) →
          x ∈ ⟦ ⟦♭ p ⟧⁻¹ ⟧ · s → x ∈ ♭? p · s
    to♭ ⟨ p ⟩ x∈p = to p x∈p

  mutual

    from : ∀ {Tok R xs x s} {p : P.Parser Tok R xs} →
           x ∈ p · s → x ∈ ⟦ ⟦ p ⟧⁻¹ ⟧ · s
    from return                                     = return
    from token                                      = token
    from (∣ˡ x∈p₁)                                  = ∣ˡ     (from x∈p₁)
    from (∣ʳ xs₁ x∈p₂)                              = ∣ʳ xs₁ (from x∈p₂)
    from (<$> x∈p)                                  = <$>    (from x∈p)
    from (_⊛_ {p₁ = ⟨ _ ⟩} {p₂ = ⟨ _ ⟩} f∈p₁ x∈p₂)  = from f∈p₁ ⊛ from x∈p₂
    from (_⊛_ {p₁ = ⟨ _ ⟩} {p₂ = ⟪ _ ⟫} f∈p₁ x∈p₂)  = from f∈p₁ ⊛ from x∈p₂
    from (_⊛_ {p₁ = ⟪ _ ⟫} {p₂ = ⟨ _ ⟩} f∈p₁ x∈p₂)  = from f∈p₁ ⊛ from x∈p₂
    from (_⊛_ {p₁ = ⟪ _ ⟫} {p₂ = ⟪ _ ⟫} f∈p₁ x∈p₂)  = from f∈p₁ ⊛ from x∈p₂
    from (_>>=_  {xs = []}              x∈p₁ y∈p₂x) = from x∈p₁     >>=                                      from         y∈p₂x
    from (_>>=_  {xs = _ ∷ _} {p₂ = p₂} x∈p₁ y∈p₂x) = from x∈p₁ ⟨⟨ _>>=_ {p₂ = λ x → ⟨ ⟦ ⟦♭ p₂ x ⟧⁻¹ ⟧ ⟩} ⟩⟩ from♭ (p₂ _) y∈p₂x
    from (_∞>>=_ {xs = []}              x∈p₁ y∈p₂x) = from x∈p₁     ∞>>=                                     from         y∈p₂x
    from (_∞>>=_ {xs = _ ∷ _} {p₂ = p₂} x∈p₁ y∈p₂x) = from x∈p₁     ∞>>=                                     from♭ (p₂ _) y∈p₂x
    from (nonempty x∈p)                             = nonempty (from x∈p)
    from (cast x∈p)                                 = cast (from x∈p)

    from♭ : ∀ {Tok R R′ xs x s y} {ys : List R′}
            (p : ∞? (P.Parser Tok R xs) (y ∷ ys)) →
            x ∈ ♭? p · s → x ∈ ⟦ ⟦♭ p ⟧⁻¹ ⟧ · s
    from♭ ⟨ _ ⟩ x∈p = from x∈p

  mutual

    from∘to : ∀ {Tok R xs x s} (p : P.Parser Tok R xs) →
              (x∈p : x ∈ ⟦ ⟦ p ⟧⁻¹ ⟧ · s) → from (to p x∈p) ≡ x∈p
    from∘to (return x)                  return            = refl
    from∘to fail                        ()
    from∘to token                       token             = refl
    from∘to (p₁ ∣ p₂)                   (∣ˡ     x∈p₁)     = Eq.cong ∣ˡ       (from∘to p₁ x∈p₁)
    from∘to (p₁ ∣ p₂)                   (∣ʳ xs₁ x∈p₂)     = Eq.cong (∣ʳ xs₁) (from∘to p₂ x∈p₂)
    from∘to (f <$> p)                   (<$> x∈p)         = Eq.cong <$>_     (from∘to p  x∈p)
    from∘to (⟨ p₁ ⟩ ⊛ ⟨ p₂ ⟩)           (f∈p₁ ⊛ x∈p₂)     = Eq.cong₂ _⊛_ (from∘to    p₁  f∈p₁) (from∘to    p₂  x∈p₂)
    from∘to (⟪ p₁ ⟫ ⊛ ⟨ p₂ ⟩)           (f∈p₁ ⊛ x∈p₂)     = Eq.cong₂ _⊛_ (from∘to (♭ p₁) f∈p₁) (from∘to    p₂  x∈p₂)
    from∘to (⟨ p₁ ⟩ ⊛ ⟪ p₂ ⟫)           (f∈p₁ ⊛ x∈p₂)     = Eq.cong₂ _⊛_ (from∘to    p₁  f∈p₁) (from∘to (♭ p₂) x∈p₂)
    from∘to (⟪ p₁ ⟫ ⊛ ⟪ p₂ ⟫)           (f∈p₁ ⊛ x∈p₂)     = Eq.cong₂ _⊛_ (from∘to (♭ p₁) f∈p₁) (from∘to (♭ p₂) x∈p₂)
    from∘to (_>>=_  {xs = []   } p₁ p₂) (x∈p₁ >>=  y∈p₂x) = Eq.cong₂ _>>=_  (from∘to    p₁  x∈p₁) (from∘to (♭? (p₂ _)) y∈p₂x)
    from∘to (_>>=_  {xs = _ ∷ _} p₁ p₂) (x∈p₁ >>=  y∈p₂x) = Eq.cong₂ (_>>=_ {p₂ = λ x → ⟨ ⟦ ⟦♭ p₂ x ⟧⁻¹ ⟧ ⟩})
                                                                            (from∘to    p₁  x∈p₁) (from♭∘to♭   (p₂ _)  y∈p₂x)
    from∘to (_∞>>=_ {xs = []   } p₁ p₂) (x∈p₁ ∞>>= y∈p₂x) = Eq.cong₂ _∞>>=_ (from∘to (♭ p₁) x∈p₁) (from∘to (♭? (p₂ _)) y∈p₂x)
    from∘to (_∞>>=_ {xs = _ ∷ _} p₁ p₂) (x∈p₁ ∞>>= y∈p₂x) = Eq.cong₂ _∞>>=_ (from∘to (♭ p₁) x∈p₁) (from♭∘to♭   (p₂ _)  y∈p₂x)
    from∘to (nonempty p)                (nonempty x∈p)    = Eq.cong nonempty (from∘to p x∈p)
    from∘to (cast xs₁≈xs₂ p)            (cast x∈p)        = Eq.cong cast     (from∘to p x∈p)

    from♭∘to♭ : ∀ {Tok R R′ xs x s y} {ys : List R′}
                (p : ∞? (P.Parser Tok R xs) (y ∷ ys)) →
                (x∈p : x ∈ ⟦ ⟦♭ p ⟧⁻¹ ⟧ · s) → from♭ p (to♭ p x∈p) ≡ x∈p
    from♭∘to♭ ⟨ p ⟩ x∈p = from∘to p x∈p

  mutual

    to∘from : ∀ {Tok R xs x s} {p : P.Parser Tok R xs} →
              (x∈p : x ∈ p · s) → to p (from x∈p) ≡ x∈p
    to∘from return                                     = refl
    to∘from token                                      = refl
    to∘from (∣ˡ     x∈p₁)                              = Eq.cong ∣ˡ       (to∘from x∈p₁)
    to∘from (∣ʳ xs₁ x∈p₂)                              = Eq.cong (∣ʳ xs₁) (to∘from x∈p₂)
    to∘from (<$> x∈p)                                  = Eq.cong <$>_     (to∘from  x∈p)
    to∘from (_⊛_ {p₁ = ⟨ _ ⟩} {p₂ = ⟨ _ ⟩} f∈p₁ x∈p₂)  = Eq.cong₂ _⊛_ (to∘from f∈p₁) (to∘from x∈p₂)
    to∘from (_⊛_ {p₁ = ⟨ _ ⟩} {p₂ = ⟪ _ ⟫} f∈p₁ x∈p₂)  = Eq.cong₂ _⊛_ (to∘from f∈p₁) (to∘from x∈p₂)
    to∘from (_⊛_ {p₁ = ⟪ _ ⟫} {p₂ = ⟨ _ ⟩} f∈p₁ x∈p₂)  = Eq.cong₂ _⊛_ (to∘from f∈p₁) (to∘from x∈p₂)
    to∘from (_⊛_ {p₁ = ⟪ _ ⟫} {p₂ = ⟪ _ ⟫} f∈p₁ x∈p₂)  = Eq.cong₂ _⊛_ (to∘from f∈p₁) (to∘from x∈p₂)
    to∘from (_>>=_  {xs = []}              x∈p₁ y∈p₂x) = Eq.cong₂  _>>=_            (to∘from x∈p₁) (to∘from y∈p₂x)
    to∘from (_>>=_  {xs = _ ∷ _} {p₂ = p₂} x∈p₁ y∈p₂x) = Eq.cong₂ (_>>=_ {p₂ = p₂}) (to∘from x∈p₁) (to♭∘from♭ (p₂ _) y∈p₂x)
    to∘from (_∞>>=_ {xs = []}              x∈p₁ y∈p₂x) = Eq.cong₂  _∞>>=_           (to∘from x∈p₁) (to∘from          y∈p₂x)
    to∘from (_∞>>=_ {xs = _ ∷ _} {p₂ = p₂} x∈p₁ y∈p₂x) = Eq.cong₂  _∞>>=_           (to∘from x∈p₁) (to♭∘from♭ (p₂ _) y∈p₂x)
    to∘from (nonempty x∈p)                             = Eq.cong nonempty (to∘from x∈p)
    to∘from (cast x∈p)                                 = Eq.cong cast     (to∘from x∈p)

    to♭∘from♭ : ∀ {Tok R R′ xs x s y} {ys : List R′}
                (p : ∞? (P.Parser Tok R xs) (y ∷ ys)) →
                (x∈p : x ∈ ♭? p · s) → to♭ p (from♭ p x∈p) ≡ x∈p
    to♭∘from♭ ⟨ _ ⟩ x∈p = to∘from x∈p

⟦⟦_⟧⟧⁻¹ : ∀ {Tok R xs} (p : Parser Tok R xs) → ⟦ ⟦ p ⟧ ⟧⁻¹ ≅ p
⟦⟦ p ⟧⟧⁻¹ = ⟦⟦ ⟦ p ⟧ ⟧⁻¹⟧
