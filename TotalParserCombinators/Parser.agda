------------------------------------------------------------------------
-- The parser type
------------------------------------------------------------------------

module TotalParserCombinators.Parser where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.List as List
open import Data.Maybe using (Maybe; nothing; just)
import Data.List.Any as Any
import Data.List.Properties as ListProp
open import Data.Product using (proj₂)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality

open Any.Membership-≡
open RawMonadPlus {f = zero} List.monadPlus
  using ()
  renaming ( return to return′
           ; ∅      to fail′
           ; _∣_    to _∣′_
           ; _⊛_    to _⊛′_
           ; _>>=_  to _>>=′_
           )

------------------------------------------------------------------------
-- Helper functions

-- Flattening for potential lists.

flatten : {A : Set} → Maybe (List A) → List A
flatten nothing   = []
flatten (just xs) = xs

-- fs ⊛flatten mxs is a variant of fs ⊛′ flatten mxs, with the
-- property that fs ⊛flatten nothing evaluates to [].

_⊛flatten_ : {A B : Set} → List (A → B) → Maybe (List A) → List B
fs ⊛flatten nothing = []
fs ⊛flatten just xs = fs ⊛′ xs

-- Applies the function to the value, returning the empty list if
-- there is no function.

apply : {A B : Set} → Maybe (A → List B) → A → List B
apply nothing  x = []
apply (just f) x = f x

-- bind mxs mf is a variant of flatten mxs >>=′ apply mf, with the
-- property that bind mxs nothing evaluates to [].

bind :  {A B : Set} → Maybe (List A) → Maybe (A → List B) → List B
bind mxs nothing  = []
bind mxs (just f) = flatten mxs >>=′ f

-- Verification of some claims made above.

module Claims where

  ⊛flatten-⊛-flatten : ∀ {A B : Set} (fs : List (A → B)) mxs →
                       fs ⊛flatten mxs ≡ (fs ⊛′ flatten mxs)
  ⊛flatten-⊛-flatten fs nothing   = sym $ ListProp.Monad.right-zero fs
  ⊛flatten-⊛-flatten fs (just xs) = refl

  ⊛flatten-nothing : {A B : Set} (fs : List (A → B)) →
                     fs ⊛flatten nothing ≡ []
  ⊛flatten-nothing fs = refl

  bind-flatten->>=-apply : ∀ {A B : Set} mxs (mf : Maybe (A → List B)) →
                           bind mxs mf ≡ (flatten mxs >>=′ apply mf)
  bind-flatten->>=-apply mxs (just f) = refl
  bind-flatten->>=-apply mxs nothing  =
    sym $ ListProp.Monad.right-zero (flatten mxs)

  bind-nothing : {A B : Set} (mxs : Maybe (List A)) →
                 bind mxs nothing ≡ [] {A = B}
  bind-nothing mxs = refl

------------------------------------------------------------------------
-- Parsers

infixl 50 _⊛_ _<$>_ _⊛flatten_
infixl 10 _>>=_
infixl  5 _∣_

-- The list index is the "initial bag"; it contains the results which
-- can be emitted without consuming any input. For
--   p : Parser Tok R xs
-- we have
--   x ∈ xs  iff  x ∈ p · []
-- (see TotalParserCombinators.InitialBag).

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
               (p₁ : ∞⟨ xs ⟩Parser Tok (R₁ → R₂) (flatten fs)            )
               (p₂ : ∞⟨ fs ⟩Parser Tok  R₁                   (flatten xs)) →
                            Parser Tok       R₂  (flatten fs ⊛flatten xs)
    _>>=_    : ∀ {R₁ R₂ xs} {f : Maybe (R₁ → List R₂)}
               (p₁ :            ∞⟨ f  ⟩Parser Tok R₁ (flatten xs))
               (p₂ : (x : R₁) → ∞⟨ xs ⟩Parser Tok R₂ (apply f x)) →
                                       Parser Tok R₂ (bind xs f)
    nonempty : ∀ {R xs} (p : Parser Tok R xs) → Parser Tok R []
    cast     : ∀ {R xs₁ xs₂} (xs₁≈xs₂ : xs₁ ∼[ bag ] xs₂)
               (p : Parser Tok R xs₁) → Parser Tok R xs₂

  ∞⟨_⟩Parser : {A : Set} → Maybe A → Set → (R : Set) → List R → Set₁
  ∞⟨ nothing ⟩Parser Tok R₁ xs = ∞ (Parser Tok R₁ xs)
  ∞⟨ just _  ⟩Parser Tok R₁ xs =    Parser Tok R₁ xs

-- Note that, with the definition above, a sequenced parser is
-- /allowed/ to be delayed if the "other" parser is not nullable, but
-- it does not have to be.

-- Note also that it would be safe to make the first argument of _>>=_
-- coinductive if apply f x ≡_[] for all x in xs. I suspect that this
-- criterion would be awkward to work with, though. Instead I only
-- allow the argument to be coinductive if f ≡ nothing.

-- Finally note that some of the combinators above are not included in
-- the paper "Total Parser Combinators".

------------------------------------------------------------------------
-- Examples

private

  -- Note that these parsers can be both left and right recursive:

  leftRight : ∀ {R Tok} → Parser Tok R _
  leftRight {R} = ♯ (const <$> leftRight) ⊛ ♯ leftRight {R}

  leftRight′ : ∀ {R Tok} → Parser Tok R _
  leftRight′ {R} = ♯ leftRight′ {R} >>= λ _ → ♯ leftRight′

  -- More examples, included to ensure that all implicit arguments are
  -- inferred automatically.

  p : {Tok R : Set} → Parser Tok R _
  p = token >>= λ _ → ♯ p

  p′ : {Tok : Set} → Parser Tok Tok _
  p′ = ♯ p′ >>= λ _ → token

------------------------------------------------------------------------
-- Helper functions

-- Returns the initial bag.

initial-bag : ∀ {Tok R xs} → Parser Tok R xs → List R
initial-bag {xs = xs} _ = xs

-- Forces if necessary.

♭? : ∀ {Tok R₁ R₂} {m : Maybe R₂} {xs} →
     ∞⟨ m ⟩Parser Tok R₁ xs → Parser Tok R₁ xs
♭? {m = nothing} = ♭
♭? {m = just _}  = id

-- Is the argument parser forced? If the result is just something,
-- then it is.

forced? : ∀ {Tok A R xs} {m : Maybe A} →
          ∞⟨ m ⟩Parser Tok R xs → Maybe A
forced? {m = m} _ = m

forced?′ : {Tok R₁ R₂ A : Set} {m : Maybe A} {f : R₁ → List R₂} →
           ((x : R₁) → ∞⟨ m ⟩Parser Tok R₂ (f x)) → Maybe A
forced?′ {m = m} _ = m

-- Short synonyms for just and nothing. ◌ stands for "delayed" (think
-- "not here") and ○ for "not delayed".

◌ : {R : Set} → Maybe R
◌ = nothing

○ : {R : Set} {x : R} → Maybe R
○ {x = x} = just x
