------------------------------------------------------------------------
-- Total parser combinators (very short version)
-- Nils Anders Danielsson
------------------------------------------------------------------------

module Short where

open import Category.Monad
open import Coinduction
open import Data.Bool
import Data.BoundedVec.Inefficient as BoundedVec
open import Data.Char
import Data.Colist as Colist
open import Data.List as List
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Show
open import Data.String using (Costring)
open import Function
open import IO hiding (return) renaming (_>>=_ to _>>=IO_)
open import Relation.Nullary.Decidable

open RawMonadPlus List.monadPlus using () renaming (_>>=_ to _>>=′_)

infix  7 _⋆ _+
infixl 6 _>>=_ _>>=app_
infixl 5 _∣_

------------------------------------------------------------------------
-- Helper functions

maybeToList : {A B : Set} → Maybe A → (A → List B) → List B
maybeToList nothing  f = []
maybeToList (just x) f = f x

flatten : {A : Set} → Maybe (List A) → List A
flatten mxs = maybeToList mxs id

app : {A B : Set} → Maybe (A → List B) → A → List B
app mf x = maybeToList mf (λ f → f x)

_>>=app_ : {A B : Set} → List A → Maybe (A → List B) → List B
xs >>=app mf = maybeToList mf (λ f → xs >>=′ f)

------------------------------------------------------------------------
-- Parsers

mutual

  data Parser : (R : Set) → List R → Set₁ where
    return : ∀ {R} (x : R) → Parser R [ x ]
    fail   : ∀ {R} → Parser R []
    token  : Parser Char []
    _∣_    : ∀ {R xs₁ xs₂}
             (p₁ : Parser R  xs₁       )
             (p₂ : Parser R         xs₂) →
                   Parser R (xs₁ ++ xs₂)
    _>>=_  : ∀ {R₁ R₂ xs} {f : Maybe (R₁ → List R₂)}
             (p₁ :            ∞⟨ f  ⟩Parser R₁ (flatten xs)           )
             (p₂ : (x : R₁) → ∞⟨ xs ⟩Parser R₂               (app f x)) →
                                     Parser R₂ (flatten xs >>=app f)

  ∞⟨_⟩Parser : {R₂ : Set} → Maybe R₂ → (R₁ : Set) → List R₁ → Set₁
  ∞⟨ nothing ⟩Parser R₁ xs = ∞ (Parser R₁ xs)
  ∞⟨ just _  ⟩Parser R₁ xs =    Parser R₁ xs

------------------------------------------------------------------------
-- Derived combinators

sat : ∀ {R} → (Char → Maybe R) → Parser R []
sat {R} p = token >>= (ok ∘ p)
  where
  ok-index : Maybe R → List R
  ok-index nothing  = []
  ok-index (just x) = [ x ]

  ok : (x : Maybe R) → Parser R (ok-index x)
  ok nothing  = fail
  ok (just x) = return x

tok : Char → Parser Char []
tok t = sat (λ t′ → if t == t′ then just t′ else nothing)

return⋆ : ∀ {R} (xs : List R) → Parser R xs
return⋆ []       = fail
return⋆ (x ∷ xs) = return x ∣ return⋆ xs

mutual

  _⋆ : ∀ {R} → Parser R [] → Parser (List R) _
  p ⋆ = return [] ∣ p +

  _+ : ∀ {R} → Parser R [] → Parser (List R) _
  p + = p               >>= λ x  → ♯ (
        p ⋆             >>= λ xs →
        return (x ∷ xs)              )

digit = sat (λ t → if in-range t then just (to-number t) else nothing)
  where
  in-range : Char → Bool
  in-range t = ⌊ toNat '0' ≤? toNat  t  ⌋ ∧
               ⌊ toNat  t  ≤? toNat '9' ⌋

  to-number : Char → ℕ
  to-number t = toNat t ∸ toNat '0'

number = digit + >>= return ∘ foldl (λ n d → 10 * n + d) 0

------------------------------------------------------------------------
-- Parser interpreter

delayed? : ∀ {R R′ xs} {m : Maybe R′} → ∞⟨ m ⟩Parser R xs → Maybe R′
delayed? {m = m} _ = m

delayed?′ : ∀ {R₁ R₂ R′ : Set} {m : Maybe R′} {f : R₁ → List R₂} →
            ((x : R₁) → ∞⟨ m ⟩Parser R₂ (f x)) → Maybe R′
delayed?′ {m = m} _ = m

∂-initial : ∀ {R xs} → Parser R xs → Char → List R
∂-initial (return x)  t = []
∂-initial fail        t = []
∂-initial token       t = [ t ]
∂-initial (p₁ ∣ p₂)   t = ∂-initial p₁ t ++ ∂-initial p₂ t
∂-initial (p₁ >>= p₂) t with delayed? p₁ | delayed?′ p₂
... | just f  | nothing =  ∂-initial p₁ t >>=′ f
... | just f  | just xs = (∂-initial p₁ t >>=′ f) ++
                          (xs >>=′ λ x → ∂-initial (p₂ x) t)
... | nothing | nothing = []
... | nothing | just xs =  xs >>=′ λ x → ∂-initial (p₂ x) t

∂ : ∀ {R xs} (p : Parser R xs) (t : Char) → Parser R (∂-initial p t)
∂ (return x)  t = fail
∂ fail        t = fail
∂ token       t = return t
∂ (p₁ ∣ p₂)   t = ∂ p₁ t ∣ ∂ p₂ t
∂ (p₁ >>= p₂) t with delayed? p₁ | delayed?′ p₂
... | just f  | nothing = ∂ p₁ t >>= (λ x → ♭ (p₂ x))
... | just f  | just xs = ∂ p₁ t >>= (λ x →    p₂ x)
                        ∣ return⋆ xs >>= λ x → ∂ (p₂ x) t
... | nothing | nothing = ♯ ∂ (♭ p₁) t >>= (λ x → ♭ (p₂ x))
... | nothing | just xs = ♯ ∂ (♭ p₁) t >>= (λ x →    p₂ x)
                        ∣ return⋆ xs >>= λ x → ∂ (p₂ x) t

parseComplete : ∀ {R xs} → Parser R xs → List Char → List R
parseComplete {xs = xs} p []      = xs
parseComplete           p (t ∷ s) = parseComplete (∂ p t) s

------------------------------------------------------------------------
-- Example

data Expr : Set where
  num   : (n : ℕ)        → Expr
  plus  : (e₁ e₂ : Expr) → Expr
  times : (e₁ e₂ : Expr) → Expr

⟦_⟧ : Expr → ℕ
⟦ num n       ⟧ = n
⟦ plus  e₁ e₂ ⟧ = ⟦ e₁ ⟧ + ⟦ e₂ ⟧
⟦ times e₁ e₂ ⟧ = ⟦ e₁ ⟧ * ⟦ e₂ ⟧

mutual

  term   = factor
         ∣ ♯ term               >>= λ e₁ →
           tok '+'              >>= λ _  →
           factor               >>= λ e₂ →
           return (plus e₁ e₂)

  factor = atom
         ∣ ♯ factor             >>= λ e₁ →
           tok '*'              >>= λ _  →
           atom                 >>= λ e₂ →
           return (times e₁ e₂)

  atom   = (number >>= return ∘ num)
         ∣ tok '('              >>= λ _  →
           ♯ term               >>= λ e  →
           tok ')'              >>= λ _  →
           return e

------------------------------------------------------------------------
-- IO

toList : Costring → List Char
toList = BoundedVec.toList ∘ Colist.take 100000

main = run $
  ♯ getContents >>=IO λ s → ♯
  let s′ = takeWhile (not ∘ _==_ '\n') $ toList s
      es = parseComplete term s′ in
  mapM′ (putStrLn ∘ show ∘ ⟦_⟧) (Colist.fromList es)
