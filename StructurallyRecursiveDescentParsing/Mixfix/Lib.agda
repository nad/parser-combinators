------------------------------------------------------------------------
-- Small library used by StructurallyRecursiveDescentParsing.Mixfix
------------------------------------------------------------------------

open import Relation.Binary

module StructurallyRecursiveDescentParsing.Mixfix.Lib
         (Token : DecSetoid)
         where

open DecSetoid Token using (_≈_; _≟_; refl) renaming (carrier to Tok)

open import Coinduction
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.NonEmpty using (List⁺; [_]; _∷_; _∷ʳ_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product
open import Relation.Nullary
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)

open import StructurallyRecursiveDescentParsing.Coinduction
import StructurallyRecursiveDescentParsing.Parser as Parser
import StructurallyRecursiveDescentParsing.Simplified as Simplified
open Simplified hiding (⟦_⟧)
open import StructurallyRecursiveDescentParsing.Parser.Semantics
  hiding (cast∈; sound; complete; _≈_)

------------------------------------------------------------------------
-- Programs

-- Agda's termination checker only accepts corecursive definitions if
-- they are /syntactically/ guarded by constructors. The following
-- small language of "parser programs" reifies a selection of parser
-- combinators as /constructors/. These constructors are then used in
-- StructurallyRecursiveDescentParsing.Mixfix in order to ensure that
-- Agda accepts the grammar defined there.

infix  55 _+
infixl 50 _⊛_ _<$>_
infixl 10 _!>>=_ _?>>=_
infixl  5 _∣_
infixr  5 _∥_

data ParserProg : Bool → Set → Set1 where
  return    : ∀ {R} (x : R) → ParserProg true R
  fail      : ∀ {R} → ParserProg false R
  token     : ParserProg false Tok
  _∣_       : ∀ {e₁ e₂ R}
              (p₁ : ParserProg  e₁       R)
              (p₂ : ParserProg       e₂  R) →
                    ParserProg (e₁ ∨ e₂) R
  _?>>=_    : ∀ {e₂ R₁ R₂}
              (p₁ :      ParserProg true R₁)
              (p₂ : R₁ → ParserProg e₂   R₂) →
                         ParserProg e₂   R₂
  _!>>=_    : ∀ {R₁ R₂} {e₂ : R₁ → Bool}
              (p₁ :                ParserProg false  R₁)
              (p₂ : (x : R₁) → ∞₁ (ParserProg (e₂ x) R₂)) →
                                   ParserProg false  R₂
  _⊛_       : ∀ {e₁ e₂ R₁ R₂}
              (p₁ : ParserProg  e₁      (R₁ → R₂))
              (p₂ : ParserProg       e₂  R₁) →
                    ParserProg (e₁ ∧ e₂) R₂
  _<$>_     : ∀ {e R₁ R₂} (f : R₁ → R₂)
              (p : ParserProg e R₁) →
                   ParserProg e R₂
  _+        : ∀ {R} (p : ParserProg false R) →
                         ParserProg false (List⁺ R)
  _between_ : ∀ {e R n}
              (p : ∞₁ (ParserProg e R)) (toks : Vec Tok (suc n)) →
              ParserProg false (Vec R n)
  _∥_       : ∀ {e₁ e₂ I i} {R : I → Set}
              (p₁ : ParserProg  e₁       (R i))
              (p₂ : ParserProg       e₂  (∃ R)) →
                    ParserProg (e₁ ∨ e₂) (∃ R)

-- Parses a given token (or, really, a given equivalence class of
-- tokens).

theToken : Tok → Parser Tok false Tok
theToken tok = token !>>= λ tok′ → ♯₁ ok tok′
  module TheToken where
  okIndex : Tok → Bool
  okIndex tok′ with tok ≟ tok′
  ... | yes _ = true
  ... | no  _ = false

  ok : (tok′ : Tok) → Parser Tok (okIndex tok′) Tok
  ok tok′ with tok ≟ tok′
  ... | yes _ = return tok′
  ... | no  _ = fail

-- Interprets the parser programs as parsers.

private
  infix 10 ♯′_

  ♯′_ : ∀ {A} → A → ∞₁ A
  ♯′ x = ♯₁ x

⟦_⟧ : ∀ {e R} → ParserProg e R → Parser Tok e R
⟦ return x                 ⟧ = return x
⟦ fail                     ⟧ = fail
⟦ token                    ⟧ = token
⟦ p₁ ∣ p₂                  ⟧ = ⟦ p₁ ⟧ ∣ ⟦ p₂ ⟧
⟦ p₁ ?>>= p₂               ⟧ = ⟦ p₁ ⟧ ?>>= λ x →    ⟦     p₂ x  ⟧
⟦ p₁ !>>= p₂               ⟧ = ⟦ p₁ ⟧ !>>= λ x → ♯₁ ⟦ ♭₁ (p₂ x) ⟧
⟦ _⊛_ {true} {true}  p₁ p₂ ⟧ = ⟦ p₁ ⟧ ?>>= λ f →
                               ⟦ p₂ ⟧ ?>>= λ x →    return (f x)
⟦ _⊛_ {true} {false} p₁ p₂ ⟧ = ⟦ p₁ ⟧ ?>>= λ f →
                               ⟦ p₂ ⟧ !>>= λ x → ♯′ return (f x)
⟦ _⊛_ {false}        p₁ p₂ ⟧ = ⟦ p₁ ⟧ !>>= λ f → ♯₁ ⟦ f <$> p₂ ⟧
⟦ _<$>_  {true}  f p       ⟧ = ⟦ p  ⟧ ?>>= λ x →    return (f x)
⟦ _<$>_  {false} f p       ⟧ = ⟦ p  ⟧ !>>= λ x → ♯′ return (f x)
⟦ p +                      ⟧ = ⟦ p  ⟧ !>>= λ x → ♯₁
                               ⟦ _∷_ x <$> p + ∣ return [ x ] ⟧
⟦ p between (t ∷ [])       ⟧ = theToken t !>>= λ _ → ♯′ return []
⟦ p between (t ∷ t′ ∷ ts)  ⟧ = theToken t !>>= λ _ → ♯₁
                                ⟦ _∷_ <$> ♭₁ p ⊛ (p between (t′ ∷ ts)) ⟧
⟦ _∥_ {true}  p₁ p₂        ⟧ = (⟦ p₁ ⟧ ?>>= λ x →    return (, x)) ∣ ⟦ p₂ ⟧
⟦ _∥_ {false} p₁ p₂        ⟧ = (⟦ p₁ ⟧ !>>= λ x → ♯′ return (, x)) ∣ ⟦ p₂ ⟧

⟦_⟧′ : ∀ {e R} → ParserProg e R → Parser.Parser Tok e R
⟦ p ⟧′ = Simplified.⟦_⟧ ⟦ p ⟧

------------------------------------------------------------------------
-- Semantics of the programs

-- This definition may seem unnecessary: why not simply define
--
--   x ⊕ s′ ∈⟦ p ⟧· s  =  x ⊕ s′ ∈ ⟦ p ⟧′ · s?
--
-- The reason is that it is hard for Agda to infer the value of p from
-- ⟦ p ⟧′ (note that ⟦_⟧′ is a function which evaluates). By using the
-- definition below this problem is avoided.

infix 4 _⊕_∈⟦_⟧·_

data _⊕_∈⟦_⟧·_ : ∀ {R e} →
                 R → List Tok → ParserProg e R → List Tok → Set1 where
  return     : ∀ {R} {x : R} {s} → x ⊕ s ∈⟦ return x ⟧· s
  token      : ∀ {x s} → x ⊕ s ∈⟦ token ⟧· x ∷ s
  ∣ˡ         : ∀ {R x e₁ e₂ s s₁}
                 {p₁ : ParserProg e₁ R} {p₂ : ParserProg e₂ R}
               (x∈p₁ : x ⊕ s₁ ∈⟦ p₁ ⟧· s) → x ⊕ s₁ ∈⟦ p₁ ∣ p₂ ⟧· s
  ∣ʳ         : ∀ {R x e₂ s s₁} e₁
                 {p₁ : ParserProg e₁ R} {p₂ : ParserProg e₂ R}
               (x∈p₂ : x ⊕ s₁ ∈⟦ p₂ ⟧· s) → x ⊕ s₁ ∈⟦ p₁ ∣ p₂ ⟧· s
  _?>>=_     : ∀ {R₁ R₂ x y e₂ s s₁ s₂}
                 {p₁ : ParserProg true R₁} {p₂ : R₁ → ParserProg e₂ R₂}
               (x∈p₁ : x ⊕ s₁ ∈⟦ p₁ ⟧· s) (y∈p₂x : y ⊕ s₂ ∈⟦ p₂ x ⟧· s₁) →
               y ⊕ s₂ ∈⟦ p₁ ?>>= p₂ ⟧· s
  _!>>=_     : ∀ {R₁ R₂ x y} {e₂ : R₁ → Bool} {s s₁ s₂}
                 {p₁ : ParserProg false R₁}
                 {p₂ : (x : R₁) → ∞₁ (ParserProg (e₂ x) R₂)}
               (x∈p₁ : x ⊕ s₁ ∈⟦ p₁ ⟧· s) (y∈p₂x : y ⊕ s₂ ∈⟦ ♭₁ (p₂ x) ⟧· s₁) →
               y ⊕ s₂ ∈⟦ p₁ !>>= p₂ ⟧· s
  _⊛_        : ∀ {e₁ e₂ s s₁ s₂ R₁ R₂ f x}
                 {p₁ : ParserProg e₁ (R₁ → R₂)} {p₂ : ParserProg e₂ R₁}
               (f∈p₁ : f ⊕ s₁ ∈⟦ p₁ ⟧· s) (x∈p₂ : x ⊕ s₂ ∈⟦ p₂ ⟧· s₁) →
               f x ⊕ s₂ ∈⟦ p₁ ⊛ p₂ ⟧· s
  _<$>_      : ∀ {e s s′ R₁ R₂ x} (f : R₁ → R₂) {p : ParserProg e R₁}
               (x∈p : x ⊕ s′ ∈⟦ p ⟧· s) → f x ⊕ s′ ∈⟦ f <$> p ⟧· s
  +-[]       : ∀ {R x s s₁} {p : ParserProg false R}
               (x∈p : x ⊕ s₁ ∈⟦ p ⟧· s) → [ x ] ⊕ s₁ ∈⟦ p + ⟧· s
  +-∷        : ∀ {R x s s₁ s₂ xs} {p : ParserProg false R}
               (x∈p : x ⊕ s₁ ∈⟦ p ⟧· s) (xs∈p : xs ⊕ s₂ ∈⟦ p + ⟧· s₁) →
               x ∷ xs ⊕ s₂ ∈⟦ p + ⟧· s
  between-[] : ∀ {e R t t′ s} {p : ∞₁ (ParserProg e R)}
               (t≈t′ : t ≈ t′) →
               [] ⊕ s ∈⟦ p between (t ∷ []) ⟧· t′ ∷ s
  between-∷  : ∀ {e R n t t′ x xs s s₁ s₂}
                 {p : ∞₁ (ParserProg e R)} {ts : Vec Tok (suc n)}
               (t≈t′ : t ≈ t′)
               (x∈p : x ⊕ s₁ ∈⟦ ♭₁ p ⟧· s)
               (xs∈⋯ : xs ⊕ s₂ ∈⟦ p between ts ⟧· s₁) →
               x ∷ xs ⊕ s₂ ∈⟦ p between (t ∷ ts) ⟧· t′ ∷ s
  ∥ˡ         : ∀ {e₁ e₂ I i} {R : I → Set} {x s s′}
                 {p₁ : ParserProg e₁ (R i)} {p₂ : ParserProg e₂ (∃ R)}
               (x∈p₁ : x ⊕ s′ ∈⟦ p₁ ⟧· s) → (, x) ⊕ s′ ∈⟦ p₁ ∥ p₂ ⟧· s
  ∥ʳ         : ∀ e₁ {e₂ I i} {R : I → Set} {x s s′}
                 {p₁ : ParserProg e₁ (R i)} {p₂ : ParserProg e₂ (∃ R)}
               (x∈p₂ : x ⊕ s′ ∈⟦ p₂ ⟧· s) → x ⊕ s′ ∈⟦ p₁ ∥ p₂ ⟧· s

-- The semantics is correct.

private

  <$>-complete : ∀ {e s s′ R₁ R₂ x} (p : ParserProg e R₁) {f : R₁ → R₂} →
                 x ⊕ s′ ∈ ⟦ p ⟧′ · s → f x ⊕ s′ ∈ ⟦ f <$> p ⟧′ · s
  <$>-complete {true}  _ x∈p·s = cast (x∈p·s >>= return)
  <$>-complete {false} _ x∈p·s =       x∈p·s >>= return

  ⊛-complete : ∀ {e₁ e₂ s s₁ s₂ R₁ R₂ f x}
                 {p₁ : ParserProg e₁ (R₁ → R₂)} {p₂ : ParserProg e₂ R₁} →
               f ⊕ s₁ ∈ ⟦ p₁ ⟧′ · s → x ⊕ s₂ ∈ ⟦ p₂ ⟧′ · s₁ →
               f x ⊕ s₂ ∈ ⟦ p₁ ⊛ p₂ ⟧′ · s
  ⊛-complete {true}  {true}  {p₂ = p₂} f∈p₁ x∈p₂ = cast (f∈p₁ >>= <$>-complete p₂ x∈p₂)
  ⊛-complete {true}  {false} {p₂ = p₂} f∈p₁ x∈p₂ = cast (f∈p₁ >>= <$>-complete p₂ x∈p₂)
  ⊛-complete {false} {_}     {p₂ = p₂} f∈p₁ x∈p₂ =       f∈p₁ >>= <$>-complete p₂ x∈p₂

  theToken-sound : ∀ {t t′ s₁ s} →
                   t′ ⊕ s₁ ∈ Simplified.⟦_⟧ (theToken t) · s →
                   t ≈ t′ × s ≡ t′ ∷ s₁
  theToken-sound {t} (_>>=_ {x = t″} token t′∈) with t ≟ t″
  theToken-sound (token >>= return) | yes t≈t″ = (t≈t″ , PropEq.refl)
  theToken-sound (token >>= ())     | no  t≉t″

  theToken-complete : ∀ {t t′ s} → t ≈ t′ →
                      t′ ⊕ s ∈ Simplified.⟦_⟧ (theToken t) · t′ ∷ s
  theToken-complete {t} {t′} {s} t≈t′ = token >>= ok-lemma
    where
    ok-lemma : t′ ⊕ s ∈ Simplified.⟦_⟧ (TheToken.ok t t′) · s
    ok-lemma with t ≟ t′
    ... | yes t≈t′ = return
    ... | no  t≉t′ with t≉t′ t≈t′
    ...   | ()

sound : ∀ {R e x s s′} {p : ParserProg e R} →
        x ⊕ s′ ∈⟦ p ⟧· s → x ⊕ s′ ∈ ⟦ p ⟧′ · s
sound return                 = return
sound token                  = token
sound (∣ˡ x∈p₁)              = ∣ˡ (sound x∈p₁)
sound (∣ʳ e₁ x∈p₂)           = ∣ʳ e₁ (sound x∈p₂)
sound (x∈p₁ ?>>= y∈p₂x)      = cast (sound x∈p₁ >>= sound y∈p₂x)
sound (x∈p₁ !>>= y∈p₂x)      =       sound x∈p₁ >>= sound y∈p₂x
sound (f∈p₁ ⊛ x∈p₂)          = ⊛-complete (sound f∈p₁) (sound x∈p₂)
sound (f <$> x∈p)            = <$>-complete _ (sound x∈p)
sound (+-[] x∈p)             = sound x∈p >>= ∣ʳ false return
sound (+-∷ {p = p} x∈p xs∈p) = sound x∈p >>=
                               ∣ˡ (<$>-complete (p +) (sound xs∈p))
sound (between-[] t≈t′)      = theToken-complete t≈t′ >>= return
sound (between-∷ {p = p} {_ ∷ _} t≈t′ x∈p xs∈⋯) =
  theToken-complete t≈t′ >>=
  ⊛-complete (<$>-complete _ (sound x∈p)) (sound xs∈⋯)
sound (∥ˡ {true}  {p₁ = p₁} x∈p₁) = ∣ˡ (<$>-complete p₁ (sound x∈p₁))
sound (∥ˡ {false} {p₁ = p₁} x∈p₁) = ∣ˡ (<$>-complete p₁ (sound x∈p₁))
sound (∥ʳ true  x∈p₂)             = ∣ʳ true  (sound x∈p₂)
sound (∥ʳ false x∈p₂)             = ∣ʳ false (sound x∈p₂)

complete : ∀ {R e x s s′} (p : ParserProg e R) →
           x ⊕ s′ ∈ ⟦ p ⟧′ · s → x ⊕ s′ ∈⟦ p ⟧· s
complete (return x)   return                  = return
complete fail         ()
complete token        token                   = token
complete (p₁ ∣ p₂)    (∣ˡ    x∈p₁)            = ∣ˡ    (complete p₁ x∈p₁)
complete (p₁ ∣ p₂)    (∣ʳ e₁ x∈p₂)            = ∣ʳ e₁ (complete p₂ x∈p₂)
complete (p₁ ?>>= p₂) (cast (x∈p₁ >>= y∈p₂x)) = complete p₁ x∈p₁ ?>>= complete     (p₂ _)  y∈p₂x
complete (p₁ !>>= p₂)       (x∈p₁ >>= y∈p₂x)  = complete p₁ x∈p₁ !>>= complete (♭₁ (p₂ _)) y∈p₂x

complete (_⊛_ {true}  {true}  p₁ p₂) (cast (f∈p₁ >>= cast (y∈p₂ >>= return))) = complete p₁ f∈p₁ ⊛ complete p₂ y∈p₂
complete (_⊛_ {true}  {false} p₁ p₂) (cast (f∈p₁ >>=      (y∈p₂ >>= return))) = complete p₁ f∈p₁ ⊛ complete p₂ y∈p₂
complete (_⊛_ {false} {true}  p₁ p₂) (      f∈p₁ >>= cast (y∈p₂ >>= return) ) = complete p₁ f∈p₁ ⊛ complete p₂ y∈p₂
complete (_⊛_ {false} {false} p₁ p₂) (      f∈p₁ >>=      (y∈p₂ >>= return) ) = complete p₁ f∈p₁ ⊛ complete p₂ y∈p₂

complete (_<$>_ {true}  f p) (cast (x∈p >>= return)) = f <$> complete p x∈p
complete (_<$>_ {false} f p)       (x∈p >>= return)  = f <$> complete p x∈p

complete (p +) (x∈p >>= ∣ˡ (xs∈p+ >>= return)) = +-∷  (complete p x∈p) (complete (p +) xs∈p+)
complete (p +) (x∈p >>= ∣ʳ .false return)      = +-[] (complete p x∈p)

complete (p between (t ∷ [])) (t∈ >>= return) with theToken-sound t∈
... | (t≈t′ , PropEq.refl) = between-[] t≈t′
complete (_between_ {true}  p (t ∷ t′ ∷ ts))
         (t∈ >>= cast (cast (x∈p >>= return) >>= (xs∈ >>= return))) with theToken-sound t∈
... | (t≈t″ , PropEq.refl) =
  between-∷ t≈t″ (complete (♭₁ p) x∈p) (complete (p between (t′ ∷ ts)) xs∈)
complete (_between_ {false} p (t ∷ t′ ∷ ts))
         (t∈ >>=      (      x∈p >>= return  >>= (xs∈ >>= return))) with theToken-sound t∈
... | (t≈t″ , PropEq.refl) =
  between-∷ t≈t″ (complete (♭₁ p) x∈p) (complete (p between (t′ ∷ ts)) xs∈)

complete (_∥_ {true}  p₁ p₂) (∣ˡ (cast (x∈p₁ >>= return))) = ∥ˡ (complete p₁ x∈p₁)
complete (_∥_ {true}  p₁ p₂) (∣ʳ .true x∈p₂) = ∥ʳ true (complete p₂ x∈p₂)
complete (_∥_ {false} p₁ p₂) (∣ˡ (x∈p₁ >>= return)) = ∥ˡ (complete p₁ x∈p₁)
complete (_∥_ {false} p₁ p₂) (∣ʳ .false x∈p₂) = ∥ʳ false (complete p₂ x∈p₂)

-- Some lemmas.

+-∷ʳ : ∀ {R x s s₁ s₂ xs} {p : ParserProg false R} →
       xs ⊕ s₁ ∈⟦ p + ⟧· s → x ⊕ s₂ ∈⟦ p ⟧· s₁ →
       xs ∷ʳ x ⊕ s₂ ∈⟦ p + ⟧· s
+-∷ʳ (+-[] x∈p)     y∈p = +-∷ x∈p (+-[] y∈p)
+-∷ʳ (+-∷ x∈p xs∈p) y∈p = +-∷ x∈p (+-∷ʳ xs∈p y∈p)

cast∈ : ∀ {e R x₁ x₂ s s′} {p : ParserProg e R} →
        x₁ ≡ x₂ → x₁ ⊕ s′ ∈⟦ p ⟧· s → x₂ ⊕ s′ ∈⟦ p ⟧· s
cast∈ PropEq.refl x∈p = x∈p
