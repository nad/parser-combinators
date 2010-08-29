------------------------------------------------------------------------
-- This module proves that the parser combinators correspond exactly
-- to functions of type List Tok → List R (if bag equality is used for
-- the lists of results)
------------------------------------------------------------------------

module TotalParserCombinators.ExpressiveStrength where

open import Coinduction
open import Data.Bool
open import Function
open import Function.Inverse as Inv using (_⇿_)
open import Data.List as List
open import Data.List.Any
open Membership-≡
import Data.List.Properties as ListProp
open import Data.List.Reverse
open import Data.Product
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; _≇_; refl)
open import Relation.Nullary

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics as S
  hiding (_≅_; _≈[_]_; token)
open import TotalParserCombinators.Lib
private
  open module Tok = Token Bool _≟_ using (tok)
open import TotalParserCombinators.BreadthFirst as Backend
  using (parse)

------------------------------------------------------------------------
-- Expressive strength

-- One direction of the correspondence has already been established:
-- For every parser there is an equivalent function.

parser⇒fun : ∀ {R xs} (p : Parser Bool R xs) {x s} →
             x ∈ p · s ⇿ x ∈ parse p s
parser⇒fun p = Backend.correct

-- For every function there is a corresponding parser.

module Monadic where

  -- The parser.

  grammar : ∀ {Tok R} (f : List Tok → List R) → Parser Tok R (f [])
  grammar f = token >>= (λ t → ♯ grammar (f ∘ _∷_ t))
            ∣ return⋆ (f [])

  -- Correctness proof.

  grammar-correct : ∀ {Tok R} (f : List Tok → List R) {x s} →
                    x ∈ grammar f · s ⇿ x ∈ f s
  grammar-correct f {s = s} = record
    { to         = P.→-to-⟶ (sound f)
    ; from       = P.→-to-⟶ (complete f s)
    ; inverse-of = record
      { left-inverse-of  = complete∘sound f
      ; right-inverse-of = sound∘complete f s
      }
    }
    where
    sound : ∀ {Tok R x s} (f : List Tok → List R) →
            x ∈ grammar f · s → x ∈ f s
    sound f (∣-right ._ x∈) with Return⋆.sound (f []) x∈
    ... | (refl , x∈′) = x∈′
    sound f (∣-left (S.token {t} >>= x∈)) = sound (f ∘ _∷_ t) x∈

    complete : ∀ {Tok R x} (f : List Tok → List R) s →
               x ∈ f s → x ∈ grammar f · s
    complete f []      x∈ = ∣-right [] (Return⋆.complete x∈)
    complete f (t ∷ s) x∈ =
      ∣-left ([ ○ - ◌ ] S.token >>= complete (f ∘ _∷_ t) s x∈)

    complete∘sound : ∀ {Tok R x s} (f : List Tok → List R)
                     (x∈pf : x ∈ grammar f · s) →
                     complete f s (sound f x∈pf) ≡ x∈pf
    complete∘sound f (∣-left (S.token {t} >>= x∈))
      rewrite complete∘sound (f ∘ _∷_ t) x∈ = refl
    complete∘sound f (∣-right .[] x∈)
      with Return⋆.sound (f []) x∈ | Return⋆.complete∘sound (f []) x∈
    complete∘sound f (∣-right .[] .(Return⋆.complete x∈f[]))
      | (refl , x∈f[]) | refl = refl

    sound∘complete : ∀ {Tok R x} (f : List Tok → List R) s
                     (x∈fs : x ∈ f s) →
                     sound f (complete f s x∈fs) ≡ x∈fs
    sound∘complete       f (t ∷ s) x∈ = sound∘complete (f ∘ _∷_ t) s x∈
    sound∘complete {Tok} f []      x∈
      with Return⋆.sound {Tok = Tok} (f []) (Return⋆.complete x∈)
         | Return⋆.sound∘complete {Tok = Tok} x∈
    ... | (refl , .x∈) | refl = refl

  -- A corollary.

  maximally-expressive :
    ∀ {Tok R} (f : List Tok → List R) {s} →
    parse (grammar f) s ≈[ bag ] f s
  maximally-expressive f {s} {x} =
    (x ∈ parse (grammar f) s)  ⇿⟨ sym Backend.correct ⟩
    x ∈ grammar f · s          ⇿⟨ grammar-correct f ⟩
    x ∈ f s                    ∎
    where open Inv.EquationalReasoning

-- If the token type is finite (in this case Bool), then the result
-- above can be established without the use of bind (_>>=_). (The
-- definition of tok uses bind, but if bind were removed it would be
-- reasonable to either add tok as a primitive combinator, or make it
-- possible to define tok using other combinators.)

module Applicative where

  -- A helper function.

  specialise : {A B : Set} → (List A → B) → A → (List A → B)
  specialise f x = λ xs → f (xs ∷ʳ x)

  -- The parser.

  grammar : ∀ {R} (f : List Bool → List R) → Parser Bool R (f [])
  grammar f =
      ♯ (const <$> grammar (specialise f true )) ⊛ tok true
    ∣ ♯ (const <$> grammar (specialise f false)) ⊛ tok false
    ∣ return⋆ (f [])

  -- Correctness proof.

  grammar-correct : ∀ {R} (f : List Bool → List R) {x s} →
                    x ∈ grammar f · s ⇿ x ∈ f s
  grammar-correct {R} f {s = s} = record
    { to         = P.→-to-⟶ (sound f)
    ; from       = P.→-to-⟶ (complete f (reverseView s))
    ; inverse-of = record
      { right-inverse-of = sound∘complete f (reverseView s)
      ; left-inverse-of  = λ x∈ →
          complete∘sound f (reverseView s) _ x∈ refl refl
      }
    }
    where
    sound : ∀ {x : R} {s} f → x ∈ grammar f · s → x ∈ f s
    sound f (∣-right ._ x∈) with Return⋆.sound (f []) x∈
    ... | (refl , x∈′) = x∈′
    sound f (∣-left (∣-left (<$> x∈ ⊛ t∈))) with Tok.sound true t∈
    ... | (refl , refl) = sound (specialise f true ) x∈
    sound f (∣-left (∣-right ._ (<$> x∈ ⊛ t∈))) with Tok.sound false t∈
    ... | (refl , refl) = sound (specialise f false) x∈

    complete : ∀ {x : R} {s} f → Reverse s →
               x ∈ f s → x ∈ grammar f · s
    complete f []                 x∈ = ∣-right [] (Return⋆.complete x∈)
    complete f (bs ∶ rs ∶ʳ true ) x∈ =
      ∣-left {xs₁ = []} (∣-left (
        [ ◌ - ○ ] <$> complete (specialise f true ) rs x∈ ⊛ Tok.complete))
    complete f (bs ∶ rs ∶ʳ false) x∈ =
      ∣-left (∣-right [] (
        [ ◌ - ○ ] <$> complete (specialise f false) rs x∈ ⊛ Tok.complete))

    sound∘complete : ∀ {x : R} {s} f (rs : Reverse s) (x∈fs : x ∈ f s) →
                     sound f (complete f rs x∈fs) ≡ x∈fs
    sound∘complete f [] x∈
      rewrite Return⋆.sound∘complete {Tok = Bool} x∈ = refl
    sound∘complete f (bs ∶ rs ∶ʳ true) x∈ =
      sound∘complete (specialise f true) rs x∈
    sound∘complete f (bs ∶ rs ∶ʳ false) x∈ =
      sound∘complete (specialise f false) rs x∈

    complete∘sound : ∀ {x : R} {s s′ : List Bool}
                     f (rs : Reverse s) (rs′ : Reverse s′)
                     (x∈pf : x ∈ grammar f · s) → s ≡ s′ → rs ≅ rs′ →
                     complete f rs (sound f x∈pf) ≡ x∈pf

    complete∘sound f rs rs′ (∣-right ._ x∈) s≡ rs≅
      with Return⋆.sound (f []) x∈
         | Return⋆.complete∘sound (f []) x∈
    complete∘sound f ._ []                 (∣-right ._ .(Return⋆.complete x∈′)) refl refl | (refl , x∈′) | refl = refl
    complete∘sound f _  ([]      ∶ _ ∶ʳ _) (∣-right ._ .(Return⋆.complete x∈′)) ()   _    | (refl , x∈′) | refl
    complete∘sound f _  ((_ ∷ _) ∶ _ ∶ʳ _) (∣-right ._ .(Return⋆.complete x∈′)) ()   _    | (refl , x∈′) | refl

    complete∘sound f rs rs′ (∣-left (∣-left (<$> x∈ ⊛ t∈))) s≡ rs≅ with Tok.sound true t∈
    complete∘sound f rs (bs′ ∶ rs′ ∶ʳ true)  (∣-left (∣-left (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) s≡ rs≅ | (refl , refl)
      with proj₁ $ ListProp.∷ʳ-injective bs bs′ s≡
    complete∘sound f rs (.bs ∶ rs′ ∶ʳ true)  (∣-left (∣-left (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) s≡ rs≅ | (refl , refl) | refl with s≡ | rs≅
    complete∘sound f ._ (.bs ∶ rs′ ∶ʳ true)  (∣-left (∣-left (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) s≡ rs≅ | (refl , refl) | refl | refl | refl
      rewrite complete∘sound (specialise f true) rs′ rs′ x∈ refl refl
            | Tok.η t∈ = refl
    complete∘sound f rs (bs′ ∶ rs′ ∶ʳ false) (∣-left (∣-left (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) s≡ rs≅ | (refl , refl)
      with proj₂ $ ListProp.∷ʳ-injective bs bs′ s≡
    ... | ()
    complete∘sound f rs []                   (∣-left (∣-left (_⊛_ {s₁ = []}    (<$> x∈) t∈))) () _   | (refl , refl)
    complete∘sound f rs []                   (∣-left (∣-left (_⊛_ {s₁ = _ ∷ _} (<$> x∈) t∈))) () _   | (refl , refl)

    complete∘sound f rs rs′ (∣-left (∣-right ._ (<$> x∈ ⊛ t∈))) s≡ rs≅ with Tok.sound false t∈
    complete∘sound f rs (bs′ ∶ rs′ ∶ʳ false) (∣-left (∣-right ._ (_⊛_ {s₁ = bs} (<$> x∈) t∈))) s≡ rs≅ | (refl , refl)
      with proj₁ $ ListProp.∷ʳ-injective bs bs′ s≡
    complete∘sound f rs (.bs ∶ rs′ ∶ʳ false) (∣-left (∣-right ._ (_⊛_ {s₁ = bs} (<$> x∈) t∈))) s≡ rs≅ | (refl , refl) | refl with s≡ | rs≅
    complete∘sound f ._ (.bs ∶ rs′ ∶ʳ false) (∣-left (∣-right ._ (_⊛_ {s₁ = bs} (<$> x∈) t∈))) s≡ rs≅ | (refl , refl) | refl | refl | refl
      rewrite complete∘sound (specialise f false) rs′ rs′ x∈ refl refl
            | Tok.η t∈ = refl
    complete∘sound f rs (bs′ ∶ rs′ ∶ʳ true)  (∣-left (∣-right ._ (_⊛_ {s₁ = bs} (<$> x∈) t∈))) s≡ rs≅ | (refl , refl)
      with proj₂ $ ListProp.∷ʳ-injective bs bs′ s≡
    ... | ()
    complete∘sound f rs []                   (∣-left (∣-right ._ (_⊛_ {s₁ = []} (<$> x∈) t∈))) () _   | (refl , refl)
    complete∘sound f rs []                (∣-left (∣-right ._ (_⊛_ {s₁ = _ ∷ _} (<$> x∈) t∈))) () _   | (refl , refl)

  -- A corollary.

  maximally-expressive :
    ∀ {R} (f : List Bool → List R) {s} →
    parse (grammar f) s ≈[ bag ] f s
  maximally-expressive f {s} {x} =
    (x ∈ parse (grammar f) s)  ⇿⟨ sym Backend.correct ⟩
    x ∈ grammar f · s          ⇿⟨ grammar-correct f ⟩
    x ∈ f s                    ∎
    where open Inv.EquationalReasoning
