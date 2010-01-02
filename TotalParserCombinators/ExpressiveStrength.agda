------------------------------------------------------------------------
-- This module proves that the parser combinators correspond exactly
-- to functions of type List Tok → List R (if bag equality is used for
-- the lists of results)
------------------------------------------------------------------------

module TotalParserCombinators.ExpressiveStrength where

open import Coinduction
open import Data.Bool
open import Function
open import Function.Inverse using (_⇿_)
open import Data.List as List
open import Data.List.Any
open Membership-≡
import Data.List.Properties as ListProp
open import Data.List.Reverse
open import Data.Product
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality
  using (_≅_; _≇_; refl)
open import Relation.Nullary

open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics hiding (_≅_)
open import TotalParserCombinators.Lib
private
  open module Tok = Token Bool _≟_ using (tok)
import TotalParserCombinators.BreadthFirst as Backend
import TotalParserCombinators.BreadthFirst.LeftInverse  as Left
import TotalParserCombinators.BreadthFirst.RightInverse as Right

------------------------------------------------------------------------
-- Boring lemmas

private

  indices-equal : {A : Set} {xs ys : List A}
                  {rxs : Reverse xs} {rys : Reverse ys} →
                  rxs ≅ rys → xs ≡ ys
  indices-equal refl = refl

  η-cast∈ : ∀ {Tok R x xs s} {p : Parser Tok R xs} {x∈} →
            ((x∈′ : x ∈ p · s) → x∈′ ≡ x∈) →
            ∀ {R′} (xs′ : List R′)
            (x∈′ : x ∈ ♭? {xs = xs′} (♯? p) · s) →
            x∈′ ≡ cast∈ refl (P.sym (♭?♯? xs′)) refl x∈
  η-cast∈ hyp []      x∈′ = hyp x∈′
  η-cast∈ hyp (_ ∷ _) x∈′ = hyp x∈′

  tok-lemma : ∀ {R t}
          (xs : List R) (t∈ : t ∈ ♭? {xs = xs} (♯? (tok t)) · [ t ]) →
          t∈ ≡ cast∈ refl (P.sym (♭?♯? xs)) refl (Tok.complete {t = t})
  tok-lemma = η-cast∈ Tok.η

------------------------------------------------------------------------
-- Expressive strength

-- One direction of the correspondence has already been established:
-- For every parser there is an equivalent function.

parser⇒fun : ∀ {R xs} (p : Parser Bool R xs) →
             ∃ λ (f : List Bool → List R) →
               ∀ x s → x ∈ p · s ⇿ x ∈ f s
parser⇒fun p =
  ( Backend.parseComplete p
  , λ _ s → record
      { to         = P.→-to-⟶ (Backend.complete s)
      ; from       = P.→-to-⟶ (Backend.sound s)
      ; inverse-of = record
        { left-inverse-of  = Right.sound∘complete s
        ; right-inverse-of = Left.complete∘sound s p
        }
      }
  )

-- For every function there is a corresponding parser.

fun⇒parser : ∀ {Tok R} (f : List Tok → List R) →
             ∃ λ (p : Parser Tok R (f [])) →
               ∀ x s → x ∈ p · s ⇿ x ∈ f s
fun⇒parser {Tok} {R} f =
  ( p f
  , λ _ s → record
      { to         = P.→-to-⟶ (sound f)
      ; from       = P.→-to-⟶ (complete f s)
      ; inverse-of = record
        { left-inverse-of  = complete∘sound f
        ; right-inverse-of = sound∘complete f s
        }
      }
  )
  where
  p : (f : List Tok → List R) → Parser Tok R (f [])
  p f = token >>= (λ t → ⟪ ♯ p (f ∘ _∷_ t) ⟫)
      ∣ return⋆ (f [])

  sound : ∀ {x s} f → x ∈ p f · s → x ∈ f s
  sound f (∣ʳ ._ x∈) with Return⋆.sound (f []) x∈
  ... | (refl , x∈′) = x∈′
  sound f (∣ˡ (token {t} >>= x∈)) = sound (f ∘ _∷_ t) x∈

  complete : ∀ {x} f s → x ∈ f s → x ∈ p f · s
  complete f []      x∈ = ∣ʳ [] (Return⋆.complete x∈)
  complete f (t ∷ s) x∈ = ∣ˡ (token >>= complete (f ∘ _∷_ t) s x∈)

  complete∘sound : ∀ {x s} f (x∈pf : x ∈ p f · s) →
                   complete f s (sound f x∈pf) ≡ x∈pf
  complete∘sound f (∣ˡ (token {t} >>= x∈))
    rewrite complete∘sound (f ∘ _∷_ t) x∈ = refl
  complete∘sound f (∣ʳ .[] x∈)
    with Return⋆.sound (f []) x∈ | Return⋆.complete∘sound (f []) x∈
  complete∘sound f (∣ʳ .[] .(Return⋆.complete x∈f[]))
    | (refl , x∈f[]) | refl = refl

  sound∘complete : ∀ {x} f s (x∈fs : x ∈ f s) →
                   sound f (complete f s x∈fs) ≡ x∈fs
  sound∘complete f (t ∷ s) x∈ = sound∘complete (f ∘ _∷_ t) s x∈
  sound∘complete f []      x∈
    with Return⋆.sound {Tok = Tok} (f []) (Return⋆.complete x∈)
       | Return⋆.sound∘complete {Tok = Tok} x∈
  ... | (refl , .x∈) | refl = refl

-- If the token type is finite (in this case Bool), then the result
-- above can be established without the use of bind (_>>=_). (The
-- definition of tok uses bind, but if bind were removed it would be
-- reasonable to either add tok as a primitive combinator, or make it
-- possible to define tok using other combinators.)

fun⇒parser′ : ∀ {R} (f : List Bool → List R) →
              ∃ λ (p : Parser Bool R (f [])) →
                ∀ x s → x ∈ p · s ⇿ x ∈ f s
fun⇒parser′ {R} f =
  ( p f
  , λ _ s → record
      { to         = P.→-to-⟶ (sound f)
      ; from       = P.→-to-⟶ (complete f (reverseView s))
      ; inverse-of = record
        { right-inverse-of = sound∘complete f (reverseView s)
        ; left-inverse-of  = λ x∈ →
            complete∘sound f (reverseView s) _ x∈ refl
        }
      }
  )
  where
  specialise : {A B : Set} → (List A → B) → A → (List A → B)
  specialise f x = λ xs → f (xs ∷ʳ x)

  p : (f : List Bool → List R) → Parser Bool R (f [])
  p f = ⟪ ♯ (const <$> p (specialise f true )) ⟫ ⊛ ♯? (tok true)
      ∣ ⟪ ♯ (const <$> p (specialise f false)) ⟫ ⊛ ♯? (tok false)
      ∣ return⋆ (f [])

  sound : ∀ {x s} f → x ∈ p f · s → x ∈ f s
  sound f (∣ʳ ._ x∈) with Return⋆.sound (f []) x∈
  ... | (refl , x∈′) = x∈′
  sound f (∣ˡ (∣ˡ (<$> x∈ ⊛ t∈))) with
    Tok.sound (cast∈ refl (♭?♯? (List.map const (f [ true  ]))) refl t∈)
  ... | (refl , refl) = sound (specialise f true ) x∈
  sound f (∣ˡ (∣ʳ ._ (<$> x∈ ⊛ t∈))) with
    Tok.sound (cast∈ refl (♭?♯? (List.map const (f [ false ]))) refl t∈)
  ... | (refl , refl) = sound (specialise f false) x∈

  complete : ∀ {x s} f → Reverse s → x ∈ f s → x ∈ p f · s
  complete f []                 x∈ = ∣ʳ [] (Return⋆.complete x∈)
  complete f (bs ∶ rs ∶ʳ true ) x∈ =
    ∣ˡ {xs₁ = []} (∣ˡ (
      <$> complete (specialise f true ) rs x∈ ⊛
      cast∈ refl (P.sym (♭?♯? (List.map const (f [ true  ])))) refl
            Tok.complete))
  complete f (bs ∶ rs ∶ʳ false) x∈ =
    ∣ˡ (∣ʳ [] (
      <$> complete (specialise f false) rs x∈ ⊛
      cast∈ refl (P.sym (♭?♯? (List.map const (f [ false ])))) refl
            Tok.complete))

  sound∘complete : ∀ {x s} f (rs : Reverse s) (x∈fs : x ∈ f s) →
                   sound f (complete f rs x∈fs) ≡ x∈fs
  sound∘complete f [] x∈
    rewrite Return⋆.sound∘complete {Tok = Bool} x∈ = refl
  sound∘complete f (bs ∶ rs ∶ʳ true) x∈
    with cast∈ refl lem refl $ cast∈ refl (P.sym lem) refl $
               Tok.complete {t = true}
       | cast∈∘cast∈-sym refl lem refl (Tok.complete {t = true})
    where lem = ♭?♯? (List.map (const {B = Bool}) (f [ true ]))
  ... | .Tok.complete | refl = sound∘complete (specialise f true) rs x∈
  sound∘complete f (bs ∶ rs ∶ʳ false) x∈
    with cast∈ refl lem refl $ cast∈ refl (P.sym lem) refl $
               Tok.complete {t = false}
       | cast∈∘cast∈-sym refl lem refl (Tok.complete {t = false})
    where lem = ♭?♯? (List.map (const {B = Bool}) (f [ false ]))
  ... | .Tok.complete | refl = sound∘complete (specialise f false) rs x∈

  complete∘sound : ∀ {x} {s s′ : List Bool}
                   f (rs : Reverse s) (rs′ : Reverse s′)
                   (x∈pf : x ∈ p f · s) → rs ≅ rs′ →
                   complete f rs (sound f x∈pf) ≡ x∈pf

  complete∘sound f rs rs′ (∣ʳ ._ x∈) eq
    with Return⋆.sound (f []) x∈
       | Return⋆.complete∘sound (f []) x∈
  complete∘sound f ._ []                 (∣ʳ ._ .(Return⋆.complete x∈′)) refl | (refl , x∈′) | refl = refl
  complete∘sound f _  ([]      ∶ _ ∶ʳ _) (∣ʳ ._ .(Return⋆.complete x∈′)) ()   | (refl , x∈′) | refl
  complete∘sound f _  ((_ ∷ _) ∶ _ ∶ʳ _) (∣ʳ ._ .(Return⋆.complete x∈′)) ()   | (refl , x∈′) | refl

  complete∘sound f rs rs′ (∣ˡ (∣ˡ (<$> x∈ ⊛ t∈))) eq
    with Tok.sound (cast∈ refl (♭?♯? (List.map const (f [ true  ]))) refl t∈)
  complete∘sound f rs (bs′ ∶ rs′ ∶ʳ true)  (∣ˡ (∣ˡ (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) eq | (refl , refl)
    with proj₁ $ ListProp.∷ʳ-injective bs bs′ (indices-equal eq)
  complete∘sound f rs (.bs ∶ rs′ ∶ʳ true)  (∣ˡ (∣ˡ (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) eq | (refl , refl) | refl with eq
  complete∘sound f ._ (.bs ∶ rs′ ∶ʳ true)  (∣ˡ (∣ˡ (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) eq | (refl , refl) | refl | refl
    rewrite complete∘sound (specialise f true) rs′ rs′ x∈ refl
          | tok-lemma (List.map const (f [ true  ])) t∈ = refl
  complete∘sound f rs (bs′ ∶ rs′ ∶ʳ false) (∣ˡ (∣ˡ (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) eq | (refl , refl)
    with proj₂ $ ListProp.∷ʳ-injective bs bs′ (indices-equal eq)
  ... | ()
  complete∘sound f rs []                   (∣ˡ (∣ˡ (_⊛_ {s₁ = []}    (<$> x∈) t∈))) () | (refl , refl)
  complete∘sound f rs []                   (∣ˡ (∣ˡ (_⊛_ {s₁ = _ ∷ _} (<$> x∈) t∈))) () | (refl , refl)

  complete∘sound f rs rs′ (∣ˡ (∣ʳ ._ (<$> x∈ ⊛ t∈))) eq
    with Tok.sound (cast∈ refl (♭?♯? (List.map const (f [ false ]))) refl t∈)
  complete∘sound f rs (bs′ ∶ rs′ ∶ʳ false) (∣ˡ (∣ʳ ._ (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) eq | (refl , refl)
    with proj₁ $ ListProp.∷ʳ-injective bs bs′ (indices-equal eq)
  complete∘sound f rs (.bs ∶ rs′ ∶ʳ false) (∣ˡ (∣ʳ ._ (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) eq | (refl , refl) | refl with eq
  complete∘sound f ._ (.bs ∶ rs′ ∶ʳ false) (∣ˡ (∣ʳ ._ (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) eq | (refl , refl) | refl | refl
    rewrite complete∘sound (specialise f false) rs′ rs′ x∈ refl
          | tok-lemma (List.map const (f [ false ])) t∈ = refl
  complete∘sound f rs (bs′ ∶ rs′ ∶ʳ true)  (∣ˡ (∣ʳ ._ (_⊛_ {s₁ = bs}    (<$> x∈) t∈))) eq | (refl , refl)
    with proj₂ $ ListProp.∷ʳ-injective bs bs′ (indices-equal eq)
  ... | ()
  complete∘sound f rs []                   (∣ˡ (∣ʳ ._ (_⊛_ {s₁ = []}    (<$> x∈) t∈))) () | (refl , refl)
  complete∘sound f rs []                   (∣ˡ (∣ʳ ._ (_⊛_ {s₁ = _ ∷ _} (<$> x∈) t∈))) () | (refl , refl)
