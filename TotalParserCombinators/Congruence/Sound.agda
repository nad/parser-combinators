------------------------------------------------------------------------
-- The parser equivalence proof language is sound
------------------------------------------------------------------------

module TotalParserCombinators.Congruence.Sound where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.List as List
import Data.List.Properties as ListProp
import Data.List.Any as Any
import Data.List.Any.BagAndSetEquality as BSEq
open import Data.Maybe
open import Data.Product
open import Function
import Function.Inverse as Inv
import Relation.Binary.PropositionalEquality as P

open Any.Membership-≡ using (bag; _∈_) renaming (_≈[_]_ to _List-≈[_]_)
open Inv.EquationalReasoning
  renaming (_≈⟨_⟩_ to _≈⟨_⟩′_; _∎ to _∎′; sym to sym′)
open RawMonad List.monad
  using () renaming (_⊛_ to _⊛′_; _>>=_ to _>>=′_)
private
  module BSMonoid {k} {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid k A)

open import TotalParserCombinators.BreadthFirst using (D)
open import TotalParserCombinators.CoinductiveEquality as CE
  using (_≈[_]c_; _∷_)
open import TotalParserCombinators.Congruence
open import TotalParserCombinators.Laws
open import TotalParserCombinators.Lib using (return⋆)
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics using (_≈[_]_)

------------------------------------------------------------------------
-- Some lemmas

private

  ⊛-[] : ∀ {A B : Set} (fs : List (A → B)) xs {k} →
         [] List-≈[ k ] xs →
         [] List-≈[ k ] (fs ⊛′ xs)
  ⊛-[] fs xs []≈xs {x} =
    x ∈ []          ≈⟨ BSMonoid.reflexive $ P.sym $
                         ListProp.Applicative.right-zero fs ⟩′
    x ∈ (fs ⊛′ [])  ≈⟨ BSEq.⊛-cong (BSMonoid.refl {x = fs}) []≈xs ⟩′
    x ∈ (fs ⊛′ xs)  ∎′

  ⊛flatten-lemma : ∀ {k} {R₁ R₂ : Set} {fs₁ fs₂ : List (R₁ → R₂)}
                   (xs₁ xs₂ : Maybe (List R₁)) →
                   fs₁ List-≈[ k ] fs₂ →
                   flatten xs₁ List-≈[ k ] flatten xs₂ →
                   fs₁ ⊛flatten xs₁ List-≈[ k ] fs₂ ⊛flatten xs₂
  ⊛flatten-lemma {k} {fs₁ = fs₁} {fs₂} xs₁ xs₂ fs₁≈fs₂ = helper xs₁ xs₂
    where
    helper : ∀ xs₁ xs₂ →
             flatten xs₁ List-≈[ k ] flatten xs₂ →
             fs₁ ⊛flatten xs₁ List-≈[ k ] fs₂ ⊛flatten xs₂
    helper nothing    nothing     []≈[]  = BSMonoid.refl
    helper nothing    (just xs₂)  []≈xs₂ = ⊛-[] fs₂ xs₂ []≈xs₂
    helper (just xs₁) nothing    xs₁≈[]  = BSMonoid.sym $
                                             ⊛-[] fs₁ xs₁ $
                                               BSMonoid.sym xs₁≈[]
    helper (just xs₁) (just xs₂) xs₁≈xs₂ = BSEq.⊛-cong fs₁≈fs₂ xs₁≈xs₂

  []-⊛flatten : ∀ {A B : Set} (xs : Maybe (List A)) →
                [] ⊛flatten xs List-≈[ bag ] ([] ∶ List B)
  []-⊛flatten nothing   = BSMonoid.refl
  []-⊛flatten (just xs) = BSMonoid.refl

  >>=-[] : ∀ {A B : Set} xs (f : A → List B) {k} →
           (∀ x → [] List-≈[ k ] f x) →
           [] List-≈[ k ] (xs >>=′ f)
  >>=-[] xs f []≈f {x} =
    x ∈ []                  ≈⟨ BSMonoid.reflexive $ P.sym $
                                 ListProp.Monad.right-zero xs ⟩′
    x ∈ (xs >>=′ λ _ → [])  ≈⟨ BSEq.>>=-cong (BSMonoid.refl {x = xs})
                                             []≈f ⟩′
    x ∈ (xs >>=′ f)         ∎′

  bind-lemma : ∀ {k} {R₁ R₂ : Set} {xs₁ xs₂ : Maybe (List R₁)}
               (f₁ f₂ : Maybe (R₁ → List R₂)) →
               flatten xs₁ List-≈[ k ] flatten xs₂ →
               (∀ x → apply f₁ x List-≈[ k ] apply f₂ x) →
               bind xs₁ f₁ List-≈[ k ] bind xs₂ f₂
  bind-lemma {k} {xs₁ = xs₁} {xs₂} f₁ f₂ xs₁≈xs₂ = helper f₁ f₂
    where
    helper : ∀ f₁ f₂ →
             (∀ x → apply f₁ x List-≈[ k ] apply f₂ x) →
             bind xs₁ f₁ List-≈[ k ] bind xs₂ f₂
    helper nothing   nothing   f₁≈f₂ = BSMonoid.refl
    helper nothing   (just f₂) f₁≈f₂ = >>=-[] (flatten xs₂) f₂ f₁≈f₂
    helper (just f₁) nothing   f₁≈f₂ = BSMonoid.sym $
                                         >>=-[] (flatten xs₁) f₁
                                           (BSMonoid.sym ∘ f₁≈f₂)
    helper (just f₁) (just f₂) f₁≈f₂ = BSEq.>>=-cong xs₁≈xs₂ f₁≈f₂

  bind-nothing : ∀ {A B : Set} (f : Maybe (A → List B)) →
                 bind nothing f List-≈[ bag ] []
  bind-nothing nothing  = BSMonoid.refl
  bind-nothing (just f) = BSMonoid.refl

------------------------------------------------------------------------
-- Equality is closed under initial-bag

initial-bag-cong :
  ∀ {k Tok R xs₁ xs₂} {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
  p₁ ≈[ k ]P p₂ → initial-bag p₁ List-≈[ k ] initial-bag p₂
initial-bag-cong (xs₁≈xs₂ ∷ Dp₁≈Dp₂)   = xs₁≈xs₂
initial-bag-cong (p ∎)                 = BSMonoid.refl
initial-bag-cong (p₁ ≈⟨ p₁≈p₂ ⟩ p₂≈p₃) = _ ≈⟨ initial-bag-cong p₁≈p₂ ⟩′ initial-bag-cong p₂≈p₃
initial-bag-cong (p₁ ≅⟨ p₁≅p₂ ⟩ p₂≈p₃) = _ ⇿⟨ initial-bag-cong p₁≅p₂ ⟩  initial-bag-cong p₂≈p₃
initial-bag-cong (sym p₁≈p₂)           = sym′ (initial-bag-cong p₁≈p₂)
initial-bag-cong (return x₁≡x₂)        = BSMonoid.reflexive $ P.cong [_] x₁≡x₂
initial-bag-cong fail                  = BSMonoid.refl
initial-bag-cong token                 = BSMonoid.refl
initial-bag-cong (p₁≈p₃ ∣ p₂≈p₄)       = BSMonoid.∙-cong (initial-bag-cong p₁≈p₃) (initial-bag-cong p₂≈p₄)
initial-bag-cong (f₁≗f₂ <$> p₁≈p₂)     = BSEq.map-cong f₁≗f₂ $ initial-bag-cong p₁≈p₂
initial-bag-cong (nonempty p₁≈p₂)      = BSMonoid.refl

initial-bag-cong (cast {xs₁  = xs₁}  {xs₂  = xs₂}
                       {xs₁′ = xs₁′} {xs₂′ = xs₂′}
                       {xs₁≈xs₁′ = xs₁≈xs₁′} {xs₂≈xs₂′ = xs₂≈xs₂′}
                       p₁≈p₂) {x} =
  x ∈ xs₁′  ⇿⟨ sym′ xs₁≈xs₁′ ⟩
  x ∈ xs₁   ≈⟨ initial-bag-cong p₁≈p₂ ⟩′
  x ∈ xs₂   ⇿⟨ xs₂≈xs₂′ ⟩
  x ∈ xs₂′  ∎′

initial-bag-cong ([ nothing          - _       ] p₁≈p₃ ⊛ p₂≈p₄)     = BSMonoid.refl
initial-bag-cong ([ just (xs₁ , xs₂) - just _  ] p₁≈p₃ ⊛ p₂≈p₄)     = ⊛flatten-lemma xs₁ xs₂
                                                                        (initial-bag-cong p₁≈p₃) (initial-bag-cong p₂≈p₄)
initial-bag-cong ([ just (xs₁ , xs₂) - nothing ] p₁≈p₃ ⊛ p₂≈p₄) {x} =
  x ∈ [] ⊛flatten xs₁  ⇿⟨ []-⊛flatten xs₁ ⟩
  x ∈ []               ⇿⟨ sym′ $ []-⊛flatten xs₂ ⟩
  x ∈ [] ⊛flatten xs₂  ∎′

initial-bag-cong ([ nothing        - _       ] p₁≈p₃ >>= p₂≈p₄)     = BSMonoid.refl
initial-bag-cong ([ just (f₁ , f₂) - just _  ] p₁≈p₃ >>= p₂≈p₄)     = bind-lemma f₁ f₂
                                                                        (initial-bag-cong p₁≈p₃) (λ x → initial-bag-cong (p₂≈p₄ x))
initial-bag-cong ([ just (f₁ , f₂) - nothing ] p₁≈p₃ >>= p₂≈p₄) {x} =
  x ∈ bind nothing f₁  ⇿⟨ bind-nothing f₁ ⟩
  x ∈ []               ⇿⟨ sym′ $ bind-nothing f₂ ⟩
  x ∈ bind nothing f₂  ∎′

------------------------------------------------------------------------
-- Equality is closed under D

D-cong : ∀ {k Tok R xs₁ xs₂}
           {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
         p₁ ≈[ k ]P p₂ → ∀ {t} → D t p₁ ≈[ k ]P D t p₂
D-cong (xs₁≈xs₂ ∷ Dp₁≈Dp₂)   {t} = ♭ (Dp₁≈Dp₂ t)
D-cong (p ∎)                 {t} = D t p ∎
D-cong (p₁ ≈⟨ p₁≈p₂ ⟩ p₂≈p₃) {t} = D t p₁ ≈⟨ D-cong p₁≈p₂ ⟩ D-cong p₂≈p₃
D-cong (p₁ ≅⟨ p₁≅p₂ ⟩ p₂≈p₃) {t} = D t p₁ ≅⟨ D-cong p₁≅p₂ ⟩ D-cong p₂≈p₃
D-cong (sym p₁≈p₂)               = sym (D-cong p₁≈p₂)
D-cong (return x₁≡x₂)            = fail ∎
D-cong fail                      = fail ∎
D-cong token                 {t} = return t ∎
D-cong (p₁≈p₃ ∣ p₂≈p₄)           = D-cong p₁≈p₃ ∣ D-cong p₂≈p₄
D-cong (f₁≗f₂ <$> p₁≈p₂)         = f₁≗f₂ <$> D-cong p₁≈p₂
D-cong (nonempty p₁≈p₂)          = D-cong p₁≈p₂
D-cong (cast p₁≈p₂)              = D-cong p₁≈p₂

D-cong ([_-_]_⊛_ nothing nothing {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t} =
  D t (p₁ ⊛ p₂)  ≈⟨ [ nothing - just (○ , ○) ] ♯ D-cong (♭ p₁≈p₃) ⊛ ♭ p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)  ∎
D-cong ([_-_]_⊛_ nothing (just (fs₁ , fs₂)) {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t} =
  D t (p₁ ⊛ p₂)                                               ≅⟨ D.D-⊛ p₁ p₂ ⟩
    D t (♭ p₁) ⊛ ♭? p₂ ∣ return⋆ (flatten fs₁) ⊛ D t (♭? p₂)  ≅⟨ [ ○ - ◌ - ○ - ○ ] D t (♭ p₁) ∎ ⊛ (♭? p₂ ∎) ∣ (_ ∎) ⟩
  ♯ D t (♭ p₁) ⊛ ♭? p₂ ∣ return⋆ (flatten fs₁) ⊛ D t (♭? p₂)  ≈⟨ [ nothing - just (○ , ○) ] ♯ D-cong (♭ p₁≈p₃) ⊛ p₂≈p₄ ∣
                                                                 [ just (○ , ○) - just (○ , ○) ]
                                                                   Return⋆.cong (initial-bag-cong (♭ p₁≈p₃)) ⊛ D-cong p₂≈p₄ ⟩
  ♯ D t (♭ p₃) ⊛ ♭? p₄ ∣ return⋆ (flatten fs₂) ⊛ D t (♭? p₄)  ≅⟨ [ ◌ - ○ - ○ - ○ ] D t (♭ p₃) ∎ ⊛ (♭? p₄ ∎) ∣ (_ ∎) ⟩
    D t (♭ p₃) ⊛ ♭? p₄ ∣ return⋆ (flatten fs₂) ⊛ D t (♭? p₄)  ≅⟨ sym $ D.D-⊛ p₃ p₄ ⟩
  D t (p₃ ⊛ p₄)                                               ∎
D-cong ([_-_]_⊛_ (just _) nothing {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t} =
  D t (p₁ ⊛ p₂)                                   ≅⟨ D.D-⊛ p₁ p₂ ⟩
  D t (♭? p₁) ⊛ ♭ p₂ ∣ return⋆ [] ⊛   D t (♭ p₂)  ≅⟨ (D t (♭? p₁) ⊛ ♭ p₂ ∎) ∣
                                                     [ ○ - ○ - ○ - ◌ ] return⋆ [] ∎ ⊛ (D t (♭ p₂) ∎) ⟩
  D t (♭? p₁) ⊛ ♭ p₂ ∣ return⋆ [] ⊛ ♯ D t (♭ p₂)  ≈⟨ [ just (○ , ○) - just (○ , ○) ] D-cong p₁≈p₃ ⊛ ♭ p₂≈p₄ ∣
                                                     [ just (○ , ○) - nothing ] (return⋆ [] ∎) ⊛ ♯ D-cong (♭ p₂≈p₄) ⟩
  D t (♭? p₃) ⊛ ♭ p₄ ∣ return⋆ [] ⊛ ♯ D t (♭ p₄)  ≅⟨ (D t (♭? p₃) ⊛ ♭ p₄ ∎) ∣
                                                     [ ○ - ○ - ◌ - ○ ] return⋆ [] ∎ ⊛ (D t (♭ p₄) ∎) ⟩
  D t (♭? p₃) ⊛ ♭ p₄ ∣ return⋆ [] ⊛   D t (♭ p₄)  ≅⟨ sym $ D.D-⊛ p₃ p₄ ⟩
  D t (p₃ ⊛ p₄)                                   ∎
D-cong ([_-_]_⊛_ (just _) (just (fs₁ , fs₂)) {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t} =
  D t (p₁ ⊛ p₂)                                              ≅⟨ D.D-⊛ p₁ p₂ ⟩
  D t (♭? p₁) ⊛ ♭? p₂ ∣ return⋆ (flatten fs₁) ⊛ D t (♭? p₂)  ≈⟨ [ just (○ , ○) - just (○ , ○) ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                                                                [ just (○ , ○) - just (○ , ○) ] Return⋆.cong (initial-bag-cong p₁≈p₃) ⊛
                                                                                                D-cong p₂≈p₄ ⟩
  D t (♭? p₃) ⊛ ♭? p₄ ∣ return⋆ (flatten fs₂) ⊛ D t (♭? p₄)  ≅⟨ sym $ D.D-⊛ p₃ p₄ ⟩
  D t (p₃ ⊛ p₄)                                              ∎

D-cong ([_-_]_>>=_ nothing nothing {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t} =
  D t (p₁ >>= p₂)  ≈⟨ [ nothing - just (○ , ○) ] ♯ D-cong (♭ p₁≈p₃) >>= (♭ ∘ p₂≈p₄) ⟩
  D t (p₃ >>= p₄)  ∎
D-cong ([_-_]_>>=_ nothing (just (xs₁ , xs₂)) {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t} =
  D t (p₁ >>= p₂)                                                         ≅⟨ D.D->>= p₁ p₂ ⟩
    D t (♭ p₁) >>= (♭? ∘ p₂) ∣ return⋆ (flatten xs₁) >>= (D t ∘ ♭? ∘ p₂)  ≅⟨ [ ○ - ◌ - ○ - ○ ] D t (♭ p₁) ∎ >>= (λ x → ♭? (p₂ x) ∎) ∣
                                                                             (_ ∎) ⟩
  ♯ D t (♭ p₁) >>= (♭? ∘ p₂) ∣ return⋆ (flatten xs₁) >>= (D t ∘ ♭? ∘ p₂)  ≈⟨ [ nothing - just (○ , ○) ] ♯ D-cong (♭ p₁≈p₃) >>= p₂≈p₄ ∣
                                                                             [ just (○ , ○) - just (○ , ○) ]
                                                                               Return⋆.cong (initial-bag-cong (♭ p₁≈p₃)) >>=
                                                                               (λ x → D-cong (p₂≈p₄ x)) ⟩
  ♯ D t (♭ p₃) >>= (♭? ∘ p₄) ∣ return⋆ (flatten xs₂) >>= (D t ∘ ♭? ∘ p₄)  ≅⟨ [ ◌ - ○ - ○ - ○ ] D t (♭ p₃) ∎ >>= (λ x → ♭? (p₄ x) ∎) ∣
                                                                             (_ ∎) ⟩
    D t (♭ p₃) >>= (♭? ∘ p₄) ∣ return⋆ (flatten xs₂) >>= (D t ∘ ♭? ∘ p₄)  ≅⟨ sym $ D.D->>= p₃ p₄ ⟩
  D t (p₃ >>= p₄)                                                         ∎
D-cong ([_-_]_>>=_ (just _) nothing {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t} =
  D t (p₁ >>= p₂)                                                     ≅⟨ D.D->>= p₁ p₂ ⟩
  D t (♭? p₁) >>= (♭ ∘ p₂) ∣ return⋆ [] >>= (D t ∘ ♭ ∘ p₂)            ≅⟨ (D t (♭? p₁) >>= (♭ ∘ p₂) ∎) ∣
                                                                         [ ○ - ○ - ○ - ◌ ] return⋆ [] ∎ >>= (λ x → D t (♭ (p₂ x)) ∎) ⟩
  D t (♭? p₁) >>= (♭ ∘ p₂) ∣ return⋆ [] >>= (λ x → ♯ D t (♭ (p₂ x)))  ≈⟨ [ just (○ , ○) - just (○ , ○) ] D-cong p₁≈p₃ >>= (♭ ∘ p₂≈p₄) ∣
                                                                         [ just (○ , ○) - nothing ] (return⋆ [] ∎) >>=
                                                                                                    (λ x → ♯ D-cong (♭ (p₂≈p₄ x))) ⟩
  D t (♭? p₃) >>= (♭ ∘ p₄) ∣ return⋆ [] >>= (λ x → ♯ D t (♭ (p₄ x)))  ≅⟨ (D t (♭? p₃) >>= (♭ ∘ p₄) ∎) ∣
                                                                         [ ○ - ○ - ◌ - ○ ] return⋆ [] ∎ >>= (λ x → D t (♭ (p₄ x)) ∎) ⟩
  D t (♭? p₃) >>= (♭ ∘ p₄) ∣ return⋆ [] >>= (D t ∘ ♭ ∘ p₄)            ≅⟨ sym $ D.D->>= p₃ p₄ ⟩
  D t (p₃ >>= p₄)                                                     ∎
D-cong ([_-_]_>>=_ (just _) (just (xs₁ , xs₂)) {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t} =
  D t (p₁ >>= p₂)                                                        ≅⟨ D.D->>= p₁ p₂ ⟩
  D t (♭? p₁) >>= (♭? ∘ p₂) ∣ return⋆ (flatten xs₁) >>= (D t ∘ ♭? ∘ p₂)  ≈⟨ [ just (○ , ○) - just (○ , ○) ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                                                                            [ just (○ , ○) - just (○ , ○) ]
                                                                              Return⋆.cong (initial-bag-cong p₁≈p₃) >>=
                                                                              (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (♭? p₃) >>= (♭? ∘ p₄) ∣ return⋆ (flatten xs₂) >>= (D t ∘ ♭? ∘ p₄)  ≅⟨ sym $ D.D->>= p₃ p₄ ⟩
  D t (p₃ >>= p₄)                                                        ∎

------------------------------------------------------------------------
-- Soundness

sound : ∀ {k Tok R xs₁ xs₂}
          {p₁ : Parser Tok R xs₁}
          {p₂ : Parser Tok R xs₂} →
        p₁ ≈[ k ]P p₂ → p₁ ≈[ k ] p₂
sound = CE.sound ∘ sound′
  where
  sound′ : ∀ {k Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁}
             {p₂ : Parser Tok R xs₂} →
           p₁ ≈[ k ]P p₂ → p₁ ≈[ k ]c p₂
  sound′ p₁≈p₂ = initial-bag-cong p₁≈p₂ ∷ λ t → ♯ sound′ (D-cong p₁≈p₂)
