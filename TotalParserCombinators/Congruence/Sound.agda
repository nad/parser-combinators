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
open import Function
import Function.Inverse as Inv
import Relation.Binary.PropositionalEquality as P

open Any.Membership-≡ using (_∈_) renaming (_≈[_]_ to _List-≈[_]_)
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
open import TotalParserCombinators.Lib
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- Some lemmas

private

  >>=-[]-lemma : ∀ {A B : Set} xs (f : A → List B) {k} →
                 (∀ x → [] List-≈[ k ] f x) →
                 [] List-≈[ k ] (xs >>=′ f)
  >>=-[]-lemma xs f []≈f {x} =
    x ∈ []                  ≈⟨ BSMonoid.reflexive $ P.sym $
                                 ListProp.Monad.right-zero xs ⟩′
    x ∈ (xs >>=′ λ _ → [])  ≈⟨ BSEq.>>=-cong (BSMonoid.refl {x = xs})
                                             []≈f ⟩′
    x ∈ (xs >>=′ f)         ∎′

  ⊛-[]-lemma : ∀ {A B : Set} (fs : List (A → B)) xs {k} →
               [] List-≈[ k ] xs →
               [] List-≈[ k ] (fs ⊛′ xs)
  ⊛-[]-lemma fs xs []≈xs {x} =
    x ∈ []          ≈⟨ BSMonoid.reflexive $ P.sym $
                         ListProp.Applicative.right-zero fs ⟩′
    x ∈ (fs ⊛′ [])  ≈⟨ BSEq.⊛-cong (BSMonoid.refl {x = fs}) []≈xs ⟩′
    x ∈ (fs ⊛′ xs)  ∎′

  >>=-∣-lemma : ∀ {Tok R R′ xs} {f : R′ → List R}
                  {p : Parser Tok R xs}
                  {p′ : (x : R′) → Parser Tok R (f x)} →
                p ≅P p ∣ return⋆ [] >>= p′
  >>=-∣-lemma {p = p} {p′} =
    p                      ≅⟨ sym $ AdditiveMonoid.right-identity p ⟩
    p ∣ fail               ≅⟨ (p ∎) ∣ sym (Monad.left-zero _) ⟩
    p ∣ return⋆ [] >>= p′  ∎

  ⊛-∣-lemma : ∀ {Tok R R′ xs xs′}
                {p : Parser Tok R xs} {p′ : Parser Tok R′ xs′} →
              p ≅P p ∣ return⋆ [] ⊛ p′
  ⊛-∣-lemma {p = p} {p′} =
    p                    ≅⟨ sym $ AdditiveMonoid.right-identity p ⟩
    p ∣ fail             ≅⟨ (p ∎) ∣ sym (ApplicativeFunctor.left-zero _) ⟩
    p ∣ return⋆ [] ⊛ p′  ∎

------------------------------------------------------------------------
-- Equality is closed under initial-bag

same-bag/set : ∀ {k Tok R xs₁ xs₂}
                 {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
               p₁ ≈[ k ]P p₂ → initial-bag p₁ List-≈[ k ] initial-bag p₂
same-bag/set (xs₁≈xs₂ ∷ Dp₁≈Dp₂)                                           = xs₁≈xs₂
same-bag/set (p ∎)                                                         = BSMonoid.refl
same-bag/set (p₁ ≈⟨ p₁≈p₂ ⟩ p₂≈p₃)                                         = _ ≈⟨ same-bag/set p₁≈p₂ ⟩′ same-bag/set p₂≈p₃
same-bag/set (p₁ ≅⟨ p₁≅p₂ ⟩ p₂≈p₃)                                         = _ ⇿⟨ same-bag/set p₁≅p₂ ⟩  same-bag/set p₂≈p₃
same-bag/set (sym p₁≈p₂)                                                   = sym′ (same-bag/set p₁≈p₂)
same-bag/set (return x₁≡x₂)                                                = BSMonoid.reflexive $ P.cong [_] x₁≡x₂
same-bag/set fail                                                          = BSMonoid.refl
same-bag/set token                                                         = BSMonoid.refl
same-bag/set (p₁≈p₃ ∣ p₂≈p₄)                                               = BSMonoid.∙-cong (same-bag/set p₁≈p₃) (same-bag/set p₂≈p₄)
same-bag/set (f₁≗f₂ <$> p₁≈p₂)                                             = BSEq.map-cong f₁≗f₂ $ same-bag/set p₁≈p₂
same-bag/set ([ nothing  - nothing  - fs₁      - fs₂      ] p₁≈p₃ ⊛ p₂≈p₄) = BSMonoid.refl
same-bag/set ([ nothing  - just xs₂ - nothing  - nothing  ] p₁≈p₃ ⊛ p₂≈p₄) = BSMonoid.refl
same-bag/set ([ nothing  - just xs₂ - nothing  - just fs₂ ] p₁≈p₃ ⊛ p₂≈p₄) = ⊛-[]-lemma fs₂ xs₂ $ same-bag/set p₂≈p₄
same-bag/set ([ nothing  - just xs₂ - just fs₁ - fs₂      ] p₁≈p₃ ⊛ p₂≈p₄) = ⊛-[]-lemma (flatten fs₂) xs₂ $ same-bag/set p₂≈p₄
same-bag/set ([ just xs₁ - nothing  - nothing  - fs₂      ] p₁≈p₃ ⊛ p₂≈p₄) = BSMonoid.refl
same-bag/set ([ just xs₁ - nothing  - just fs₁ - fs₂      ] p₁≈p₃ ⊛ p₂≈p₄) = BSMonoid.sym $ ⊛-[]-lemma fs₁ xs₁ $
                                                                               BSMonoid.sym $ same-bag/set p₂≈p₄
same-bag/set ([ just xs₁ - just xs₂ - nothing  - nothing  ] p₁≈p₃ ⊛ p₂≈p₄) = BSMonoid.refl
same-bag/set ([ just xs₁ - just xs₂ - nothing  - just fs₂ ] p₁≈p₃ ⊛ p₂≈p₄) = BSEq.⊛-cong (same-bag/set p₁≈p₃) (same-bag/set p₂≈p₄)
same-bag/set ([ just xs₁ - just xs₂ - just fs₁ - fs₂      ] p₁≈p₃ ⊛ p₂≈p₄) = BSEq.⊛-cong (same-bag/set p₁≈p₃) (same-bag/set p₂≈p₄)
same-bag/set ([ nothing - nothing - xs₁      - xs₂      ] p₁≈p₃ >>= p₂≈p₄) = BSMonoid.refl
same-bag/set ([ nothing - just f₂ - nothing  - nothing  ] p₁≈p₃ >>= p₂≈p₄) = BSMonoid.refl
same-bag/set ([ nothing - just f₂ - nothing  - just xs₂ ] p₁≈p₃ >>= p₂≈p₄) = >>=-[]-lemma xs₂ f₂ $ λ x → same-bag/set (p₂≈p₄ x)
same-bag/set ([ nothing - just f₂ - just xs₁ - xs₂      ] p₁≈p₃ >>= p₂≈p₄) = >>=-[]-lemma (flatten xs₂) f₂ $ λ x → same-bag/set (p₂≈p₄ x)
same-bag/set ([ just f₁ - nothing - nothing  - xs₂      ] p₁≈p₃ >>= p₂≈p₄) = BSMonoid.refl
same-bag/set ([ just f₁ - nothing - just xs₁ - xs₂      ] p₁≈p₃ >>= p₂≈p₄) = BSMonoid.sym $ >>=-[]-lemma xs₁ f₁ $ λ x →
                                                                              BSMonoid.sym $ same-bag/set (p₂≈p₄ x)
same-bag/set ([ just f₁ - just f₂ - nothing  - nothing  ] p₁≈p₃ >>= p₂≈p₄) = BSMonoid.refl
same-bag/set ([ just f₁ - just f₂ - nothing  - just xs₂ ] p₁≈p₃ >>= p₂≈p₄) = BSEq.>>=-cong (same-bag/set p₁≈p₃)
                                                                                           (λ x → same-bag/set (p₂≈p₄ x))
same-bag/set ([ just f₁ - just f₂ - just xs₁ - xs₂      ] p₁≈p₃ >>= p₂≈p₄) = BSEq.>>=-cong (same-bag/set p₁≈p₃)
                                                                                           (λ x → same-bag/set (p₂≈p₄ x))
same-bag/set (nonempty p₁≈p₂)                                              = BSMonoid.refl
same-bag/set (cast {xs₁ = xs₁} {xs₂ = xs₂} {xs₁′ = xs₁′} {xs₂′ = xs₂′}
                   {xs₁≈xs₁′ = xs₁≈xs₁′} {xs₂≈xs₂′} p₁≈p₂) {x}             =
  x ∈ xs₁′  ⇿⟨ sym′ xs₁≈xs₁′ ⟩
  x ∈ xs₁   ≈⟨ same-bag/set p₁≈p₂ ⟩′
  x ∈ xs₂   ⇿⟨ xs₂≈xs₂′ ⟩
  x ∈ xs₂′  ∎′

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

D-cong ([_-_-_-_]_⊛_ _ _ _ _ {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t}
  with forced? p₁ | forced? p₂ | forced? p₃ | forced? p₄
... | nothing | nothing | nothing | nothing =
  D t (p₁ ⊛ p₂)  ≈⟨ [ ◌ - ◌ - ○ - ○ ] ♯ D-cong (♭ p₁≈p₃) ⊛ ♭ p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)  ∎
... | nothing | nothing | nothing | just fs₄ =
  D t (p₁ ⊛ p₂)                            ≅⟨ ⊛-∣-lemma ⟩
  D t (p₁ ⊛ p₂) ∣ return⋆ [] ⊛ D t (♭ p₂)  ≈⟨ [ ◌ - ◌ - ○ - ○ ] ♯ D-cong (♭ p₁≈p₃) ⊛ p₂≈p₄ ∣
                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set (♭ p₁≈p₃)) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)                            ∎
... | nothing | nothing | just xs₃ | nothing =
  D t (p₁ ⊛ p₂)  ≈⟨ [ ◌ - ○ - ○ - ○ ] D-cong p₁≈p₃ ⊛ ♭ p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)  ∎
... | nothing | nothing | just xs₃ | just fs₄ =
  D t (p₁ ⊛ p₂)                            ≅⟨ ⊛-∣-lemma ⟩
  D t (p₁ ⊛ p₂) ∣ return⋆ [] ⊛ D t (♭ p₂)  ≈⟨ [ ◌ - ○ - ○ - ○ ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)                            ∎
... | nothing | just fs₂ | nothing | nothing =
  D t (p₁ ⊛ p₂)                            ≈⟨ [ ◌ - ◌ - ○ - ○ ] ♯ D-cong (♭ p₁≈p₃) ⊛ p₂≈p₄ ∣
                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set (♭ p₁≈p₃)) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄) ∣ return⋆ [] ⊛ D t (♭ p₄)  ≅⟨ sym (⊛-∣-lemma {p = D t (p₃ ⊛ p₄)}) ⟩
  D t (p₃ ⊛ p₄)                            ∎
... | nothing | just fs₂ | nothing | just fs₄ =
  D t (p₁ ⊛ p₂)  ≈⟨ [ ◌ - ◌ - ○ - ○ ] ♯ D-cong (♭ p₁≈p₃) ⊛ p₂≈p₄ ∣
                    [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set (♭ p₁≈p₃)) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)  ∎
... | nothing | just fs₂ | just xs₃ | nothing =
  D t (p₁ ⊛ p₂)                            ≈⟨ [ ◌ - ○ - ○ - ○ ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄) ∣ return⋆ [] ⊛ D t (♭ p₄)  ≅⟨ sym (⊛-∣-lemma {p = D t (p₃ ⊛ p₄)}) ⟩
  D t (p₃ ⊛ p₄)                            ∎
... | nothing | just fs₂ | just xs₃ | just fs₄ =
  D t (p₁ ⊛ p₂)  ≈⟨ [ ◌ - ○ - ○ - ○ ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                    [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)  ∎
... | just xs₁ | nothing | nothing | nothing =
  D t (p₁ ⊛ p₂)  ≈⟨ [ ○ - ◌ - ○ - ○ ] D-cong p₁≈p₃ ⊛ ♭ p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)  ∎
... | just xs₁ | nothing | nothing | just fs₄ =
  D t (p₁ ⊛ p₂)                            ≅⟨ ⊛-∣-lemma ⟩
  D t (p₁ ⊛ p₂) ∣ return⋆ [] ⊛ D t (♭ p₂)  ≈⟨ [ ○ - ◌ - ○ - ○ ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)                            ∎
... | just xs₁ | nothing | just xs₃ | nothing =
  D t (p₁ ⊛ p₂)  ≈⟨ [ ○ - ○ - ○ - ○ ] D-cong p₁≈p₃ ⊛ ♭ p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)  ∎
... | just xs₁ | nothing | just xs₃ | just fs₄ =
  D t (p₁ ⊛ p₂)                            ≅⟨ ⊛-∣-lemma ⟩
  D t (p₁ ⊛ p₂) ∣ return⋆ [] ⊛ D t (♭ p₂)  ≈⟨ [ ○ - ○ - ○ - ○ ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)                            ∎
... | just xs₁ | just fs₂ | nothing | nothing =
  D t (p₁ ⊛ p₂)                            ≈⟨ [ ○ - ◌ - ○ - ○ ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄) ∣ return⋆ [] ⊛ D t (♭ p₄)  ≅⟨ sym (⊛-∣-lemma {p = D t (p₃ ⊛ p₄)}) ⟩
  D t (p₃ ⊛ p₄)                            ∎
... | just xs₁ | just fs₂ | nothing | just fs₄ =
  D t (p₁ ⊛ p₂)  ≈⟨ [ ○ - ◌ - ○ - ○ ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                    [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)  ∎
... | just xs₁ | just fs₂ | just xs₃ | nothing =
  D t (p₁ ⊛ p₂)                            ≈⟨ [ ○ - ○ - ○ - ○ ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄) ∣ return⋆ [] ⊛ D t (♭ p₄)  ≅⟨ sym (⊛-∣-lemma {p = D t (p₃ ⊛ p₄)}) ⟩
  D t (p₃ ⊛ p₄)                            ∎
... | just xs₁ | just fs₂ | just xs₃ | just fs₄ =
  D t (p₁ ⊛ p₂)  ≈⟨ [ ○ - ○ - ○ - ○ ] D-cong p₁≈p₃ ⊛ p₂≈p₄ ∣
                    [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) ⊛ D-cong p₂≈p₄ ⟩
  D t (p₃ ⊛ p₄)  ∎

D-cong ([_-_-_-_]_>>=_ _ _ _ _ {p₁} {p₂} {p₃} {p₄} p₁≈p₃ p₂≈p₄) {t}
  with forced? p₁ | forced?′ p₂ | forced? p₃ | forced?′ p₄
... | nothing | nothing | nothing | nothing =
  D t (p₁ >>= p₂)  ≈⟨ [ ◌ - ◌ - ○ - ○ ] ♯ D-cong (♭ p₁≈p₃) >>= (λ x → ♭ (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)  ∎
... | nothing | nothing | nothing | just xs₄ =
  D t (p₁ >>= p₂)                                          ≅⟨ >>=-∣-lemma ⟩
  D t (p₁ >>= p₂) ∣ return⋆ [] >>= (λ x → D t (♭ (p₂ x)))  ≈⟨ [ ◌ - ◌ - ○ - ○ ] ♯ D-cong (♭ p₁≈p₃) >>= p₂≈p₄ ∣
                                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set (♭ p₁≈p₃)) >>=
                                                                                (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)                                          ∎
... | nothing | nothing | just f₃ | nothing =
  D t (p₁ >>= p₂)  ≈⟨ [ ◌ - ○ - ○ - ○ ] D-cong p₁≈p₃ >>= (λ x → ♭ (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)  ∎
... | nothing | nothing | just f₃ | just xs₄ =
  D t (p₁ >>= p₂)                                          ≅⟨ >>=-∣-lemma ⟩
  D t (p₁ >>= p₂) ∣ return⋆ [] >>= (λ x → D t (♭ (p₂ x)))  ≈⟨ [ ◌ - ○ - ○ - ○ ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) >>=
                                                                                (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)                                          ∎
... | nothing | just xs₂ | nothing | nothing =
  D t (p₁ >>= p₂)                                          ≈⟨ [ ◌ - ◌ - ○ - ○ ] ♯ D-cong (♭ p₁≈p₃) >>= p₂≈p₄ ∣
                                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set (♭ p₁≈p₃)) >>=
                                                                                (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄) ∣ return⋆ [] >>= (λ x → D t (♭ (p₄ x)))  ≅⟨ sym (>>=-∣-lemma {p = D t (p₃ >>= p₄)}) ⟩
  D t (p₃ >>= p₄)                                          ∎
... | nothing | just xs₂ | nothing | just xs₄ =
  D t (p₁ >>= p₂)  ≈⟨ [ ◌ - ◌ - ○ - ○ ] ♯ D-cong (♭ p₁≈p₃) >>= p₂≈p₄ ∣
                      [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set (♭ p₁≈p₃)) >>=
                                        (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)  ∎
... | nothing | just xs₂ | just f₃ | nothing =
  D t (p₁ >>= p₂)                                          ≈⟨ [ ◌ - ○ - ○ - ○ ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) >>=
                                                                                (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄) ∣ return⋆ [] >>= (λ x → D t (♭ (p₄ x)))  ≅⟨ sym (>>=-∣-lemma {p = D t (p₃ >>= p₄)}) ⟩
  D t (p₃ >>= p₄)                                          ∎
... | nothing | just xs₂ | just f₃ | just xs₄ =
  D t (p₁ >>= p₂)  ≈⟨ [ ◌ - ○ - ○ - ○ ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                      [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) >>= (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)  ∎
... | just f₁ | nothing | nothing | nothing =
  D t (p₁ >>= p₂)  ≈⟨ [ ○ - ◌ - ○ - ○ ] D-cong p₁≈p₃ >>= (λ x → ♭ (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)  ∎
... | just f₁ | nothing | nothing | just xs₄ =
  D t (p₁ >>= p₂)                                          ≅⟨ >>=-∣-lemma ⟩
  D t (p₁ >>= p₂) ∣ return⋆ [] >>= (λ x → D t (♭ (p₂ x)))  ≈⟨ [ ○ - ◌ - ○ - ○ ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) >>=
                                                                                (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)                                          ∎
... | just f₁ | nothing | just f₃ | nothing =
  D t (p₁ >>= p₂)  ≈⟨ [ ○ - ○ - ○ - ○ ] D-cong p₁≈p₃ >>= (λ x → ♭ (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)  ∎
... | just f₁ | nothing | just f₃ | just xs₄ =
  D t (p₁ >>= p₂)                                          ≅⟨ >>=-∣-lemma ⟩
  D t (p₁ >>= p₂) ∣ return⋆ [] >>= (λ x → D t (♭ (p₂ x)))  ≈⟨ [ ○ - ○ - ○ - ○ ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) >>=
                                                                                (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)                                          ∎
... | just f₁ | just xs₂ | nothing | nothing =
  D t (p₁ >>= p₂)                                          ≈⟨ [ ○ - ◌ - ○ - ○ ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) >>=
                                                                                (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄) ∣ return⋆ [] >>= (λ x → D t (♭ (p₄ x)))  ≅⟨ sym (>>=-∣-lemma {p = D t (p₃ >>= p₄)}) ⟩
  D t (p₃ >>= p₄)                                          ∎
... | just f₁ | just xs₂ | nothing | just xs₄ =
  D t (p₁ >>= p₂)  ≈⟨ [ ○ - ◌ - ○ - ○ ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                      [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) >>= (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)  ∎
... | just f₁ | just xs₂ | just f₃ | nothing =
  D t (p₁ >>= p₂)                                          ≈⟨ [ ○ - ○ - ○ - ○ ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                                                              [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) >>=
                                                                                (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄) ∣ return⋆ [] >>= (λ x → D t (♭ (p₄ x)))  ≅⟨ sym (>>=-∣-lemma {p = D t (p₃ >>= p₄)}) ⟩
  D t (p₃ >>= p₄)                                          ∎
... | just f₁ | just xs₂ | just f₃ | just xs₄ =
  D t (p₁ >>= p₂)  ≈⟨ [ ○ - ○ - ○ - ○ ] D-cong p₁≈p₃ >>= p₂≈p₄ ∣
                      [ ○ - ○ - ○ - ○ ] Return⋆.cong (same-bag/set p₁≈p₃) >>= (λ x → D-cong (p₂≈p₄ x)) ⟩
  D t (p₃ >>= p₄)  ∎

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
  sound′ p₁≈p₂ =
    same-bag/set p₁≈p₂ ∷ λ t → ♯ sound′ (D-cong p₁≈p₂)
