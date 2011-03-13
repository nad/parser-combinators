------------------------------------------------------------------------
-- Lemmas about the initial bag index
------------------------------------------------------------------------

module TotalParserCombinators.InitialBag where

open import Category.Monad
open import Data.List as List
open import Data.List.Any as Any
open import Data.List.Any.Membership as M hiding (⊛-∈↔)
open import Data.List.Any.Properties
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_)
import Function.Related as Related
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H
  using (refl) renaming (_≅_ to _≅′_)

open Any.Membership-≡ using (_∈_) renaming (_≈[_]_ to _List-≈[_]_)
open Inv.Inverse
open RawMonadPlus List.monadPlus using () renaming (_⊛_ to _⊛′_)

open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- Optimisation

private

  abstract

    ⊛-∈↔ : ∀ {A B : Set} (fs : List (A → B)) {xs y} →
           (∃₂ λ f x → f ∈ fs × x ∈ xs × y ≡ f x) ↔ y ∈ fs ⊛′ xs
    ⊛-∈↔ = M.⊛-∈↔

------------------------------------------------------------------------
-- Sanity check: The initial set index is correctly defined

mutual

  complete : ∀ {Tok R xs x} {p : Parser Tok R xs} →
             x ∈ p · [] → x ∈ xs
  complete x∈p = complete′ x∈p refl

  private

    complete′ : ∀ {Tok R xs x s} {p : Parser Tok R xs} →
                x ∈ p · s → s ≡ [] → x ∈ xs
    complete′ return                                                    refl = to return↔            ⟨$⟩ refl
    complete′ (∣-left      x∈p₁)                                        refl = to ++↔                ⟨$⟩ inj₁ (complete x∈p₁)
    complete′ (∣-right xs₁ x∈p₂)                                        refl = to (++↔ {P = _≡_ _}
                                                                                       {xs = xs₁})   ⟨$⟩ inj₂ (complete x∈p₂)
    complete′ (<$> x∈p)                                                 refl = to map-∈↔             ⟨$⟩ (_ , complete x∈p , refl)
    complete′ (_⊛_   {s₁ = []} {xs = just _}                f∈p₁ x∈p₂)  refl = to (⊛-∈↔ _)           ⟨$⟩ (_ , _ , complete f∈p₁
                                                                                                                , complete x∈p₂ , refl)
    complete′ (_>>=_ {s₁ = []} {xs = just xs} {f = just _}  x∈p₁ y∈p₂x) refl = to (>>=-∈↔ {xs = xs}) ⟨$⟩ (_ , complete x∈p₁
                                                                                                            , complete y∈p₂x)
    complete′ (cast {xs₁≈xs₂ = xs₁≈xs₂} x∈p)                            refl = to xs₁≈xs₂            ⟨$⟩ complete x∈p

    complete′ (_⊛_   {s₁ = []} {xs = nothing}               f∈p₁ x∈p₂)  refl with complete x∈p₂
    ... | ()
    complete′ (_>>=_ {s₁ = []} {xs = nothing}               x∈p₁ y∈p₂x) refl with complete x∈p₁
    ... | ()
    complete′ (_>>=_ {s₁ = []} {xs = just _}  {f = nothing} x∈p₁ y∈p₂x) refl with complete y∈p₂x
    ... | ()

    complete′ token                     ()
    complete′ (_⊛_    {s₁ = _ ∷ _} _ _) ()
    complete′ (_>>=_  {s₁ = _ ∷ _} _ _) ()
    complete′ (nonempty _)              ()

mutual

  sound : ∀ {Tok R xs x} (p : Parser Tok R xs) →
          x ∈ xs → x ∈ p · []
  sound (return x)              (here refl) = return
  sound (_∣_ {xs₁ = xs₁} p₁ p₂) x∈xs with from (++↔ {P = _≡_ _} {xs = xs₁}) ⟨$⟩ x∈xs
  ... | inj₁ x∈xs₁ = ∣-left      (sound p₁ x∈xs₁)
  ... | inj₂ x∈xs₂ = ∣-right xs₁ (sound p₂ x∈xs₂)
  sound (f <$> p) x∈xs with from (map-∈↔ {f = f}) ⟨$⟩ x∈xs
  ... | (y , y∈xs , refl) = <$> sound p y∈xs
  sound (_⊛_ {fs = fs} {just xs} p₁ p₂) y∈ys
    with from (⊛-∈↔ (flatten fs) {xs = xs}) ⟨$⟩ y∈ys
  sound (_⊛_ {fs = nothing} {just xs} p₁ p₂)  y∈ys | (f′ , x′ , ()    , x′∈xs , refl)
  sound (_⊛_ {fs = just fs} {just xs} p₁ p₂)  y∈ys | (f′ , x′ , f′∈fs , x′∈xs , refl) =
    _⊛_ {fs = ○} {xs = ○} (sound p₁ f′∈fs) (sound p₂ x′∈xs)
  sound (_>>=_ {xs = zs} {f = just f} p₁ p₂) y∈ys
    with from (>>=-∈↔ {xs = flatten zs} {f = f}) ⟨$⟩ y∈ys
  ... | (x , x∈zs , y∈fx) =
    _>>=_ {xs = zs} {f = just f} (sound p₁ x∈zs) (sound′ (p₂ x) x∈zs y∈fx)
  sound (cast xs₁≈xs₂ p) x∈xs = cast (sound p (from xs₁≈xs₂ ⟨$⟩ x∈xs))

  sound (return _)                 (there ())
  sound fail                       ()
  sound token                      ()
  sound (_⊛_   {xs = nothing} _ _) ()
  sound (_>>=_ {f  = nothing} _ _) ()
  sound (nonempty _)               ()

  private

    sound′ : ∀ {Tok R₁ R₂ x y xs} {zs : Maybe (List R₁)}
               (p : ∞⟨ zs ⟩Parser Tok R₂ xs) →
               x ∈ flatten zs → y ∈ xs → y ∈ ♭? p · []
    sound′ {zs = just _}  p _  = sound p
    sound′ {zs = nothing} p ()

mutual

  sound∘complete : ∀ {Tok R xs x} {p : Parser Tok R xs}
                   (x∈p : x ∈ p · []) →
                   sound p (complete x∈p) ≡ x∈p
  sound∘complete x∈p = H.≅-to-≡ (sound∘complete′ x∈p refl)

  private

    sound∘complete′ : ∀ {Tok R xs x s} {p : Parser Tok R xs}
                      (x∈p : x ∈ p · s) (s≡[] : s ≡ []) →
                      sound p (complete′ x∈p s≡[]) ≅′ x∈p
    sound∘complete′ return                                refl = refl
    sound∘complete′ (∣-left {xs₁ = xs₁} {xs₂ = xs₂} x∈p₁) refl
      rewrite left-inverse-of (++↔ {P = _≡_ _} {xs = xs₁} {ys = xs₂}) (inj₁ (complete x∈p₁)) =
        H.cong (∣-left ∶ (_ → _ ∈ _ · _)) (sound∘complete′ x∈p₁ refl)
    sound∘complete′ (∣-right xs₁ x∈p₂) refl
      rewrite left-inverse-of (++↔ {P = _≡_ _} {xs = xs₁}) (inj₂ (complete x∈p₂)) =
        H.cong (∣-right xs₁ ∶ (_ → _ ∈ _ · _)) (sound∘complete′ x∈p₂ refl)
    sound∘complete′ (<$>_ {f = f} x∈p) refl
      rewrite left-inverse-of (map-∈↔ {f = f}) (_ , complete x∈p , refl) =
        H.cong (<$>_ ∶ (_ → _ ∈ _ · _)) (sound∘complete′ x∈p refl)
    sound∘complete′ (_⊛_ {s₁ = []} {fs = fs} {xs = just xs} f∈p₁ x∈p₂) refl
      with complete f∈p₁ | complete x∈p₂
      | from inv ⟨$⟩ (to inv ⟨$⟩ (_ , _ , complete f∈p₁ , complete x∈p₂ , refl))
      | left-inverse-of inv (_ , _ , complete f∈p₁ , complete x∈p₂ , refl)
      | sound∘complete f∈p₁ | sound∘complete x∈p₂
      where inv = ⊛-∈↔ (flatten fs) {xs = xs}
    sound∘complete′ (_⊛_ {s₁ = []} {fs = nothing} {xs = just xs} _ _) refl | () | _ | _ | _ | _ | _
    sound∘complete′ (_⊛_ {s₁ = []} {fs = just fs} {xs = just xs} {p₁ = p₁} {p₂ = p₂}
                         .(sound p₁ ∈fs) .(sound p₂ ∈xs)) refl
      | ∈fs | ∈xs | ._ | refl | refl | refl = refl
    sound∘complete′ (_>>=_ {x = x} {y = y} {s₁ = []} {xs = just _} {f = just f} {p₁ = p₁} {p₂ = p₂} x∈p₁ y∈p₂x) refl
      rewrite left-inverse-of (>>=-∈↔ {f = f}) (_ , complete x∈p₁ , complete y∈p₂x)
         with sound p₁ (complete x∈p₁)
            | sound∘complete x∈p₁
            | sound′ (p₂ x) (complete x∈p₁) (complete y∈p₂x)
            | helper (p₂ x) (complete x∈p₁) y∈p₂x
         where
         helper : ∀ {Tok R₁ R₂ x y ys} {xs : Maybe (List R₁)}
                  (p : ∞⟨ xs ⟩Parser Tok R₂ ys) →
                  (x∈xs : x ∈ flatten xs) (y∈p : y ∈ ♭? p · []) →
                  sound′ p x∈xs (complete y∈p) ≡ y∈p
         helper {xs = nothing} p () _
         helper {xs = just _}  p _  y∈p = sound∘complete y∈p
    ... | ._ | refl | ._ | refl = refl
    sound∘complete′ (cast {xs₁≈xs₂ = xs₁≈xs₂} x∈p)             refl with complete x∈p | sound∘complete x∈p
    sound∘complete′ (cast {xs₁≈xs₂ = xs₁≈xs₂} .(sound _ x∈xs)) refl | x∈xs | refl
      rewrite left-inverse-of xs₁≈xs₂ x∈xs = refl

    sound∘complete′ (_⊛_    {s₁ = []} {xs = nothing}              _    x∈p₂)  refl with complete x∈p₂
    ... | ()
    sound∘complete′ (_>>=_  {s₁ = []} {xs = nothing}              x∈p₁ y∈p₂x) refl with complete x∈p₁
    ... | ()
    sound∘complete′ (_>>=_  {s₁ = []} {xs = just _} {f = nothing} x∈p₁ y∈p₂x) refl with complete y∈p₂x
    ... | ()

    sound∘complete′ token                     ()
    sound∘complete′ (_⊛_    {s₁ = _ ∷ _} _ _) ()
    sound∘complete′ (_>>=_  {s₁ = _ ∷ _} _ _) ()
    sound∘complete′ (nonempty _)              ()

complete∘sound : ∀ {Tok R xs x}
                 (p : Parser Tok R xs) (x∈p : x ∈ xs) →
                 complete (sound p x∈p) ≡ x∈p
complete∘sound (return x)              (here refl) = refl
complete∘sound (_∣_ {xs₁ = xs₁} p₁ p₂) x∈xs
  with from             (++↔ {P = _≡_ _} {xs = xs₁}) ⟨$⟩ x∈xs
     | right-inverse-of (++↔ {P = _≡_ _} {xs = xs₁})     x∈xs
complete∘sound (_∣_ {xs₁ = xs₁} p₁ p₂) .(to ++↔                          ⟨$⟩ inj₁ x∈xs₁) | inj₁ x∈xs₁ | refl =
  P.cong (_⟨$⟩_ (to ++↔)                          ∘ inj₁) $ complete∘sound p₁ x∈xs₁
complete∘sound (_∣_ {xs₁ = xs₁} p₁ p₂) .(to (++↔ {P = _≡_ _} {xs = xs₁}) ⟨$⟩ inj₂ x∈xs₂) | inj₂ x∈xs₂ | refl =
  P.cong (_⟨$⟩_ (to (++↔ {P = _≡_ _} {xs = xs₁})) ∘ inj₂) $ complete∘sound p₂ x∈xs₂
complete∘sound (f <$> p) x∈xs
  with             from (map-∈↔ {f = f}) ⟨$⟩ x∈xs
     | right-inverse-of (map-∈↔ {f = f})     x∈xs
complete∘sound (f <$> p) .(to (map-∈↔ {f = f}) ⟨$⟩ (y , y∈xs , refl)) | (y , y∈xs , refl) | refl =
  P.cong (λ y∈ → to map-∈↔ ⟨$⟩ (y , y∈ , refl)) $ complete∘sound p y∈xs
complete∘sound (_⊛_ {fs = fs} {just xs} p₁ p₂) y∈ys
  with from             (⊛-∈↔ (flatten fs) {xs = xs}) ⟨$⟩ y∈ys
     | right-inverse-of (⊛-∈↔ (flatten fs) {xs = xs})     y∈ys
complete∘sound (_⊛_ {fs = nothing} {xs = just xs} p₁ p₂)
               y∈ys                                                | (f′ , x′ , ()    , x′∈xs , refl) | _
complete∘sound (_⊛_ {fs = just fs} {xs = just xs} p₁ p₂)
               .(to (⊛-∈↔ _) ⟨$⟩ (f′ , x′ , f′∈fs , x′∈xs , refl)) | (f′ , x′ , f′∈fs , x′∈xs , refl) | refl =
  P.cong₂ (λ f′∈ x′∈ → to (⊛-∈↔ _) ⟨$⟩ (f′ , x′ , f′∈ , x′∈ , refl))
          (complete∘sound p₁ f′∈fs)
          (complete∘sound p₂ x′∈xs)
complete∘sound (_>>=_ {xs = zs}      {just f} p₁ p₂) y∈ys
  with from             (>>=-∈↔ {xs = flatten zs} {f = f}) ⟨$⟩ y∈ys
     | right-inverse-of (>>=-∈↔ {xs = flatten zs} {f = f})     y∈ys
complete∘sound (_>>=_ {xs = nothing} {just f} p₁ p₂) ._                                           | (x , ()   , y∈fx) | refl
complete∘sound (_>>=_ {xs = just zs} {just f} p₁ p₂) .(to (>>=-∈↔ {f = f}) ⟨$⟩ (x , x∈zs , y∈fx)) | (x , x∈zs , y∈fx) | refl =
  P.cong₂ (λ x∈ y∈ → to (>>=-∈↔ {f = f}) ⟨$⟩ (x , x∈ , y∈))
          (complete∘sound p₁ x∈zs)
          (complete∘sound (p₂ x) y∈fx)
complete∘sound (cast xs₁≈xs₂ p) x∈xs
  rewrite complete∘sound p (from xs₁≈xs₂ ⟨$⟩ x∈xs) =
    right-inverse-of xs₁≈xs₂ x∈xs

complete∘sound (return _)                 (there ())
complete∘sound fail                       ()
complete∘sound token                      ()
complete∘sound (_⊛_   {xs = nothing} _ _) ()
complete∘sound (_>>=_ {f  = nothing} _ _) ()
complete∘sound (nonempty _)               ()

correct : ∀ {Tok R xs x} {p : Parser Tok R xs} → x ∈ p · [] ↔ x ∈ xs
correct {p = p} = record
  { to         = P.→-to-⟶ complete
  ; from       = P.→-to-⟶ $ sound p
  ; inverse-of = record
    { left-inverse-of  = sound∘complete
    ; right-inverse-of = complete∘sound p
    }
  }

------------------------------------------------------------------------
-- Equal parsers have equal initial bags/sets

cong : ∀ {k Tok R xs₁ xs₂}
         {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
       p₁ ≈[ k ] p₂ → initial-bag p₁ List-≈[ k ] initial-bag p₂
cong {xs₁ = xs₁} {xs₂} {p₁} {p₂} p₁≈p₂ {x} =
  (x ∈ xs₁)    ↔⟨ sym correct ⟩
  x ∈ p₁ · []  ≈⟨ p₁≈p₂ ⟩
  x ∈ p₂ · []  ↔⟨ correct ⟩
  (x ∈ xs₂)    ∎
  where open Related.EquationalReasoning
