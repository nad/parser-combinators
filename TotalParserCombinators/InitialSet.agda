------------------------------------------------------------------------
-- Lemmas about the initial set index
------------------------------------------------------------------------

module TotalParserCombinators.InitialSet where

open import Data.List
open import Data.List.Any as Any
open import Data.List.Any.Membership
open import Data.List.Any.Properties
open import Data.Product as Prod
open import Data.Sum
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; module Equivalent) renaming (_∘_ to _⟨∘⟩_)
open import Function.Inverse as Inv
  using (_⇿_) renaming (_∘_ to _⟪∘⟫_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
open import Relation.Binary.HeterogeneousEquality as H
  using (refl) renaming (_≅_ to _≅′_)

open Any.Membership-≡
open Inv.Inverse
private
  open module SetS {R : Set} = Setoid (Set-equality {R})
    using () renaming (_≈_ to _Set-≈_)
  open module BagS {R : Set} = Setoid (Bag-equality {R})
    using () renaming (_≈_ to _Bag-≈_)

import TotalParserCombinators.Applicative as ⊛
open import TotalParserCombinators.Coinduction
open import TotalParserCombinators.Parser
open import TotalParserCombinators.Semantics

------------------------------------------------------------------------
-- Sanity check: The initial set index is correctly defined

mutual

  complete : ∀ {Tok R xs x} {p : Parser Tok R xs} →
             x ∈ p · [] → x ∈ xs
  complete x∈p = complete′ x∈p refl

  private

    complete′ : ∀ {Tok R xs x s} {p : Parser Tok R xs} →
                x ∈ p · s → s ≡ [] → x ∈ xs
    complete′ return                                        refl = to return⇿          ⟨$⟩ refl
    complete′ (∣ˡ     x∈p₁)                                 refl = to ++⇿              ⟨$⟩ inj₁ (complete x∈p₁)
    complete′ (∣ʳ xs₁ x∈p₂)                                 refl = to (++⇿ {xs = xs₁}) ⟨$⟩ inj₂ (complete x∈p₂)
    complete′ (<$> x∈p)                                     refl = to map-∈⇿           ⟨$⟩ (_ , complete x∈p , refl)
    complete′ (_⊛_   {s₁ = []} {fs = fs}        f∈p₁ x∈p₂)  refl = to ⊛.⇿              ⟨$⟩ (_ , _ , complete f∈p₁ , complete x∈p₂ , refl)
    complete′ (_>>=_ {s₁ = []} {xs = _ ∷ _} {f} x∈p₁ y∈p₂x) refl = to (>>=-∈⇿ {f = f}) ⟨$⟩ (_ , complete x∈p₁ , complete y∈p₂x)
    complete′ (cast {xs₁≈xs₂ = xs₁≈xs₂} x∈p)                refl = to xs₁≈xs₂          ⟨$⟩ complete x∈p

    complete′ (_>>=_  {s₁ = []} {xs = []} x∈p₁ y∈p₂x) refl with complete x∈p₁
    ... | ()
    complete′ (_>>=!_ {s₁ = []}           x∈p₁ y∈p₂x) refl with complete y∈p₂x
    ... | ()

    complete′ token                     ()
    complete′ (_⊛_    {s₁ = _ ∷ _} _ _) ()
    complete′ (_>>=_  {s₁ = _ ∷ _} _ _) ()
    complete′ (_>>=!_ {s₁ = _ ∷ _} _ _) ()
    complete′ (nonempty _)              ()

mutual

  sound : ∀ {Tok R xs x} (p : Parser Tok R xs) →
          x ∈ xs → x ∈ p · []
  sound (return x)              (here refl) = return
  sound (_∣_ {xs₁ = xs₁} p₁ p₂) x∈xs with from (++⇿ {xs = xs₁}) ⟨$⟩ x∈xs
  ... | inj₁ x∈xs₁ = ∣ˡ     (sound p₁ x∈xs₁)
  ... | inj₂ x∈xs₂ = ∣ʳ xs₁ (sound p₂ x∈xs₂)
  sound (_<$>_ {xs = xs} f p) x∈xs with from (map-∈⇿ {xs = xs}) ⟨$⟩ x∈xs
  ... | (y , y∈xs , refl) = <$> sound p y∈xs
  sound (_⊛_ {fs = fs} {x ∷ xs} ⟨ p₁ ⟩ p₂) y∈ys
    with from (⊛.⇿ {fs = fs} {xs = x ∷ xs}) ⟨$⟩ y∈ys
  sound (_⊛_ {xs = x ∷ xs} ⟨ p₁ ⟩ ⟪ p₂ ⟫)  y∈ys | (f′ , x′ , ()    , x′∈x∷xs , refl)
  sound (_⊛_ {xs = x ∷ xs} ⟨ p₁ ⟩ ⟨ p₂ ⟩)  y∈ys | (f′ , x′ , f′∈fs , x′∈x∷xs , refl) =
    sound p₁ f′∈fs ⊛ sound p₂ x′∈x∷xs
  sound (_>>=_ {xs = zs} {f} p₁ p₂) y∈ys
    with from (>>=-∈⇿ {xs = zs} {f = f}) ⟨$⟩ y∈ys
  ... | (x , x∈zs , y∈fx) =
    _>>=_ {f = f} (sound p₁ x∈zs) (sound′ (p₂ x) x∈zs y∈fx)
  sound (cast xs₁≈xs₂ p) x∈xs = cast (sound p (from xs₁≈xs₂ ⟨$⟩ x∈xs))

  sound (return _)   (there ())
  sound fail         ()
  sound token        ()
  sound (⟪ _ ⟫ ⊛ _)  ()
  sound (_ >>=! _)   ()
  sound (nonempty _) ()

  private

    sound′ : ∀ {Tok R₁ R₂ x y xs} {zs : List R₁}
               (p : ∞? (Parser Tok R₂ xs) zs) →
               x ∈ zs → y ∈ xs → y ∈ ♭? p · []
    sound′ ⟨ p ⟩ _  = sound p
    sound′ ⟪ p ⟫ ()

mutual

  sound∘complete : ∀ {Tok R xs x} {p : Parser Tok R xs}
                   (x∈p : x ∈ p · []) →
                   sound p (complete x∈p) ≡ x∈p
  sound∘complete x∈p = H.≅-to-≡ (sound∘complete′ x∈p refl)

  private

    sound∘complete′ : ∀ {Tok R xs x s} {p : Parser Tok R xs}
                      (x∈p : x ∈ p · s) (s≡[] : s ≡ []) →
                      sound p (complete′ x∈p s≡[]) ≅′ x∈p
    sound∘complete′ return                            refl = refl
    sound∘complete′ (∣ˡ {xs₁ = xs₁} {xs₂ = xs₂} x∈p₁) refl rewrite left-inverse-of (++⇿ {xs = xs₁} {ys = xs₂}) (inj₁ (complete x∈p₁)) =
                                                           H.cong ((_ → _ ∈ _ · _) ∶ ∣ˡ)     (sound∘complete′ x∈p₁ refl)
    sound∘complete′ (∣ʳ xs₁ x∈p₂)                     refl rewrite left-inverse-of (++⇿ {xs = xs₁}) (inj₂ (complete x∈p₂)) =
                                                           H.cong ((_ → _ ∈ _ · _) ∶ ∣ʳ xs₁) (sound∘complete′ x∈p₂ refl)
    sound∘complete′ (<$>_ {f = f} x∈p)                refl rewrite left-inverse-of (map-∈⇿ {f = f}) (_ , complete x∈p , refl) =
                                                           H.cong ((_ → _ ∈ _ · _) ∶ <$>_) (sound∘complete′ x∈p refl)
    sound∘complete′ (_⊛_ {s₁ = []} {fs = fs} {xs = x ∷ xs} {p₁ = ⟨ p₁ ⟩} f∈p₁ x∈p₂) refl
      with complete f∈p₁ | complete x∈p₂
      | from (⊛.⇿ {fs = fs} {xs = x ∷ xs}) ⟨$⟩
          (to ⊛.⇿ ⟨$⟩ (_ , _ , complete f∈p₁ , complete x∈p₂ , refl))
      | left-inverse-of ⊛.⇿ (_ , _ , complete f∈p₁ , complete x∈p₂ , refl)
      | sound∘complete f∈p₁ | sound∘complete x∈p₂
    sound∘complete′ (_⊛_ {s₁ = []} {fs = []}     {xs = _ ∷ _}  {p₁ = ⟨ _  ⟩} {p₂ = ⟪ _  ⟫} _ _) refl | () | _ | _ | _ | _ | _
    sound∘complete′ (_⊛_ {s₁ = []} {fs = f ∷ fs} {xs = x ∷ xs} {p₁ = ⟨ p₁ ⟩} {p₂ = ⟨ p₂ ⟩}
                             .(sound p₁ ∈f∷fs) .(sound p₂ ∈x∷xs)) refl
      | ∈f∷fs | ∈x∷xs | ._ | refl | refl | refl = refl
    sound∘complete′ (_>>=_ {x = x} {y = y} {s₁ = []} {xs = _ ∷ _} {f} {p₁ = p₁} {p₂ = p₂} x∈p₁ y∈p₂x) refl
      rewrite left-inverse-of (>>=-∈⇿ {f = f}) (_ , complete x∈p₁ , complete y∈p₂x)
         with sound p₁ (complete x∈p₁)
            | sound∘complete x∈p₁
            | sound′ (p₂ x) (complete x∈p₁) (complete y∈p₂x)
            | helper (p₂ x) (complete x∈p₁) y∈p₂x
         where
         helper : ∀ {Tok R₁ R₂ x y ys} {xs : List R₁}
                  (p : ∞? (Parser Tok R₂ ys) xs) →
                  (x∈xs : x ∈ xs) (y∈p : y ∈ ♭? p · []) →
                  sound′ p x∈xs (complete y∈p) ≡ y∈p
         helper ⟪ p ⟫ () _
         helper ⟨ p ⟩ _  y∈p = sound∘complete y∈p
    ... | ._ | refl | ._ | refl = refl
    sound∘complete′ (cast {xs₁≈xs₂ = xs₁≈xs₂} x∈p)             refl with complete x∈p | sound∘complete x∈p
    sound∘complete′ (cast {xs₁≈xs₂ = xs₁≈xs₂} .(sound _ x∈xs)) refl | x∈xs | refl
      rewrite left-inverse-of xs₁≈xs₂ x∈xs = refl

    sound∘complete′ (_⊛_    {s₁ = []} {xs = []} _    x∈p₂)  refl with complete x∈p₂
    ... | ()
    sound∘complete′ (_>>=_  {s₁ = []} {xs = []} x∈p₁ y∈p₂x) refl with complete x∈p₁
    ... | ()
    sound∘complete′ (_>>=!_ {s₁ = []}           x∈p₁ y∈p₂x) refl with complete y∈p₂x
    ... | ()

    sound∘complete′ token                     ()
    sound∘complete′ (_⊛_    {s₁ = _ ∷ _} _ _) ()
    sound∘complete′ (_>>=_  {s₁ = _ ∷ _} _ _) ()
    sound∘complete′ (_>>=!_ {s₁ = _ ∷ _} _ _) ()
    sound∘complete′ (nonempty _)              ()

complete∘sound : ∀ {Tok R xs x}
                 (p : Parser Tok R xs) (x∈p : x ∈ xs) →
                 complete (sound p x∈p) ≡ x∈p
complete∘sound (return x)              (here refl) = refl
complete∘sound (_∣_ {xs₁ = xs₁} p₁ p₂) x∈xs
  with from             (++⇿ {xs = xs₁}) ⟨$⟩ x∈xs
     | right-inverse-of (++⇿ {xs = xs₁})     x∈xs
complete∘sound (_∣_ {xs₁ = xs₁} p₁ p₂) .(to ++⇿              ⟨$⟩ inj₁ x∈xs₁) | inj₁ x∈xs₁ | refl =
  cong (_⟨$⟩_ (to ++⇿)              ∘ inj₁) $ complete∘sound p₁ x∈xs₁
complete∘sound (_∣_ {xs₁ = xs₁} p₁ p₂) .(to (++⇿ {xs = xs₁}) ⟨$⟩ inj₂ x∈xs₂) | inj₂ x∈xs₂ | refl =
  cong (_⟨$⟩_ (to (++⇿ {xs = xs₁})) ∘ inj₂) $ complete∘sound p₂ x∈xs₂
complete∘sound (_<$>_ {xs = xs} f p) x∈xs
  with            from (map-∈⇿ {xs = xs}) ⟨$⟩ x∈xs
     | right-inverse-of map-∈⇿                x∈xs
complete∘sound (_<$>_ {xs = xs} f p) .(to map-∈⇿ ⟨$⟩ (y , y∈xs , refl)) | (y , y∈xs , refl) | refl =
  cong (λ y∈ → to map-∈⇿ ⟨$⟩ (y , y∈ , refl)) $ complete∘sound p y∈xs
complete∘sound (_⊛_ {fs = fs} {x ∷ xs} ⟨ p₁ ⟩ p₂) y∈ys
  with from             (⊛.⇿ {fs = fs} {xs = x ∷ xs}) ⟨$⟩ y∈ys
     | right-inverse-of (⊛.⇿ {fs = fs} {xs = x ∷ xs})     y∈ys
complete∘sound (_⊛_ {xs = x ∷ xs} ⟨ p₁ ⟩ ⟪ p₂ ⟫)
               y∈ys                                             | (f′ , x′ , ()    , x′∈x∷xs , refl) | _
complete∘sound (_⊛_ {xs = x ∷ xs} ⟨ p₁ ⟩ ⟨ p₂ ⟩)
               .(to ⊛.⇿ ⟨$⟩ (f′ , x′ , f′∈fs , x′∈x∷xs , refl)) | (f′ , x′ , f′∈fs , x′∈x∷xs , refl) | refl =
  cong₂ (λ f′∈ x′∈ → to ⊛.⇿ ⟨$⟩ (f′ , x′ , f′∈ , x′∈ , refl))
        (complete∘sound p₁ f′∈fs)
        (complete∘sound p₂ x′∈x∷xs)
complete∘sound (_>>=_ {xs = zs}     {f} p₁ p₂) y∈ys
  with from             (>>=-∈⇿ {xs = zs} {f = f}) ⟨$⟩ y∈ys
     | right-inverse-of (>>=-∈⇿ {xs = zs} {f = f})     y∈ys
complete∘sound (_>>=_ {xs = []}     {f} p₁ p₂) ._                                             | (x , ()     , y∈fx) | refl
complete∘sound (_>>=_ {xs = z ∷ zs} {f} p₁ p₂) .(to (>>=-∈⇿ {f = f}) ⟨$⟩ (x , x∈z∷zs , y∈fx)) | (x , x∈z∷zs , y∈fx) | refl =
  cong₂ (λ x∈ y∈ → to (>>=-∈⇿ {f = f}) ⟨$⟩ (x , x∈ , y∈))
        (complete∘sound p₁ x∈z∷zs)
        (helper (p₂ x) x∈z∷zs y∈fx)
  where
  helper : ∀ {Tok R₁ R₂ x y xs z} {zs : List R₁}
           (p : ∞? (Parser Tok R₂ xs) (z ∷ zs))
           (x∈z∷zs : x ∈ z ∷ zs) (y∈xs : y ∈ xs) →
           complete (sound′ p x∈z∷zs y∈xs) ≡ y∈xs
  helper ⟨ p ⟩ x∈z∷zs y∈xs = complete∘sound p y∈xs
complete∘sound (cast xs₁≈xs₂ p) x∈xs
  rewrite complete∘sound p (from xs₁≈xs₂ ⟨$⟩ x∈xs) =
    right-inverse-of xs₁≈xs₂ x∈xs

complete∘sound (return _)   (there ())
complete∘sound fail         ()
complete∘sound token        ()
complete∘sound (⟪ _ ⟫ ⊛ _)  ()
complete∘sound (_ >>=! _)   ()
complete∘sound (nonempty _) ()

correct : ∀ {Tok R xs x} {p : Parser Tok R xs} → x ∈ p · [] ⇿ x ∈ xs
correct {p = p} = record
  { to         = P.→-to-⟶ complete
  ; from       = P.→-to-⟶ $ sound p
  ; inverse-of = record
    { left-inverse-of  = sound∘complete
    ; right-inverse-of = complete∘sound p
    }
  }

------------------------------------------------------------------------
-- Equal parsers have equal initial sets

same-set : ∀ {Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≈ p₂ → xs₁ Set-≈ xs₂
same-set p₁≈p₂ =
  equivalent correct ⟨∘⟩
  p₁≈p₂ ⟨∘⟩
  equivalent (Inv.sym correct)

same-bag : ∀ {Tok R xs₁ xs₂}
             {p₁ : Parser Tok R xs₁} {p₂ : Parser Tok R xs₂} →
           p₁ ≅ p₂ → xs₁ Bag-≈ xs₂
same-bag p₁≅p₂ = correct ⟪∘⟫ p₁≅p₂ ⟪∘⟫ Inv.sym correct
