------------------------------------------------------------------------
-- Fixity and associativity
------------------------------------------------------------------------

module RecursiveDescent.Inductive.Mixfix.FA where

open import Data.Function
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

data Fixity : Set where
  prefx  : Fixity
  infx   : Fixity -- infix is a reserved word.
  postfx : Fixity

private
  pre≢in : prefx ≢ infx
  pre≢in ()

  pre≢post : prefx ≢ postfx
  pre≢post ()

  in≢post : infx ≢ postfx
  in≢post ()

_Fix-≟_ : Decidable (_≡_ {Fixity})
prefx  Fix-≟ prefx  = yes ≡-refl
prefx  Fix-≟ infx   = no pre≢in
prefx  Fix-≟ postfx = no pre≢post
infx   Fix-≟ prefx  = no (pre≢in ∘ ≡-sym)
infx   Fix-≟ infx   = yes ≡-refl
infx   Fix-≟ postfx = no in≢post
postfx Fix-≟ prefx  = no (pre≢post ∘ ≡-sym)
postfx Fix-≟ infx   = no (in≢post ∘ ≡-sym)
postfx Fix-≟ postfx = yes ≡-refl

data Associativity : Set where
  left  : Associativity
  right : Associativity
  non   : Associativity

private
  left≢right : left ≢ right
  left≢right ()

  left≢non : left ≢ non
  left≢non ()

  right≢non : right ≢ non
  right≢non ()

_Assoc-≟_ : Decidable (_≡_ {Associativity})
left  Assoc-≟ left  = yes ≡-refl
left  Assoc-≟ right = no left≢right
left  Assoc-≟ non   = no left≢non
right Assoc-≟ left  = no (left≢right ∘ ≡-sym)
right Assoc-≟ right = yes ≡-refl
right Assoc-≟ non   = no right≢non
non   Assoc-≟ left  = no (left≢non ∘ ≡-sym)
non   Assoc-≟ right = no (right≢non ∘ ≡-sym)
non   Assoc-≟ non   = yes ≡-refl

data FA : Set where
  prefx  : FA
  infx   : (assoc : Associativity) -> FA
  postfx : FA

fixity : FA -> Fixity
fixity prefx    = prefx
fixity (infx _) = infx
fixity postfx   = postfx

associativity : FA -> Associativity
associativity (infx a) = a
associativity _        = non

toFA : Fixity -> Associativity -> FA
toFA prefx  _ = prefx
toFA infx   a = infx a
toFA postfx _ = postfx

toFA-left-inverse : forall fa ->
                    toFA (fixity fa) (associativity fa) ≡ fa
toFA-left-inverse prefx    = ≡-refl
toFA-left-inverse (infx _) = ≡-refl
toFA-left-inverse postfx   = ≡-refl

toFA-cong : forall {fa₁ fa₂} ->
            fixity        fa₁ ≡ fixity        fa₂ ->
            associativity fa₁ ≡ associativity fa₂ ->
            fa₁ ≡ fa₂
toFA-cong {fa₁} {fa₂} fix-≡ assoc-≡ = begin
  fa₁                                    ≡⟨ ≡-sym (toFA-left-inverse fa₁) ⟩
  toFA (fixity fa₁) (associativity fa₁)  ≡⟨ ≡-cong₂ toFA fix-≡ assoc-≡ ⟩
  toFA (fixity fa₂) (associativity fa₂)  ≡⟨ toFA-left-inverse fa₂ ⟩
  fa₂                                    ∎

_≟_ : Decidable (_≡_ {FA})
fa₁ ≟ fa₂ with fixity        fa₁ Fix-≟   fixity        fa₂
             | associativity fa₁ Assoc-≟ associativity fa₂
fa₁ ≟ fa₂ | yes fix-≡ | yes assoc-≡ = yes (toFA-cong fix-≡ assoc-≡)
fa₁ ≟ fa₂ | no  fix-≢ | _           = no (fix-≢ ∘ ≡-cong fixity)
fa₁ ≟ fa₂ | _         | no assoc-≢  = no (assoc-≢ ∘
                                          ≡-cong associativity)
