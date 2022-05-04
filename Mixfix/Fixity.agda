------------------------------------------------------------------------
-- Fixity and associativity
------------------------------------------------------------------------

module Mixfix.Fixity where

open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Fin.Properties using (inj⇒≟)
open import Function.Base
open import Function.Bundles
open import Function.Consequences
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.PropositionalEquality.Properties as ≡

data Associativity : Set where
  left  : Associativity
  right : Associativity
  non   : Associativity

-- A combination of fixity and associativity. Only infix operators
-- have associativity.

-- Note that infix is a reserved word.

data Fixity : Set where
  prefx  : Fixity
  infx   : (assoc : Associativity) → Fixity
  postfx : Fixity
  closed : Fixity

Fixity-is-finite : Fixity ↪ Fin 6
Fixity-is-finite = mk↪ {to = to} {from = from} from-to
  where
  to : Fixity → Fin 6
  to prefx        = # 0
  to (infx left)  = # 1
  to (infx right) = # 2
  to (infx non)   = # 3
  to postfx       = # 4
  to closed       = # 5

  from : Fin 6 → Fixity
  from zero                                   = prefx
  from (suc zero)                             = infx left
  from (suc (suc zero))                       = infx right
  from (suc (suc (suc zero)))                 = infx non
  from (suc (suc (suc (suc zero))))           = postfx
  from (suc (suc (suc (suc (suc zero)))))     = closed
  from (suc (suc (suc (suc (suc (suc ()))))))

  from-to : ∀ f → from (to f) ≡ f
  from-to prefx        = refl
  from-to (infx left)  = refl
  from-to (infx right) = refl
  from-to (infx non)   = refl
  from-to postfx       = refl
  from-to closed       = refl

_≟_ : Decidable (_≡_ {A = Fixity})
_≟_ = inj⇒≟ injection
  where
  open RightInverse Fixity-is-finite

  injection : Fixity ↣ Fin 6
  injection = mk↣ $
    inverseʳ⇒injective (≡.setoid _) {f⁻¹ = from} from-cong inverseʳ
