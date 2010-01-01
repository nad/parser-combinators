------------------------------------------------------------------------
-- Fixity and associativity
------------------------------------------------------------------------

module Mixfix.Fixity where

open import Data.Fin using (Fin; zero; suc; #_)
open import Data.Fin.Props using (eq?)
open import Function.LeftInverse
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as Eq

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

Fixity-is-finite : LeftInverse (Eq.setoid Fixity) (Eq.setoid (Fin 6))
Fixity-is-finite = record
  { from            = Eq.→-to-⟶ from
  ; to              = Eq.→-to-⟶ to
  ; left-inverse-of = left-inverse-of
  }
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

  left-inverse-of : Eq.→-to-⟶ from LeftInverseOf Eq.→-to-⟶ to
  left-inverse-of prefx        = refl
  left-inverse-of (infx left)  = refl
  left-inverse-of (infx right) = refl
  left-inverse-of (infx non)   = refl
  left-inverse-of postfx       = refl
  left-inverse-of closed       = refl

_≟_ : Decidable (_≡_ {A = Fixity})
_≟_ = eq? injection
  where open LeftInverse Fixity-is-finite
