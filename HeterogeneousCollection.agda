module HeterogeneousCollection (Index : Set) where

data Ctxt : Set where
  ε   : Ctxt
  _▻_ : Ctxt -> Index -> Ctxt

data Label : Ctxt -> Index -> Set where
  lz : forall {Γ i}    -> Label (Γ ▻ i) i
  ls : forall {Γ i i'} -> Label Γ i -> Label (Γ ▻ i') i

data Coll (T : Index -> Set) : Ctxt -> Set where
  ∅   : Coll T ε
  _▷_ : forall {Γ i} -> Coll T Γ -> T i -> Coll T (Γ ▻ i)

lookup :  forall {Γ i} {T : Index -> Set}
       -> Label Γ i -> Coll T Γ -> T i
lookup ()     ∅
lookup lz     (ρ ▷ p) = p
lookup (ls l) (ρ ▷ p) = lookup l ρ
