------------------------------------------------------------------------
-- Parser monad
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.OrderMorphism
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Props.StrictTotalOrder as STOProps
open import Data.Product

module StructurallyRecursiveDescentParsing.Memoised.Monad

  -- Input string positions.

  {Position : Set} {_<P_ : Rel Position}
  (posOrdered : IsStrictTotalOrder _≡_ _<P_)

  -- Input strings.

  (Input : Position -> Set)

  -- In order to be able to store results in a memo table (and avoid
  -- having to lift the table code to Set1) the result types have to
  -- come from the following universe:

  {Result : Set} (⟦_⟧ : Result -> Set)

  -- Memoisation keys. These keys must uniquely identify the
  -- computation that they are associated with, when paired up with
  -- the current input string position.

  {Key : let PosPoset = STOProps.poset
                          (record { carrier = _ ; _≈_ = _; _<_ = _
                                  ; isStrictTotalOrder = posOrdered })
             MonoFun = PosPoset ⇒-Poset PosPoset in
         MonoFun -> Result -> Set}
  {_≈_ _<_ : Rel (∃₂ Key)}
  (keyOrdered : IsStrictTotalOrder _≈_ _<_)

  -- Furthermore the underlying equality needs to be strong enough.

  (funsEqual    : _≈_ =[ proj₁ ]⇒ _≡_)
  (resultsEqual : _≈_ =[ (\rfk -> proj₁ (proj₂ rfk)) ]⇒ _≡_)

  where

open _⇒-Poset_
open STOProps (record { carrier = _ ; _≈_ = _; _<_ = _
                      ; isStrictTotalOrder = posOrdered })

import Data.AVL.IndexedMap as Map renaming (Map to MemoTable)
open import Category.Monad
open import Category.Monad.State
import Data.List as List; open List using (List)
open import Data.Function
open import Data.Maybe
open import Data.Unit
open import Relation.Binary.Product.StrictLex
open import Relation.Binary.Product.Pointwise
import Relation.Binary.On as On

------------------------------------------------------------------------
-- Monotone functions

MonoFun : Set
MonoFun = poset ⇒-Poset poset

------------------------------------------------------------------------
-- Memo table keys and values

-- Indices and keys used by the memo table.

Index : Set
Index = Position × MonoFun × Result

data MemoTableKey : Index -> Set where
  key : forall {f r} (key : Key f r) pos -> MemoTableKey (pos , f , r)

-- Input strings of a certain maximum length.

record Input≤ (bnd : Position) : Set where
  field
    position : Position
    bounded  : position ≤ bnd
    string   : Input position

open Input≤ public

_isBounded∶_ : forall {bnd pos} -> Input pos -> pos ≤ bnd -> Input≤ bnd
xs isBounded∶ le = record { position = _; bounded = le; string = xs }

-- Memo table values.

Value : Index -> Set
Value (pos , f , r) = List (⟦ r ⟧ × Input≤ (fun f pos))

------------------------------------------------------------------------
-- Parser monad

-- The parser monad is instantiated with the memo table at the end of
-- the file in order to reduce the time required to type check it.

private
 module Dummy
        (MemoTable : Set)
        (empty  : MemoTable)
        (insert : forall {i} ->
                  MemoTableKey i -> Value i -> MemoTable -> MemoTable)
        (lookup : forall {i} ->
                  MemoTableKey i -> MemoTable -> Maybe (Value i))
        where

  -- The parser monad is built upon a list monad, for backtracking, and
  -- two state monads. One of the state monads stores a memo table, and
  -- is unaffected by backtracking. The other state monad, which /is/
  -- affected by backtracking, stores the remaining input string.

  -- The memo table state monad.

  module MemoState = RawMonadState (StateMonadState MemoTable)

  -- The list monad.

  module List = RawMonadPlus List.ListMonadPlus

  -- The inner monad (memo table plus list).

  module IM where

    Inner : Set -> Set
    Inner R = State MemoTable (List R)

    InnerMonadPlus : RawMonadPlus Inner
    InnerMonadPlus = record
      { monadZero = record
        { monad = record
          { return = \x -> return (List.return x)
          ; _>>=_  = \m f -> List.concat <$> (List.mapM monad f =<< m)
          }
        ; ∅ = return List.∅
        }
      ; _∣_ = \m₁ m₂ -> List._∣_ <$> m₁ ⊛ m₂
      }
      where open MemoState

    InnerMonadState : RawMonadState MemoTable Inner
    InnerMonadState = record
      { monad = RawMonadPlus.monad InnerMonadPlus
      ; get   = List.return <$> get
      ; put   = \s -> List.return <$> put s
      }
      where open MemoState

    open RawMonadPlus  InnerMonadPlus  public
    open RawMonadState InnerMonadState public
      using (get; put; modify)

  -- The complete parser monad.

  module PM where

    infixr 5 _∣_
    infixl 1 _>>=_ _>>_
    infixr 1 _=<<_

    -- Parameters:
    -- • bnd: Upper bound of the length of the input.
    -- • f:   The actual length of the output is bounded by
    --        f (actual length of the input).
    -- • A:   Result type.

    data P (bnd : Position) (f : MonoFun) (A : Set) : Set where
      pm : (im : (inp : Input≤ bnd) ->
                 IM.Inner (A × Input≤ (fun f (position inp)))) ->
           P bnd f A

    private

      unPM : forall {bnd f A} ->
             P bnd f A -> (inp : Input≤ bnd) ->
             IM.Inner (A × Input≤ (fun f (position inp)))
      unPM (pm m) = m

    -- Memoises the computation, assuming that the key is sufficiently
    -- unique.

    memoise : forall {bnd f r} ->
              Key f r -> P bnd f ⟦ r ⟧ -> P bnd f ⟦ r ⟧
    memoise {bnd} {f} {r} k (pm p) = pm helper₁
      where
      helper₁ : (inp : Input≤ bnd) ->
                IM.Inner (⟦ r ⟧ × Input≤ (fun f (position inp)))
      helper₁ xs = let open IM in
                   helper₂ =<< lookup k′ <$> get
        where
        i = (position xs , f , r)

        k′ : MemoTableKey i
        k′ = key k (position xs)

        helper₂ : Maybe (Value i) -> State MemoTable (Value i)
        helper₂ (just v) = return v  where open MemoState
        helper₂ nothing  = p xs                 >>= \v ->
                           modify (insert k′ v) >>
                           return v
          where open MemoState

    -- Other monadic operations.

    return : forall {bnd A} -> A -> P bnd idM A
    return a = pm \xs -> IM.return (a , string xs isBounded∶ refl)

    _>>=_ : forall {bnd A B f g} ->
            P bnd f A -> (A -> P (fun f bnd) g B) -> P bnd (g ∘M f) B
    _>>=_ {f = f} {g} (pm m₁) m₂ = pm \xs ->
      m₁ xs ⟨ IM._>>=_ ⟩ \ays ->
      let a = proj₁ ays; ys = proj₂ ays in
      fix (bounded ys) ⟨ IM._<$>_ ⟩
        unPM (m₂ a) (string ys isBounded∶
                       lemma f (bounded xs) (bounded ys))
      where
      lemma : forall f {i j k} -> j ≤ k -> i ≤ fun f j -> i ≤ fun f k
      lemma f j≤k i≤gj = trans i≤gj (monotone f j≤k)

      fix : forall {A i j} -> i ≤ j ->
            A × Input≤ (fun g i) ->
            A × Input≤ (fun g j)
      fix le (a , xs) =
        (a , string xs isBounded∶ lemma g le (bounded xs))

    _>>_ : forall {bnd A B f g} ->
           P bnd f A -> P (fun f bnd) g B -> P bnd (g ∘M f) B
    m₁ >> m₂ = m₁ >>= \_ -> m₂

    _=<<_ : forall {bnd A B f g} ->
            (A -> P (fun f bnd) g B) -> P bnd f A -> P bnd (g ∘M f) B
    m₂ =<< m₁ = m₁ >>= m₂

    ∅ : forall {bnd f A} -> P bnd f A
    ∅ = pm (\_ -> IM.∅)

    _∣_ : forall {bnd f A} -> P bnd f A -> P bnd f A -> P bnd f A
    pm m₁ ∣ pm m₂ = pm \xs -> IM._∣_ (m₁ xs) (m₂ xs)

    get : forall {bnd} -> P bnd idM (Input≤ bnd)
    get = pm \xs -> IM.return (xs , string xs isBounded∶ refl)

    put : forall {bnd bnd′} -> Input≤ bnd′ -> P bnd (constM bnd′) ⊤
    put xs = pm \_ -> IM.return (_ , xs)

    -- A generalised variant of modify.

    gmodify : forall {bnd A} f ->
              ((inp : Input≤ bnd) -> A × Input≤ (fun f (position inp))) ->
              P bnd f A
    gmodify f g = pm \xs -> IM.return (g xs)

    modify : forall {bnd} f ->
             ((inp : Input≤ bnd) -> Input≤ (fun f (position inp))) ->
             P bnd f ⊤
    modify f g = gmodify f (\xs -> (_ , g xs))

    adjustBound : forall {bnd f g A} ->
                  (forall p -> fun f p ≤ fun g p) ->
                  P bnd f A -> P bnd g A
    adjustBound hyp (pm m) =
      pm \xs ->
        let le = \(ys : _) -> trans (bounded ys) (hyp (position xs)) in
        map-× id (\ys -> string ys isBounded∶ le ys)
          ⟨ IM._<$>_ ⟩
        m xs

    run : forall {A f pos} ->
          Input pos -> P pos f A -> List (A × Input≤ (fun f pos))
    run xs (pm m) = proj₁ (m (xs isBounded∶ refl) empty)

------------------------------------------------------------------------
-- Memo tables

-- Shuffles the elements to simplify defining equality and order
-- relations for the keys.

shuffle : ∃ MemoTableKey -> Position × ∃₂ Key
shuffle ((pos , f , r) , key k .pos) = (pos , f , r , k)

-- Equality and ordering.

Eq : Rel (∃ MemoTableKey)
Eq = _≡_ ×-Rel _≈_  on₁  shuffle

Lt : Rel (∃ MemoTableKey)
Lt = ×-Lex _≡_ _<P_ _<_  on₁  shuffle

isOrdered : IsStrictTotalOrder Eq Lt
isOrdered = On.isStrictTotalOrder shuffle
              (posOrdered ×-isStrictTotalOrder keyOrdered)

indicesEqual′ : Eq =[ proj₁ ]⇒ _≡_
indicesEqual′ {((_ , _ , _) , key _ ._)}
              {((_ , _ , _) , key _ ._)} (eq₁ , eq₂) =
  ≡-cong₂ _,_ eq₁ (≡-cong₂ _,_ (funsEqual eq₂) (resultsEqual eq₂))

open Map isOrdered (\{k₁} {k₂} -> indicesEqual′ {k₁} {k₂}) Value

-- Instantiation of the Dummy module above.

open Dummy MemoTable empty insert lookup public
