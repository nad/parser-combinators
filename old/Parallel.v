Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Max.

Set Implicit Arguments.

CoInductive P (tok a : Set) : bool -> nat -> Set :=
  | symbolBind : forall e d,
                 (forall c : tok, P tok a (e c) (d c)) ->
                 P tok a false 0
  | fail       : P tok a false 0
  | returnPlus : forall e d,
                 list a -> P tok a e d -> P tok a true (S d).

Implicit Arguments symbolBind [tok a e d].
Implicit Arguments returnPlus [tok a e d].

Program CoFixpoint choice tok a e1 d1 e2 d2
  (p1 : P tok a e1 d1) (p2 : P tok a e2 d2) :
  P tok a (orb e1 e2) (max d1 d2) :=
  match p1                , p2 with
  | fail                  , p2                    => p2
  | returnPlus _ _ _ _    , fail                  => p1
  | symbolBind _ _ _      , fail                  => p1
  | symbolBind _ _ f1     , symbolBind _ _ f2     => symbolBind (fun c => choice (f1 c) (f2 c))
  | symbolBind _ _ _      , returnPlus _ _ xs2 p2 => returnPlus xs2 (choice p1 p2)
  | returnPlus _ _ xs1 p1 , symbolBind _ _ _      => returnPlus xs1 (choice p2 p1)
  | returnPlus _ _ xs1 p1 , returnPlus _ _ xs2 p2 => returnPlus (app xs1 xs2) (choice p1 p2)
  end.

Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Arith.Wf_nat.

Program Fixpoint parse' stupid tok a e d
  (p : P tok a e d) (s : list tok)
  (eq : stupid = existT (fun _ => nat) (length s) d)
  {wf (wf_lexprod nat (fun _ => nat) lt (fun _ => lt)
                      lt_wf (fun _ => lt_wf)) stupid}
  : list (a * list tok) :=
  match d , p                   , s with
  | _     , symbolBind _ _ f    , cons c s => @parse' _ _ _ _ _ (f c) s (refl_equal _)
  | _     , symbolBind _ _ f    , nil      => nil
  | _     , fail                , _        => nil
  | S d   , returnPlus _ _ xs p , s        => app (map (fun x => (x , s)) xs)
                                                  (@parse' (existT _ (length s) d) _ _ _ _
                                                           p s (refl_equal _))
  | 0     , returnPlus _ _ _ _  , _        => !
  end.

Definition parse tok a e d (p : P tok a e d) (s : list tok) :
                 list (a * list tok) :=
  parse' p s (refl_equal _).
