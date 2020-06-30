module RunST

(* Similar to LatticeAlg, but ignoring exceptions to start with
a simpler example. The interaction between state+exn can be tricky. *)

open FStar.Tactics
open FStar.List.Tot
open FStar.Universe

module WF = FStar.WellFounded

let axiom1 = WF.axiom1

#set-options "--print_universes --print_implicits --print_effect_args"

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

let unreachable (#a:Type u#aa) () : Pure a (requires False) (ensures (fun _ -> False)) =
  coerce (raise_val "whatever")

type eff_label =
  | RD
  | WR

type annot = eff_label -> bool

noeq
type action : inp:Type0 -> out:Type0 -> st0:Type0 -> st1:Type0 -> Type u#1 =
  | Read  : #st0:Type0 -> action unit st0 st0 st0
  | Write : #st0:Type0 -> #st1:Type0 -> action st1 unit st0 st1

noeq
type repr0 (a:Type u#aa) : st0:Type0 -> st1:Type0 -> Type u#(max 1 aa) =
  | Return : #s:Type0 -> x:a -> repr0 a s s
  | Act    : #i:_ -> #o:_ -> #st0:_ -> #st1:_ -> #st2:_ ->
             act:(action i o st0 st1) -> i -> k:(o -> repr0 a st1 st2) -> repr0 a st0 st2

let abides_act #i #o (ann:annot) (a : action i o 'st0 'st1) : prop =
    (Read? a ==> ann RD)
  /\ (Write ? a ==> ann WR)

let rec abides #a (ann:annot) (f : repr0 a 'st0 'st1) : prop =
  begin match f with
  | Act a i k ->
    abides_act ann a /\ (forall o. (axiom1 k o; abides ann (k o)))
  | Return _ -> True
  end

let interp (l : list eff_label) : annot =
  fun lab -> mem lab l

let rec interp_at (l1 l2 : list eff_label) (l : eff_label)
  : Lemma (interp (l1@l2) l == (interp l1 l || interp l2 l))
          [SMTPat (interp (l1@l2) l)]
  = match l1 with
    | [] -> ()
    | _::l1 -> interp_at l1 l2 l

let sublist (l1 l2 : list eff_label) =
  forall x. mem x l1 ==> mem x l2

let sublist_refl
  (l : list eff_label)
  : Lemma (sublist l l)
          [SMTPat (sublist l l)]
  = ()

let rec interp_sublist (l1 l2 : list eff_label) (l : eff_label)
  : Lemma (requires (sublist l1 l2))
          (ensures (interp l1 l ==> interp l2 l))
          [SMTPat (interp l1 l); SMTPat (sublist l1 l2)]
  = match l1 with
    | [] -> ()
    | _::l1 -> interp_sublist l1 l2 l

let rec sublist_at
  (l1 l2 : list eff_label)
  : Lemma (sublist l1 (l1@l2) /\ sublist l2 (l1@l2))
          [SMTPatOr [[SMTPat (sublist l1 (l1@l2))];
                     [SMTPat (sublist l2 (l1@l2))]]]
  = match l1 with
    | [] -> ()
    | _::l1 -> sublist_at l1 l2

let rec abides_sublist #a (l1 l2 : list eff_label) (c : repr0 a 'st0 'st1)
  : Lemma (requires (abides (interp l1) c) /\ sublist l1 l2)
          (ensures (abides (interp l2) c))
          [SMTPat (abides (interp l2) c); SMTPat (sublist l1 l2)]
  = match c with
    | Return _ -> ()
    | Act a i k ->
      let sub o : Lemma (abides (interp l2) (k o)) =
        axiom1 k o;
        abides_sublist l1 l2 (k o)
      in
      Classical.forall_intro sub

let rec abides_app #a (l1 l2 : list eff_label) (c : repr0 a 'st0 'st1)
  : Lemma (requires (abides (interp l1) c \/ abides (interp l2) c))
          (ensures (abides (interp (l1@l2)) c))
          [SMTPat (abides (interp (l1@l2)) c)]
  = // GM: Just copied the proof from above since it ought to work,
    //     do something smarter later.
    match c with
    | Return _ -> ()
    | Act a i k ->
      let sub o : Lemma (abides (interp (l1@l2)) (k o)) =
        axiom1 k o;
        abides_app l1 l2 (k o)
      in
      Classical.forall_intro sub


type repr (a:Type u#aa)
          (st0 st1 : Type0)
          (labs : list u#0 eff_label)
  : Type u#(max 1 aa)
  =
  r:(repr0 a st0 st1){abides (interp labs) r}

let ann_le (ann1 ann2 : annot) : prop =
  forall x. ann1 x ==> ann2 x

let return (a:Type) (x:a) (s:Type)
  : repr a s s []
  =
  Return x

let rec bind (a b : Type)
  (st0 st1 st2 : Type)
  (labs1 labs2 : list eff_label)
  (c : repr a st0 st1 labs1)
  (f : (x:a -> repr b st1 st2 labs2))
  : Tot (repr b st0 st2 (labs1@labs2))
  = match c with
    | Return x -> f x
    | Act a i k ->
      let k' o : repr b _ _ (labs1@labs2) =
        axiom1 k o;
        bind _ _ _ _ _ _ _ (k o) f
      in
      Act a i k'

let subcomp (a:Type)
  (labs1 labs2 : list eff_label)
  (s0 s1 : Type)
  (f : repr a s0 s1 labs1)
  : Pure (repr a s0 s1 labs2)
         (requires (sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let ite (p q r : Type0) = (p ==> q) /\ (~p ==> r)

let if_then_else
  (a : Type)
  (labs1 labs2 : list eff_label)
  (st0 st1 : Type)
  (f : repr a st0 st1 labs1)
  (g : repr a st0 st1 labs2)
  (p : Type0)
  : Type
  = repr a st0 st1 (labs1@labs2)

[@@smt_reifiable_layered_effect]
total // need this for catch!!
reifiable
reflectable
layered_effect {
  EFF : a:Type -> Type0 -> Type0 -> list eff_label  -> Effect
  with
  repr         = repr;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

unfold
let pure_monotonic #a (wp : pure_wp a) : Type =
  forall p1 p2. (forall x. p1 x ==> p2 x) ==> wp p1 ==> wp p2

//unfold
//let sp #a (wp : pure_wp a) : pure_post a =
//  fun x -> ~ (wp (fun y -> ~(x == y)))

let lift_pure_eff
 (a:Type)
 (s:Type)
 (wp : pure_wp a)
 (f : unit -> PURE a wp)
 : Pure (repr a s s [])
        (requires (wp (fun _ -> True) /\ pure_monotonic wp))
        (ensures (fun _ -> True))
 = Return (f ())

sub_effect PURE ~> EFF = lift_pure_eff

let get #s () : EFF s s s [RD] =
  EFF?.reflect (Act Read () Return)

let put #si #so (x:so) : EFF unit si so [WR] =
  EFF?.reflect (Act Write x Return)

// GM: something is up with unfolding. Try only [dump ""] here
// and see an explosion. I had filed it as #2039.
let test0 (x y : int) : EFF int int int [RD] by (norm [delta]) =
  let z = get #int () in
  if x + z > 0
  then 0
  else 1 // y - z

let test1 (x y : int) : EFF int int int [RD; WR] =
  let z = get () in
  if x + z > 0
  then 0
  else (put 42; y - z)

let sublist_at_self (l1 : list eff_label)
  : Lemma (sublist (l1@l1) l1)
          [SMTPat (l1@l1)]
  = Classical.forall_intro (List.Tot.Properties.append_mem l1 l1)

let labpoly #s0 #labs (f g : unit -> EFF int s0 s0 labs) : EFF int s0 s0 labs =
  f () + g ()

// is this really similar to the haskell one?
let runST #a #labs (c : (s:Type0 -> repr a s s labs)) : Tot a =
  let rec aux #st0 #st1 (s:st0) (c : repr a st0 st1 labs) : Tot a (decreases c) =
    match c with
    | Return x -> x
    | Act Read  _ k -> axiom1 k s; aux s (k s)
    | Act Write s k -> axiom1 k (); aux s (k ())
  in
  aux () (c unit)

let pure_tree_invariant_state #a #st0 #st1 (t : repr a st0 st1 []) : Lemma (st0 == st1) = ()

// st0 and st1 have to match, but anyway
let interp_pure_tree #a #st0 #st1 (t : repr a st0 st1 []) : Tot a =
  match t with
  | Return x -> x

let interp_pure #a #st0 #st1 (f : unit -> EFF a st0 st1 []) : Tot a = interp_pure_tree (reify (f ()))

let rec interp_rd_tree #a #st0 #st1 (t : repr a st0 st1 [RD]) (s:st0) : Tot a =
  match t with
  | Return x -> x
  | Act Read _ k ->
    axiom1 k s;
    interp_rd_tree (k s) s

let interp_rd #a #st0 #st1 (f : unit -> EFF a st0 st1 [RD]) (s:st0) : Tot a
  = interp_rd_tree (reify (f ())) s

let rec interp_rdwr_tree #a #st0 #st1 (t : repr a st0 st1 [RD;WR]) (s:st0) : Tot (a & st1) =
  match t with
  | Return x -> (x, s)
  | Act Read _ k ->
    axiom1 k s;
    interp_rdwr_tree (k s) s
  | Act Write s k ->
    axiom1 k ();
    interp_rdwr_tree (k ()) s

let interp_rdwr #a #st0 #st1
  (f : unit -> EFF a st0 st1 [RD;WR]) (s:st0)
  : Tot (a & st1)
  = interp_rdwr_tree (reify (f ())) s
