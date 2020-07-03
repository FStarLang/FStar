module RunST

(* Similar to LatticeAlg, but ignoring exceptions to start with
a simpler example. The interaction between state+exn can be tricky. *)

open FStar.Tactics
open FStar.List.Tot
open FStar.Universe
open FStar.Ghost

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
  | EXN

type annot = eff_label -> Type0

noeq
type action : inp:Type0 -> out:Type0 -> st0:Type0 -> st1:Type0 -> Type u#1 =
  | Read  : #st0:Type0 -> action unit st0 st0 st0
  | Write : #st0:Type0 -> #st1:Type0 -> action st1 unit st0 st1
  | Raise : #a:Type -> #st0:Type -> action exn a st0 st0 // exceptions do not change state type

noeq
type repr0 (a:Type u#aa) : st0:Type0 -> st1:Type0 -> Type u#(max 1 aa) =
  | Return : #s:Type0 -> x:a -> repr0 a s s
  | Act    : #i:_ -> #o:_ -> #st0:_ -> #st1:_ -> #st2:_ ->
             act:(action i o st0 st1) -> i -> k:(o -> repr0 a st1 st2) -> repr0 a st0 st2

let abides_act #i #o (ann:annot) (a : action i o 'st0 'st1) : prop =
    (Read? a ==> ann RD)
  /\ (Write ? a ==> ann WR)
  /\ (Raise ? a ==> ann EXN)

let rec abides #a (ann:annot) (f : repr0 a 'st0 'st1) : prop =
  begin match f with
  | Act a i k ->
    abides_act ann a /\ (forall o. (axiom1 k o; abides ann (k o)))
  | Return _ -> True
  end

let interp (l : list eff_label) : annot =
  fun lab -> memP lab l

let rec interp_at (l1 l2 : list eff_label) (l : eff_label)
  : Lemma (interp (l1@l2) l <==> (interp l1 l \/ interp l2 l))
          [SMTPat (interp (l1@l2) l)]
  = match l1 with
    | [] -> ()
    | _::l1 -> interp_at l1 l2 l

let sublist (l1 l2 : list eff_label) =
  forall x. memP x l1 ==> memP x l2

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

let rec at_sublist
  (l1 l2 l3 : list eff_label)
  : Lemma (requires (sublist l1 l3 /\ sublist l2 l3))
          (ensures (sublist (l1@l2) l3))
          [SMTPat (sublist (l1@l2) l3)]
  = match l1 with
    | [] -> ()
    | _::l1 -> at_sublist l1 l2 l3

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
          (labs : erased u#0 (list u#0 eff_label))
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
  (labs1 labs2 : erased (list eff_label)) // forgetting the erased here gives an odd error ar the effect defn
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
  (labs1 labs2 : erased (list eff_label))
  (s0 s1 : Type)
  (f : repr a s0 s1 labs1)
  : Pure (repr a s0 s1 labs2)
         (requires (sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let ite (p q r : Type0) = (p ==> q) /\ (~p ==> r)

let if_then_else
  (a : Type)
  (labs1
   labs2 : erased (list eff_label))
  (st0
   st1 : Type)
  (f : repr a st0 st1 labs1)
  (g : repr a st0 st1 labs2)
  (p : bool)
: Type
= repr a st0 st1 (labs1@labs2)

[@@allow_informative_binders]
total
reifiable
reflectable
layered_effect {
  EFF : a:Type -> Type0 -> Type0 -> erased (list eff_label)  -> Effect // would be nice to get this from repr
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
 (f : eqtype_as_type unit -> PURE a wp)
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
  = ()

let labpoly #s0 #labs (f g : unit -> EFF int s0 s0 labs) : EFF int s0 s0 labs =
  f () + g ()

let termination_hack (i:int) : y:int{y<<i} = admit(); i-1

let rec aux (i:int) : EFF unit int int [RD;WR] (decreases i) =
  if i = 0
  then ()
  else
    (put (get () + i);
     aux (termination_hack i))

let sumn #st (n:nat) : EFF int st int [RD;WR] =
  put 0;
  aux n;
  get ()

let _runST (#a:Type0) #labs #si #sf ($c : repr a si sf labs) (s0:si) : Tot (option (a & sf)) =
  let rec aux #st0 (s:st0) (c : repr a st0 sf labs) : Tot (option (a & sf)) (decreases c) =
    match c with
    | Return x -> Some (x, s)
    | Act Read  _ k -> axiom1 k s; aux s (k s)
    | Act Write s k -> axiom1 k (); aux s (k ())
    | Act Raise e k -> None
  in
  aux s0 c

let runST #a #labs #si #sf ($c : (unit -> EFF a si sf labs)) (s0:si) : Tot (option (a & sf)) =
  _runST (reify (c ())) s0

// GM: doesn't really reduce
let test_run_st : option int =
  let c () : EFF int unit int [RD;WR] =
    sumn 5
  in
  match runST #int #[RD;WR] c ()  with
  | Some xs -> Some (fst xs)
  // | None -> None // incomplete patterns???
  | _ -> None

//#set-options "--print_full_names"

let rec _catchST (#a:Type0) #labs #si #sf
  (stt:Type)
  (c : repr a si sf (RD::WR::labs))
  (s0:si)
: repr (a & sf) stt stt labs
= match c with
  | Return x -> Return (x, s0)
  | Act Read _i k -> axiom1 k s0; _catchST #a #labs stt (k s0) s0
  | Act Write s k -> axiom1 k (); _catchST #a #labs stt (k ()) s
  | Act Raise e k ->
    let k' o : repr (a & sf) _ _ labs =
      axiom1 k o;
      _catchST #a #labs stt (k o) s0
    in
    Act Raise e k'

(* I would hope to write a general case like this:

assume
val act_keeps_state (a:action 'in 'out 'st0 'st1) : Lemma ('st0 == 'st1)

  | Act #_ #ot #st0 #st1 #st2__
        act e k ->
    act_keeps_state act;
    assert (st1 == unit);
    assert (st2__ == unit);
    let k' o : repr (a & sf) st1 st2__ labs =
      axiom1 k o;
      _catchST #a #labs stt (k o) s0
    in
    Act act e k'

 It's required that all unhandled actions do not change the state. TBD how
 that's best encoded.
*)

// GM: Remember the dollar sign! Otherwise, even if we provide the implicits
// explicitly, we go to a subtyping query which usually fails.
let catchST #a #labs #st #si #sf ($c : (unit -> EFF a si sf (RD::WR::labs))) (s0:si)
: EFF (a & sf) st st labs
= EFF?.reflect (_catchST st (reify (c ())) s0)

let puresum (n:nat)
  : EFF int bool bool []
  = let (x, _) = catchST (fun () -> sumn 42) 0 in x

let pure_tree_invariant_state #a #st0 #st1 (t : repr a st0 st1 []) : Lemma (st0 == st1) = ()

// st0 and st1 have to match, but anyway
let interp_pure_tree #a #st0 #st1 (t : repr a st0 st1 []) : Tot a =
  match t with
  | Return x -> x

let interp_pure #a #st0 #st1 ($f : unit -> EFF a st0 st1 []) : Tot a = interp_pure_tree (reify (f ()))


inline_for_extraction
let xxx = interp_pure (fun () -> puresum 10)

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
