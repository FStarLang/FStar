module LatticeAlg

(* An algebraic presentation of ALL using action trees. *)

open FStar.Tactics
open FStar.List.Tot
open FStar.Universe

#set-options "--print_universes --print_implicits --print_effect_args"

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

let unreachable (#a:Type u#aa) () : Pure a (requires False) (ensures (fun _ -> False)) =
  coerce #(raise_t string) #a (raise_val "whatever")

type eff_label =
  | RD
  | WR
  | EXN

type annot = eff_label -> bool

type state = int

noeq
type action : Type0 -> Type0 -> Type u#1 =
  | Read : action unit state
  | Write : action state unit
  | Raise : #a:Type0 -> action exn a
  
noeq
type repr0 (a:Type u#aa) : Type u#(max 1 aa) =
  | Return : a -> repr0 a
  | Act    : #i:_ -> #o:_ -> act:(action i o) -> i -> k:(o -> repr0 a) -> repr0 a
  
let abides_act #i #o (ann:annot) (a : action i o) : prop =
    (Read? a ==> ann RD)
  /\ (Write ? a ==> ann WR)
  /\ (Raise ? a ==> ann EXN)

let rec abides #a (ann:annot) (f : repr0 a) : prop =
  begin match f with
  | Act a i k ->
    abides_act ann a /\ (forall o. (FStar.WellFounded.axiom1 k o; abides ann (k o)))
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

let rec abides_sublist #a (l1 l2 : list eff_label) (c : repr0 a)
  : Lemma (requires (abides (interp l1) c) /\ sublist l1 l2)
          (ensures (abides (interp l2) c))
          [SMTPat (abides (interp l2) c); SMTPat (sublist l1 l2)]
  = match c with
    | Return _ -> ()
    | Act a i k -> 
      let sub o : Lemma (abides (interp l2) (k o)) =
        FStar.WellFounded.axiom1 k o;
        abides_sublist l1 l2 (k o)
      in
      Classical.forall_intro sub

let rec abides_app #a (l1 l2 : list eff_label) (c : repr0 a)
  : Lemma (requires (abides (interp l1) c \/ abides (interp l2) c))
          (ensures (abides (interp (l1@l2)) c))
          [SMTPat (abides (interp (l1@l2)) c)]
  = // GM: Just copied the proof from above since it ought to work,
    //     do something smarter later.
    match c with
    | Return _ -> ()
    | Act a i k -> 
      let sub o : Lemma (abides (interp (l1@l2)) (k o)) =
        FStar.WellFounded.axiom1 k o;
        abides_app l1 l2 (k o)
      in
      Classical.forall_intro sub


type repr (a:Type u#aa)
          (labs : list u#0 eff_label) // GM: why do I need this annot...? seems we get an ill-formed type if not
                                      // somehow it's about `type` instead of `let`
  : Type u#(max 1 aa)
  =
  r:(repr0 a){abides (interp labs) r}

let ann_le (ann1 ann2 : annot) : prop =
  forall x. ann1 x ==> ann2 x
  
let return (a:Type) (x:a)
  : repr a []
  =
  Return x

let rec bind (a b : Type)
  (labs1 labs2 : list eff_label)
  (c : repr a labs1)
  (f : (x:a -> repr b labs2))
  : Tot (repr b (labs1@labs2))
  = match c with
    | Return x -> f x
    | Act a i k -> 
      let k' o : repr b (labs1@labs2) =
        FStar.WellFounded.axiom1 k o;
        bind _ _ _ _ (k o) f
      in
      Act a i k'

let subcomp (a:Type)
  (labs1 labs2 : list eff_label)
  (f : repr a labs1)
  : Pure (repr a labs2)
         (requires (sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let ite (p q r : Type0) = (p ==> q) /\ (~p ==> r)

let if_then_else
  (a : Type)
  (labs1 labs2 : list eff_label)
  (f : repr a labs1)
  (g : repr a labs2)
  (p : bool)
  : Type
  = repr a (labs1@labs2)

[@@smt_reifiable_layered_effect]
total // need this for catch!!
reifiable
reflectable
layered_effect {
  EFF : a:Type -> list eff_label  -> Effect
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
 (wp : pure_wp a)
 (f : eqtype_as_type unit -> PURE a wp)
 : Pure (repr a [])
        (requires (wp (fun _ -> True) /\ pure_monotonic wp))
        (ensures (fun _ -> True))
 = Return (f ())
 
sub_effect PURE ~> EFF = lift_pure_eff

let get () : EFF int [RD] =
  EFF?.reflect (Act Read () Return)
  
let put (s:state) : EFF unit [WR] =
  EFF?.reflect (Act Write s Return)

let raise #a (e:exn) : EFF a [EXN] =
  EFF?.reflect (Act Raise e Return)

exception Failure of string

let test0 (x y : int) : EFF int [RD; EXN] =
  let z = get () in
  if x + z > 0
  then raise (Failure "oops")
  else y - z

let test1 (x y : int) : EFF int [EXN; RD; WR] =
  let z = get () in
  if x + z > 0
  then raise (Failure "asd")
  else (put 42; y - z)

let sublist_at_self (l1 : list eff_label)
  : Lemma (sublist (l1@l1) l1)
          [SMTPat (l1@l1)]
  = Classical.forall_intro (List.Tot.Properties.append_mem l1 l1)

let labpoly #labs (f g : unit -> EFF int labs) : EFF int labs =
  f () + g ()

// FIXME: putting this definition inside catch causes a blowup:
//
// Unexpected error
// Failure("Empty option")
// Raised at file "stdlib.ml", line 29, characters 17-33
// Called from file "ulib/ml/FStar_All.ml" (inlined), line 4, characters 21-24
// Called from file "src/ocaml-output/FStar_TypeChecker_Util.ml", line 874, characters 18-65
// Called from file "src/ocaml-output/FStar_TypeChecker_Common.ml", line 675, characters 34-38
// Called from file "src/ocaml-output/FStar_TypeChecker_Common.ml", line 657, characters 25-33
// Called from file "src/ocaml-output/FStar_TypeChecker_TcTerm.ml", line 2048, characters 30-68
// Called from file "src/basic/ml/FStar_Util.ml", line 24, characters 14-18
// ....
let rec catch0 #a #labs (t1 : repr a (EXN::labs))
                    (t2 : repr a labs)
  : repr a labs
  = match t1 with
    | Act Raise e _ -> t2
    | Act act i k ->
      let k' o : repr a labs =
        FStar.WellFounded.axiom1 k o;
        catch0 (k o) t2
      in
      Act act i k'
    | Return v -> Return v
   | _ -> unreachable ()

(* no rollback *)
let catch #a #labs
  (f : unit -> EFF a (EXN::labs))
  (g : unit -> EFF a labs)
  : EFF a labs
=
 EFF?.reflect begin
   catch0 (reify (f ())) (reify (g ()))
 end

// TODO: haskell-like runST.
// strong update with index on state type(s)?

let test_catch #labs (f : unit -> EFF int [EXN;WR]) : EFF int [WR] =
  catch f (fun () -> 42)

let test_catch2 (f : unit -> EFF int [EXN;EXN;WR]) : EFF int [EXN;WR] =
  catch f (fun () -> 42)

let interp_pure_tree #a (t : repr a []) : Tot a =
  match t with
  | Return x -> x

let interp_pure #a (f : unit -> EFF a []) : Tot a = interp_pure_tree (reify (f ()))

let rec interp_rd_tree #a (t : repr a [RD]) (s:state) : Tot a =
  match t with
  | Return x -> x
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rd_tree (k s) s

let interp_rd #a (f : unit -> EFF a [RD]) (s:state) : Tot a = interp_rd_tree (reify (f ())) s

let rec interp_rdwr_tree #a (t : repr a [RD;WR]) (s:state) : Tot (a & state) =
  match t with
  | Return x -> (x, s)
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rdwr_tree (k s) s
  | Act Write s k ->
    FStar.WellFounded.axiom1 k ();
    interp_rdwr_tree (k ()) s
    
let interp_rdwr #a (f : unit -> EFF a [RD;WR]) (s:state) : Tot (a & state) = interp_rdwr_tree (reify (f ())) s

let rec interp_all_tree #a (t : repr a [RD;WR;EXN]) (s:state) : Tot (option a & state) =
  match t with
  | Return x -> (Some x, s)
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_all_tree (k s) s
  | Act Write s k ->
    FStar.WellFounded.axiom1 k ();
    interp_all_tree (k ()) s
  | Act Raise e k ->
    (None, s)
    
let interp_all #a (f : unit -> EFF a [RD;WR;EXN]) (s:state) : Tot (option a & state) = interp_all_tree (reify (f ())) s
