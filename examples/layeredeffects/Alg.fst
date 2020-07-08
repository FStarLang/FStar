module Alg

(* An algebraic presentation of ALL using action trees. *)

open FStar.Tactics
open FStar.List.Tot
open FStar.Universe
module WF = FStar.WellFounded
module L = Lattice

type state = int

type empty =

type op =
  | Read
  | Write
  | Raise
  | Other of int

assume val other_inp : int -> Type
let op_inp : op -> Type =
 function
 | Read -> unit
 | Write -> state
 | Raise -> exn
 | Other i -> other_inp i

assume val other_out : int -> Type
let op_out : op -> Type =
 function
 | Read -> state
 | Write -> unit
 | Raise -> empty
 | Other i -> other_inp i

noeq
type tree0 (a:Type u#aa) : Type u#aa =
  | Return : a -> tree0 a
  | Act    : op:op -> i:(op_inp op) -> k:(op_out op -> tree0 a) -> tree0 a

type ops = list op

let rec abides #a (labs:ops) (f : tree0 a) : prop =
  begin match f with
  | Act a i k ->
    mem a labs /\ (forall o. (FStar.WellFounded.axiom1 k o; abides labs (k o)))
  | Return _ -> True
  end

type tree (a:Type u#aa)
          (labs : list u#0 op)
  : Type u#aa
  =
  r:(tree0 a){abides labs r}

let rec interp_at (l1 l2 : ops) (l : op)
  : Lemma (mem l (l1@l2) == (mem l l1 || mem l l2))
          [SMTPat (mem l (l1@l2))]
  = match l1 with
    | [] -> ()
    | _::l1 -> interp_at l1 l2 l

let sublist (l1 l2 : ops) = forall x. mem x l1 ==> mem x l2

let rec sublist_at
  (l1 l2 : ops)
  : Lemma (sublist l1 (l1@l2) /\ sublist l2 (l1@l2))
          [SMTPatOr [[SMTPat (sublist l1 (l1@l2))];
                     [SMTPat (sublist l2 (l1@l2))]]]
  = match l1 with
    | [] -> ()
    | _::l1 -> sublist_at l1 l2

let sublist_at_self
  (l : ops)
  : Lemma (sublist l (l@l))
          [SMTPat (sublist l (l@l))]
  = ()
  
let rec abides_sublist_nopat #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c) /\ sublist l1 l2)
          (ensures (abides l2) c)
  = match c with
    | Return _ -> ()
    | Act a i k ->
      let sub o : Lemma (abides l2 (k o)) =
        FStar.WellFounded.axiom1 k o;
        abides_sublist_nopat l1 l2 (k o)
      in
      Classical.forall_intro sub

let abides_sublist #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c) /\ sublist l1 l2)
          (ensures (abides l2 c))
          [SMTPat (abides l2 c); SMTPat (sublist l1 l2)]
  = abides_sublist_nopat l1 l2 c
  
let abides_at_self #a
  (l : ops)
  (c : tree0 a)
  : Lemma (abides (l@l) c <==>  abides l c)
          [SMTPat (abides (l@l) c)]
  = (* Trigger some patterns *)
    assert (sublist l (l@l));
    assert (sublist (l@l) l)

let abides_app #a (l1 l2 : ops) (c : tree0 a)
  : Lemma (requires (abides l1 c \/ abides l2 c))
          (ensures (abides (l1@l2) c))
          [SMTPat (abides (l1@l2) c)]
  = sublist_at l1 l2

let handler_ty_l (o:op) (b:Type) (labs:ops) =
  op_inp o -> (op_out o -> tree b labs) -> tree b labs

let handler_ty (labs0 : ops) (b:Type) (labs1 : ops) : Type =
  o:op{mem o labs0} -> handler_ty_l o b labs1

(* The most generic handling construct, we use it to implement bind *)
val handle_with (#a #b:_) (#labs0 #labs1 : ops)
           (f:tree a labs0)
           (v : a -> tree b labs1)
           (h: handler_ty labs0 b labs1)
           : tree b labs1
let rec handle_with #a #b #labs0 #labs1 f v h =
  match f with
  | Return x -> v x
  | Act act i k ->
    let k' o : tree b labs1 =
        WF.axiom1 k o;
       handle_with #a #b #labs0 #labs1 (k o) v h
    in
    h act i k'

let return (a:Type) (x:a)
  : tree a []
  = Return x

let bind (a b : Type)
  (labs1 labs2 : ops)
  (c : tree a labs1)
  (f : (x:a -> tree b labs2))
  : Tot (tree b (labs1@labs2))
  = handle_with #_ #_ #labs1 #(labs1@labs2) c f (fun act i k -> Act act i k)
  
let subcomp (a:Type)
  (labs1 labs2 : ops)
  (f : tree a labs1)
  : Pure (tree a labs2)
         (requires (sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let if_then_else
  (a : Type)
  (labs1 labs2 : ops)
  (f : tree a labs1)
  (g : tree a labs2)
  (p : bool)
  : Type
  = tree a (labs1@labs2)

let _get : tree int [Read] = Act Read () Return
let _put (s:state) : tree unit [Write] = Act Write s Return

[@@allow_informative_binders]
total // need this for catch!!
reifiable
reflectable
layered_effect {
  Alg : a:Type -> ops  -> Effect
  with
  repr         = tree;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

let get () : Alg int [Read] =
  Alg?.reflect _get

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
 : Pure (tree a [])
        (requires (wp (fun _ -> True) /\ pure_monotonic wp))
        (ensures (fun _ -> True))
 = Return (f ())

sub_effect PURE ~> Alg = lift_pure_eff

let put (s:state) : Alg unit [Write] =
  Alg?.reflect (Act Write s Return)

#set-options "--print_implicits"

let raise #a (e:exn) : Alg a [Raise] =  
  Alg?.reflect (Act Raise e (fun e -> match e with))
  // funnily enough, the version below also succeeds from concluding
  // a==empty under the lambda since the context becomes inconsistent
  //Alg?.reflect (Act Raise e Return

exception Failure of string

let test0 (x y : int) : Alg int [Read; Raise] =
  let z = get () in
  if z < 0 then raise (Failure "error");
  x + y + z

let test1 (x y : int) : Alg int [Raise; Read; Write] =
  let z = get () in
  if x + z > 0
  then raise (Failure "asd")
  else (put 42; y - z)

let labpoly #labs (f g : unit -> Alg int labs) : Alg int labs =
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
let rec catch0 #a #labs (t1 : tree a (Raise::labs))
                        (t2 : tree a labs)
  : tree a labs
  = match t1 with
    | Act Raise e _ -> t2
    | Act act i k ->
      let k' o : tree a labs =
        FStar.WellFounded.axiom1 k o;
        catch0 (k o) t2
      in
      Act act i k'
    | Return v -> Return v

(* no rollback *)
let catch #a #labs
  (f : unit -> Alg a (Raise::labs))
  (g : unit -> Alg a labs)
  : Alg a labs
=
 Alg?.reflect begin
   catch0 (reify (f ())) (reify (g ()))
 end

let rec _catchST #a #labs (t1 : tree a (Read::Write::labs)) (s0:state) : tree (a & int) labs =
  match t1 with
  | Return v -> Return (v, s0)
  | Act Write s k -> WF.axiom1 k (); _catchST (k ()) s
  | Act Read  _ k -> WF.axiom1 k s0; _catchST (k s0) s0
  | Act act i k ->
     let k' o : tree (a & int) labs =
       WF.axiom1 k o;
       _catchST #a #labs (k o) s0
     in
     Act act i k'

let catchST #a #labs
  (f : unit -> Alg a (Read::Write::labs))
  (s0 : state)
  : Alg (a & state) labs
=
 Alg?.reflect begin
   _catchST (reify (f ())) s0
 end

let g #labs () : Alg int labs = 42  //AR: 07/03: had to hoist after removing smt_reifiablep

let test_catch #labs (f : unit -> Alg int [Raise;Write]) : Alg int [Write] =
  catch f g

let test_catch2 (f : unit -> Alg int [Raise;Raise;Write]) : Alg int [Raise;Write] =
  catch f g

let interp_pure_tree #a (t : tree a []) : Tot a =
  match t with
  | Return x -> x

let interp_pure #a (f : unit -> Alg a []) : Tot a = interp_pure_tree (reify (f ()))

let rec interp_rd_tree #a (t : tree a [Read]) (s:state) : Tot a =
  match t with
  | Return x -> x
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rd_tree (k s) s

let interp_rd #a (f : unit -> Alg a [Read]) (s:state) : Tot a = interp_rd_tree (reify (f ())) s

let rec interp_rdwr_tree #a (t : tree a [Read;Write]) (s:state) : Tot (a & state) =
  match t with
  | Return x -> (x, s)
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rdwr_tree (k s) s
  | Act Write s k ->
    FStar.WellFounded.axiom1 k ();
    interp_rdwr_tree (k ()) s

let interp_rdwr #a (f : unit -> Alg a [Read;Write]) (s:state) : Tot (a & state) = interp_rdwr_tree (reify (f ())) s

let rec interp_read_raise_tree #a (t : tree a [Read;Raise]) (s:state) : either exn a =
  match t with
  | Return x -> Inr x
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_read_raise_tree (k s) s
  | Act Raise e k ->
    Inl e

let interp_read_raise_exn #a (f : unit -> Alg a [Read;Raise]) (s:state) : either exn a =
  interp_read_raise_tree (reify (f ())) s

let rec interp_all_tree #a (t : tree a [Read;Write;Raise]) (s:state) : Tot (option a & state) =
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

let interp_all #a (f : unit -> Alg a [Read;Write;Raise]) (s:state) : Tot (option a & state) = interp_all_tree (reify (f ())) s

//let action_input (a:action 'i 'o) = 'i
//let action_output (a:action 'i 'o) = 'o
//
//let handler_ty (a:action _ _) (b:Type) (labs:list eff_label) =
//    action_input a ->
//    (action_output a -> tree b labs) -> tree b labs
//
//let dpi31 (#a:Type) (#b:a->Type) (#c:(x:a->b x->Type)) (t : (x:a & y:b x & c x y)) : a =
//  let (| x, y, z |) = t in x
//
//let dpi32 (#a:Type) (#b:a->Type) (#c:(x:a->b x->Type)) (t : (x:a & y:b x & c x y)) : b (dpi31 t) =
//  let (| x, y, z |) = t in y
//
//let dpi33 (#a:Type) (#b:a->Type) (#c:(x:a->b x->Type)) (t : (x:a & y:b x & c x y)) : c (dpi31 t) (dpi32 t) =
//  let (| x, y, z |) = t in z

  //handler_ty (dpi33 (action_of l)) b labs
  //F* complains this is not a function
  //let (| _, _, a |) = action_of l in
  //handler_ty a b labs

(* A generic handler for a (single) label l, relies on the fact that
we can compare actions for equality, or equivalently map them to their
labels. *)
val handle (#a #b:_) (#labs:_) (o:op)
           (f:tree a (o::labs))
           (h:handler_ty_l o b labs)
           (v: a -> tree b labs)
           : tree b labs
let rec handle #a #b #labs l f h v =
  match f with
  | Return x -> v x
  | Act act i k ->
    if act = l
    then h i (fun o -> WF.axiom1 k o; handle l (k o) h v)
    else begin
      let k' o : tree b labs =
         WF.axiom1 k o;
         handle l (k o) h v
      in
      Act act i k'
    end

(* Easy enough to handle 2 labels at once *)
val handle2 (#a #b:_) (#labs:_) (l1 l2 : op)
           (f:tree a (l1::l2::labs))
           (h1:handler_ty_l l1 b labs)
           (h2:handler_ty_l l2 b labs)
           (v : a -> tree b labs)
           : tree b labs
let rec handle2 #a #b #labs l1 l2 f h1 h2 v =
  match f with
  | Return x -> v x
  | Act act i k ->
    if act = l1
    then h1 i (fun o -> WF.axiom1 k o; handle2 l1 l2 (k o) h1 h2 v)
    else if act = l2
    then h2 i (fun o -> WF.axiom1 k o; handle2 l1 l2 (k o) h1 h2 v)
    else begin
      let k' o : tree b labs =
         WF.axiom1 k o;
         handle2 l1 l2 (k o) h1 h2 v
      in
      Act act i k'
    end

let catch0' #a #labs (t1 : tree a (Raise::labs))
                     (t2 : tree a labs)
  : tree a labs
  = handle Raise t1 (fun i k -> t2) (fun x -> Return x)

let catch0'' #a #labs (t1 : tree a (Raise::labs))
                      (t2 : tree a labs)
  : tree a labs
  = handle_with t1
                (fun x -> Return x)
                (function Raise -> (fun i k -> t2)
                        | act -> (fun i k -> Act act i k))

let fmap #a #b #labs (f : a -> b) (t : tree a labs) : tree b labs =
  bind _ _ _ labs t (fun x -> Return (f x))

let join #a #labs (t : tree (tree a labs) labs) : tree a labs =
  bind _ _ _ _ t (fun x -> x)

let app #a #b #labs (t : tree (a -> b) labs) (x:a) : tree b labs =
  fmap (fun f -> f x) t

let frompure #a (t : tree a []) : a =
  match t with
  | Return x -> x

(* Handling Read/Write into the state monad. There is some noise in the
handler, but it's basically interpreting [Read () k] as [\s -> k s s]
and similarly for Write. The only tricky thing is the stacking of [tree]
involved. *)
let catchST2 #a #labs (f : tree a (Read::Write::labs))
  : tree (state -> tree (a & state) labs) labs
  = handle2 Read Write f
            (fun _ k -> Return (fun s -> bind _ _ _ _ (k s)  (fun f -> f s)))
            (fun s k -> Return (fun _ -> bind _ _ _ _ (k ()) (fun f -> f s)))
            (fun x ->   Return (fun s0 -> Return (x, s0)))

(* Since this is a monad, we can apply the internal function and
then collapse the computations to get a more familiar looking catchST *)
let catchST2' #a #labs (f : tree a (Read::Write::labs)) (s0:state)
  : tree (a & state) labs
  = join (app (catchST2 f) s0)

(* And of course into a pure tree if no labels remain *)
let catchST2_emp #a
  (f : tree a (Read::Write::[]))
  : state -> a & state
  = fun s0 -> frompure (catchST2' f s0)

let baseop = o:op{not (Other? o)}

let trlab : o:baseop -> L.eff_label = function
  | Read  -> L.RD
  | Write  -> L.WR
  | Raise -> L.EXN

let trlab' = function
  | L.RD  -> Read
  | L.WR  -> Write
  | L.EXN -> Raise

let trlabs  = List.Tot.map trlab
let trlabs' = List.Tot.map trlab'

let rec lab_corr (l:baseop) (ls:list baseop)
  : Lemma (mem l ls <==> mem (trlab l) (trlabs ls))
          [SMTPat (mem l ls)] // needed for interp_into_lattice_tree below
  = match ls with
    | [] -> ()
    | l1::ls -> lab_corr l ls

(* Tied to the particular tree of Lattice.fst *)

(* no datatype subtyping *)
let fixup : list baseop -> ops = List.Tot.map #baseop #op (fun x -> x)

let rec fixup_corr (l:baseop) (ls:list baseop)
  : Lemma (mem l (fixup ls) <==> mem l ls)
          [SMTPat (mem l (fixup ls))]
  = match ls with
    | [] -> ()
    | l1::ls -> fixup_corr l ls
    
let rec fixup_no_other (l:op{Other? l}) (ls:list baseop)
  : Lemma (mem l (fixup ls) <==> False)
          [SMTPat (mem l (fixup ls))]
  = match ls with
    | [] -> ()
    | l1::ls -> fixup_no_other l ls

// This would be a lot nicer if it was done in L.EFF itself,
// but the termination proof fails since it has no logical payload.
let rec interp_into_lattice_tree #a (#labs:list baseop)
  (t : tree a (fixup labs))
  : L.repr a (trlabs labs)
  = match t with
    | Return x -> L.return _ x
    | Act Read i k ->
      L.bind _ _ _ _ (reify (L.get i))
       (fun x -> WF.axiom1 k x;
              interp_into_lattice_tree #a #labs (k x))
    | Act Write i k ->
      L.bind _ _ _ _ (reify (L.put i))
       (fun x -> WF.axiom1 k x;
              interp_into_lattice_tree #a #labs (k x))
    | Act Raise i k ->
      L.bind _ _ _ _ (reify (L.raise ()))
       (fun x -> WF.axiom1 k x;
              interp_into_lattice_tree #a #labs (k x))

let interp_into_lattice #a (#labs:list baseop)
  (f : unit -> Alg a (fixup labs))
  : Lattice.EFF a (trlabs labs)
  = Lattice.EFF?.reflect (interp_into_lattice_tree (reify (f ())))

// This is rather silly: we reflect and then reify. Maybe define interp_into_lattice
// directly?
let interp_full #a (#labs:list baseop)
  (f : unit -> Alg a (fixup labs))
  : Tot (f:(state -> Tot (option a & state)){Lattice.abides f (Lattice.interp (trlabs labs))})
  = reify (interp_into_lattice #a #labs f)


(* Doing it directly. *)

type sem0 (a:Type) : Type = state -> Tot (either exn a & state)

let abides' (f : sem0 'a) (labs:list baseop) : prop =
    (mem Read  labs \/ (forall s0 s1. fst (f s0) == fst (f s1)))
  /\ (mem Write labs \/ (forall s0. snd (f s0) == s0))
  /\ (mem Raise labs \/ (forall s0. Inr? (fst (f s0))))

type sem (a:Type) (labs : list baseop) = r:(sem0 a){abides' r labs}

let rec interp_sem #a (#labs:list baseop) (t : tree a (fixup labs)) : sem a labs =
  match t with
  | Return x -> fun s0 -> (Inr x, s0)
  | Act Read _ k ->
    (* Needs this trick for termination. Trying to call axiom1 within
     * `r` messes up the refinement about Read. *)
    let k : (s:state -> (r:(tree a (fixup labs)){r << k})) = fun s -> WF.axiom1 k s; k s in
    let r : sem a labs = fun s0 -> interp_sem #a #labs (k s0) s0 in
    r
  | Act Write s k ->
    WF.axiom1 k ();
    fun s0 -> interp_sem #a #labs (k ()) s
  | Act Raise e k -> fun s0 -> (Inl e, s0)

(* Way back: from the pure ALG into the free one, necessarilly giving
a fully normalized tree *)

let interp_from_lattice_tree #a #labs
  (t : L.repr a labs)
  : tree a [Read;Raise;Write] // conservative
  = Act Read () (fun s0 ->
     let (r, s1) = t s0 in
     match r with
     | Some x -> Act Write s1 (fun _ -> Return x)
     | None   -> Act Write s1 (fun _ -> Act Raise (Failure "") (fun x -> match x with))) // empty match

let read_handler (b:Type)
                 (labs:ops)
                 (s0:state)
   : handler_ty_l Read b labs
   = fun _ k -> k s0

let handle_read (a:Type)
                (labs:ops)
                (f:tree a (Read::labs))
                (h:handler_ty_l Read a labs)
   : tree a labs
   = handle Read f h (fun x -> Return x)


let weaken #a #labs l (f:tree a labs) : tree a (l::labs) =
  assert(l::labs == [l]@labs);
  f

let write_handler (a:Type)
                  (labs:ops)
  : handler_ty_l Write a labs
  = fun s k -> handle_read a labs (weaken Read (k())) (read_handler a labs s)


let handle_write (a:Type)
                (labs:ops)
                (f:tree a (Write::labs))
   : tree a labs
   = handle Write f (write_handler a labs) (fun x -> Return x)

let handle_st (a:Type)
              (labs: ops)
              (f:tree a (Write::Read::labs))
              (s0:state)
   : tree a labs
   = handle_read _ _ (handle_write _ _ f) (fun _ k -> k s0)
