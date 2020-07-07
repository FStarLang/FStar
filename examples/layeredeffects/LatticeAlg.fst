module LatticeAlg

(* An algebraic presentation of ALL using action trees. *)

open FStar.Tactics
open FStar.List.Tot
open FStar.Universe
module WF = FStar.WellFounded
module L = Lattice

let coerce #a #b (x:a{a == b}) : b = x

let unreachable (#a:Type u#aa) () : Pure a (requires False) (ensures (fun _ -> False)) =
  coerce #(raise_t string) #a (raise_val "whatever")

type state = int

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
 | Raise -> c_False
 | Other i -> other_inp i

noeq
type repr0 (a:Type u#aa) : Type u#aa =
  | Return : a -> repr0 a
  | Act    : op:op -> i:(op_inp op) -> k:(op_out op -> repr0 a) -> repr0 a

let rec abides #a (labs:list op) (f : repr0 a) : prop =
  begin match f with
  | Act a i k ->
    mem a labs /\ (forall o. (FStar.WellFounded.axiom1 k o; abides labs (k o)))
  | Return _ -> True
  end

type repr (a:Type u#aa)
          (labs : list u#0 op)
  : Type u#aa
  =
  r:(repr0 a){abides labs r}

let rec interp_at (l1 l2 : list op) (l : op)
  : Lemma (mem l (l1@l2) == (mem l l1 || mem l l2))
          [SMTPat (mem l (l1@l2))]
  = match l1 with
    | [] -> ()
    | _::l1 -> interp_at l1 l2 l

let sublist (l1 l2 : list op) = forall x. mem x l1 ==> mem x l2

let rec sublist_at
  (l1 l2 : list op)
  : Lemma (sublist l1 (l1@l2) /\ sublist l2 (l1@l2))
          [SMTPatOr [[SMTPat (sublist l1 (l1@l2))];
                     [SMTPat (sublist l2 (l1@l2))]]]
  = match l1 with
    | [] -> ()
    | _::l1 -> sublist_at l1 l2

let sublist_at_self
  (l : list op)
  : Lemma (sublist l (l@l))
          [SMTPat (sublist l (l@l))]
  = ()
  
let rec abides_sublist_nopat #a (l1 l2 : list op) (c : repr0 a)
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

let abides_sublist #a (l1 l2 : list op) (c : repr0 a)
  : Lemma (requires (abides l1 c) /\ sublist l1 l2)
          (ensures (abides l2 c))
          [SMTPat (abides l2 c); SMTPat (sublist l1 l2)]
  = abides_sublist_nopat l1 l2 c
  
let abides_at_self #a
  (l : list op)
  (c : repr0 a)
  : Lemma (abides (l@l) c <==>  abides l c)
          [SMTPat (abides (l@l) c)]
  = (* Trigger some patterns *)
    assert (sublist l (l@l));
    assert (sublist (l@l) l)

let abides_app #a (l1 l2 : list op) (c : repr0 a)
  : Lemma (requires (abides l1 c \/ abides l2 c))
          (ensures (abides (l1@l2) c))
          [SMTPat (abides (l1@l2) c)]
  = sublist_at l1 l2

let return (a:Type) (x:a)
  : repr a []
  = Return x

let rec bind (a b : Type)
  (labs1 labs2 : list op)
  (c : repr a labs1)
  (f : (x:a -> repr b labs2))
  : Tot (repr b (labs1@labs2))
  = match c with
    | Return x -> f x
    | Act act i k ->
      let k' o : repr b (labs1@labs2) =
        FStar.WellFounded.axiom1 k o;
        bind _ _ _ _ (k o) f
      in
      Act act i k'

let subcomp (a:Type)
  (labs1 labs2 : list op)
  (f : repr a labs1)
  : Pure (repr a labs2)
         (requires (sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let if_then_else
  (a : Type)
  (labs1 labs2 : list op)
  (f : repr a labs1)
  (g : repr a labs2)
  (p : bool)
  : Type
  = repr a (labs1@labs2)

let _get () : repr int [Read] = Act Read () Return

[@@allow_informative_binders]
total // need this for catch!!
reifiable
reflectable
layered_effect {
  EFF : a:Type -> list op  -> Effect
  with
  repr         = repr;
  return       = return;
  bind         = bind;
  subcomp      = subcomp;
  if_then_else = if_then_else
}

let get () : EFF int [Read] =
  EFF?.reflect (_get ())

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

let put (s:state) : EFF unit [Write] =
  EFF?.reflect (Act Write s Return)

let raise #a (e:exn) : EFF a [Raise] =
  EFF?.reflect (Act Raise e Return)

exception Failure of string

let test0 (x y : int) : EFF int [Read; Raise] =
  let z = get () in
  if z < 0 then raise (Failure "error");
  x + y + z

let test1 (x y : int) : EFF int [Raise; Read; Write] =
  let z = get () in
  if x + z > 0
  then raise (Failure "asd")
  else (put 42; y - z)

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
let rec catch0 #a #labs (t1 : repr a (Raise::labs))
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

(* no rollback *)
let catch #a #labs
  (f : unit -> EFF a (Raise::labs))
  (g : unit -> EFF a labs)
  : EFF a labs
=
 EFF?.reflect begin
   catch0 (reify (f ())) (reify (g ()))
 end

let rec _catchST #a #labs (t1 : repr a (Read::Write::labs)) (s0:state) : repr (a & int) labs =
  match t1 with
  | Return v -> Return (v, s0)
  | Act Write s k -> WF.axiom1 k (); _catchST (k ()) s
  | Act Read  _ k -> WF.axiom1 k s0; _catchST (k s0) s0
  | Act act i k ->
     let k' o : repr (a & int) labs =
       WF.axiom1 k o;
       _catchST #a #labs (k o) s0
     in
     Act act i k'

let catchST #a #labs
  (f : unit -> EFF a (Read::Write::labs))
  (s0 : state)
  : EFF (a & state) labs
=
 EFF?.reflect begin
   _catchST (reify (f ())) s0
 end

let g #labs () : EFF int labs = 42  //AR: 07/03: had to hoist after removing smt_reifiablep

let test_catch #labs (f : unit -> EFF int [Raise;Write]) : EFF int [Write] =
  catch f g

let test_catch2 (f : unit -> EFF int [Raise;Raise;Write]) : EFF int [Raise;Write] =
  catch f g

let interp_pure_tree #a (t : repr a []) : Tot a =
  match t with
  | Return x -> x

let interp_pure #a (f : unit -> EFF a []) : Tot a = interp_pure_tree (reify (f ()))

let rec interp_rd_tree #a (t : repr a [Read]) (s:state) : Tot a =
  match t with
  | Return x -> x
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rd_tree (k s) s

let interp_rd #a (f : unit -> EFF a [Read]) (s:state) : Tot a = interp_rd_tree (reify (f ())) s

let rec interp_rdwr_tree #a (t : repr a [Read;Write]) (s:state) : Tot (a & state) =
  match t with
  | Return x -> (x, s)
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rdwr_tree (k s) s
  | Act Write s k ->
    FStar.WellFounded.axiom1 k ();
    interp_rdwr_tree (k ()) s

let interp_rdwr #a (f : unit -> EFF a [Read;Write]) (s:state) : Tot (a & state) = interp_rdwr_tree (reify (f ())) s

let rec interp_rdexn_tree #a (t : repr a [Read;Raise]) (s:state) : Tot (option a) =
  match t with
  | Return x -> Some x
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rdexn_tree (k s) s
  | Act Raise e k ->
    None

let interp_rdexn #a (f : unit -> EFF a [Read;Raise]) (s:state) : Tot (option a) = interp_rdexn_tree (reify (f ())) s

let rec interp_all_tree #a (t : repr a [Read;Write;Raise]) (s:state) : Tot (option a & state) =
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

let interp_all #a (f : unit -> EFF a [Read;Write;Raise]) (s:state) : Tot (option a & state) = interp_all_tree (reify (f ())) s

//let action_input (a:action 'i 'o) = 'i
//let action_output (a:action 'i 'o) = 'o
//
//let handler_ty (a:action _ _) (b:Type) (labs:list eff_label) =
//    action_input a ->
//    (action_output a -> repr b labs) -> repr b labs
//
//let dpi31 (#a:Type) (#b:a->Type) (#c:(x:a->b x->Type)) (t : (x:a & y:b x & c x y)) : a =
//  let (| x, y, z |) = t in x
//
//let dpi32 (#a:Type) (#b:a->Type) (#c:(x:a->b x->Type)) (t : (x:a & y:b x & c x y)) : b (dpi31 t) =
//  let (| x, y, z |) = t in y
//
//let dpi33 (#a:Type) (#b:a->Type) (#c:(x:a->b x->Type)) (t : (x:a & y:b x & c x y)) : c (dpi31 t) (dpi32 t) =
//  let (| x, y, z |) = t in z

let handler_ty_l (o:op) (b:Type) (labs:list op) =
  op_inp o -> (op_out o -> repr b labs) -> repr b labs

  //handler_ty (dpi33 (action_of l)) b labs
  //F* complains this is not a function
  //let (| _, _, a |) = action_of l in
  //handler_ty a b labs

(* A generic handler for a (single) label l, relies on the fact that
we can compare actions for equality, or equivalently map them to their
labels. *)
val handle (#a #b:_) (#labs:_) (o:op)
           (f:repr a (o::labs))
           (h:handler_ty_l o b labs)
           (v: a -> repr b labs)
           : repr b labs
let rec handle #a #b #labs l f h v =
  match f with
  | Return x -> v x
  | Act act i k ->
    if act = l
    then h i (fun o -> WF.axiom1 k o; handle l (k o) h v)
    else begin
      let k' o : repr b labs =
         WF.axiom1 k o;
         handle l (k o) h v
      in
      Act act i k'
    end

(* Easy enough to handle 2 labels at once *)
val handle2 (#a #b:_) (#labs:_) (l1 l2 : op)
           (f:repr a (l1::l2::labs))
           (h1:handler_ty_l l1 b labs)
           (h2:handler_ty_l l2 b labs)
           (v : a -> repr b labs)
           : repr b labs
let rec handle2 #a #b #labs l1 l2 f h1 h2 v =
  match f with
  | Return x -> v x
  | Act act i k ->
    if act = l1
    then h1 i (fun o -> WF.axiom1 k o; handle2 l1 l2 (k o) h1 h2 v)
    else if act = l2
    then h2 i (fun o -> WF.axiom1 k o; handle2 l1 l2 (k o) h1 h2 v)
    else begin
      let k' o : repr b labs =
         WF.axiom1 k o;
         handle2 l1 l2 (k o) h1 h2 v
      in
      Act act i k'
    end

(* All the way *)
val handle_with (#a #b:_) (#labs0 #labs1 : list op)
           (f:repr a labs0)
           (h: (l:op{mem l labs0} -> handler_ty_l l b labs1))
           (v : a -> repr b labs1)
           : repr b labs1
let rec handle_with #a #b #labs0 #labs1 f h v =
  match f with
  | Return x -> v x
  | Act act i k ->
    let k' o : repr b labs1 =
        WF.axiom1 k o;
       handle_with #a #b #labs0 #labs1 (k o) h v
    in
    h act i k'

let catch0' #a #labs (t1 : repr a (Raise::labs))
                     (t2 : repr a labs)
  : repr a labs
  = handle Raise t1 (fun i k -> t2) (fun x -> Return x)

let catch0'' #a #labs (t1 : repr a (Raise::labs))
                      (t2 : repr a labs)
  : repr a labs
  = handle_with t1 (function Raise -> (fun i k -> t2)
                           | act -> (fun i k -> Act act i k))
                   (fun x -> Return x)

let fmap #a #b #labs (f : a -> b) (t : repr a labs) : repr b labs =
  bind _ _ _ labs t (fun x -> Return (f x))

let join #a #labs (t : repr (repr a labs) labs) : repr a labs =
  bind _ _ _ _ t (fun x -> x)

let app #a #b #labs (t : repr (a -> b) labs) (x:a) : repr b labs =
  fmap (fun f -> f x) t

let frompure #a (t : repr a []) : a =
  match t with
  | Return x -> x

// akin to "push_squash" can't be done I think
// val push #a #b #labs (t : a -> repr b labs) : repr (a -> b) labs

#set-options "--print_implicits"

let catchST2_emp #a
  (f : repr a (Read::Write::[]))
  : repr (state -> a & state) []
  = handle2 #a #(state -> a & state)
            #[]
            Read Write f
            (fun _  k -> Return (fun s -> frompure (k s) s))
            (fun s' k -> Return (fun s -> frompure (k ()) s'))
            (fun x -> Return (fun s -> (x,s)))

(* The mysterious version without annotations *)
let catchST2 #a #labs (f : repr a (Read::Write::labs))
  : repr (state -> repr (a & state) labs) labs
  = handle2 Read Write f
            (fun _ k -> Return (fun s -> bind _ _ _ _ (k s)  (fun f -> f s)))
            (fun s k -> Return (fun _ -> bind _ _ _ _ (k ()) (fun f -> f s)))
            (fun x ->   Return (fun s0 -> Return (x, s0)))

(* Fully annotated *)
let catchST2_sensible #a #labs
  (f : repr a (Read::Write::labs))
  : repr (state -> repr (a & state) labs) labs
  = handle2 #a #(state -> repr (a & state) labs)
            #labs
            Read Write f
            (fun _  (k : (state -> repr (state -> repr (a & state) labs) labs)) ->
                       let ff : state -> repr (a & state) labs =
                         fun s0 -> let f : repr (state -> repr (a&state) labs) labs = k s0 in
                                let ff : repr (repr (a&state) labs) labs = app #state #(repr (a&state) labs) #labs f s0 in
                                join ff
                       in
                       Return ff)
            (fun s' k -> bind _ _ _ labs (k ()) (fun f -> Return (fun _ -> f s')))
            (fun x -> Return (fun s0 -> Return (x, s0)))

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
          [SMTPat (mem l ls)] // needed for interp_into_lattice_repr below
  = match ls with
    | [] -> ()
    | l1::ls -> lab_corr l ls

(* Tied to the particular repr of Lattice.fst *)

(* no datatype subtyping *)
let fixup : list baseop -> list op = List.Tot.map #baseop #op (fun x -> x)

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

let rec interp_into_lattice_repr #a (#labs:list baseop)
  (t : repr a (fixup labs))
  : L.repr a (trlabs labs)
  = match t with
    | Return x -> L.return _ x
    | Act Read i k ->
      L.bind _ _ _ _ (reify (L.get i))
       (fun x -> WF.axiom1 k x;
              interp_into_lattice_repr #a #labs (k x))
    | Act Write i k ->
      L.bind _ _ _ _ (reify (L.put i))
       (fun x -> WF.axiom1 k x;
              interp_into_lattice_repr #a #labs (k x))
    | Act Raise i k ->
      L.bind _ _ _ _ (reify (L.raise ()))
       (fun x -> WF.axiom1 k x;
              interp_into_lattice_repr #a #labs (k x))

let interp_into_lattice #a (#labs:list baseop)
  (f : unit -> EFF a (fixup labs))
  : Lattice.EFF a (trlabs labs)
  = Lattice.EFF?.reflect (interp_into_lattice_repr (reify (f ())))

// This is rather silly: we reflect and then reify. Maybe define interp_into_lattice
// directly?
let interp_full #a (#labs:list baseop)
  (f : unit -> EFF a (fixup labs))
  : Tot (f:(state -> Tot (option a & state)){Lattice.abides f (Lattice.interp (trlabs labs))})
  = reify (interp_into_lattice #a #labs f)


(* Doing it directly. *)

type sem0 (a:Type) : Type = state -> Tot (option a & state)

let abides' (f : sem0 'a) (labs:list baseop) : prop =
    (not (mem Read  labs) ==> (forall s0 s1. fst (f s0) == fst (f s1)))
  /\ (not (mem Write labs) ==> (forall s0. snd (f s0) == s0))
  /\ (not (mem Raise labs) ==> (forall s0. Some? (fst (f s0))))

type sem (a:Type) (labs : list baseop) = r:(sem0 a){abides' r labs}

let rec interp_sem #a (#labs:list baseop) (t : repr a (fixup labs)) : sem a labs =
  match t with
  | Return x -> fun s0 -> (Some x, s0)
  | Act Read _ k ->
    (* Needs this trick for termination. Trying to call axiom1 within
     * `r` messes up the refinement about Read. *)
    let k : (s:state -> (r:(repr a (fixup labs)){r << k})) = fun s -> WF.axiom1 k s; k s in
    let r : sem a labs = fun s0 -> interp_sem #a #labs (k s0) s0 in
    r
  | Act Write s k ->
    WF.axiom1 k ();
    fun s0 -> interp_sem #a #labs (k ()) s
  | Act Raise e k -> fun s0 -> (None, s0)

(* Way back: from the pure ALG into the free one, necessarilly giving
a fully normalized tree *)

let interp_from_lattice_repr #a #labs
  (t : L.repr a labs)
  : repr a [Read;Raise;Write] // conservative
  = Act Read () (fun s0 ->
     let (r, s1) = t s0 in
     match r with
     | Some x -> Act Write s1 (fun _ -> Return x)
     | None   -> Act Write s1 (fun _ -> Act Raise (Failure "") (fun _ -> unreachable ())))



let read_handler (b:Type)
                 (labs:list op)
                 (s0:state)
   : handler_ty_l Read b labs
   = fun _ k -> k s0


let handle_read (a:Type)
                (labs:list op)
                (f:repr a (Read::labs))
                (h:handler_ty_l Read a labs)
   : repr a labs
   = handle Read f h (fun x -> Return x)


let weaken #a #labs l (f:repr a labs) : repr a (l::labs) =
  assert(l::labs == [l]@labs);
  f

let write_handler (a:Type)
                  (labs:list op)
  : handler_ty_l Write a labs
  = fun s k -> handle_read a labs (weaken Read (k())) (read_handler a labs s)


let handle_write (a:Type)
                (labs:list op)
                (f:repr a (Write::labs))
   : repr a labs
   = handle Write f (write_handler a labs) (fun x -> Return x)

let handle_st (a:Type)
              (labs: list op)
              (f:repr a (Write::Read::labs))
              (s0:state)
   : repr a labs
   = handle_read _ _ (handle_write _ _ f) (fun _ k -> k s0)
