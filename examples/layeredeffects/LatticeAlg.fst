module LatticeAlg

(* An algebraic presentation of ALL using action trees. *)

open FStar.Tactics
open FStar.List.Tot
open FStar.Universe

module WF = FStar.WellFounded

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

let unreachable (#a:Type u#aa) () : Pure a (requires False) (ensures (fun _ -> False)) =
  coerce #(raise_t string) #a (raise_val "whatever")

type state = int

type eff_label =
  | RD
  | WR
  | EXN

noeq
type action : Type0 -> Type0 -> Type u#1 =
  | Read : action unit state
  | Write : action state unit
  | Raise : action exn c_False
  
noeq
type repr0 (a:Type u#aa) : Type u#(max 1 aa) =
  | Return : a -> repr0 a
  | Act    : #i:_ -> #o:_ -> act:(action i o) -> i -> k:(o -> repr0 a) -> repr0 a
  
type annot = eff_label -> bool

let interp (l : list eff_label) : annot =
  fun lab -> mem lab l

let label_of #ii #oo (a:action ii oo) : eff_label =
 match a with
 | Read -> RD
 | Write -> WR
 | Raise -> EXN
 
let label_ii (l:eff_label) : Type =
 match l with
 | RD -> unit
 | WR -> state
 | EXN -> exn
 
let label_oo (l:eff_label) : Type =
 match l with
 | RD -> state
 | WR -> unit
 | EXN -> c_False

let action_of (l:eff_label) : action (label_ii l) (label_oo l) =
  match l with
  | RD ->  Read
  | WR ->  Write
  | EXN -> Raise

let abides_act #i #o (ann:annot) (a : action i o) : prop =
  ann (label_of a) == true
  
let rec abides #a (ann:annot) (f : repr0 a) : prop =
  begin match f with
  | Act a i k ->
    abides_act ann a /\ (forall o. (FStar.WellFounded.axiom1 k o; abides ann (k o)))
  | Return _ -> True
  end

type repr (a:Type u#aa)
          (labs : list u#0 eff_label) // #2074
  : Type u#(max 1 aa)
  =
  r:(repr0 a){abides (interp labs) r}

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

let rec abides_sublist_nopat #a (l1 l2 : list eff_label) (c : repr0 a)
  : Lemma (requires (abides (interp l1) c) /\ sublist l1 l2)
          (ensures (abides (interp l2) c))
  = match c with
    | Return _ -> ()
    | Act a i k -> 
      let sub o : Lemma (abides (interp l2) (k o)) =
        FStar.WellFounded.axiom1 k o;
        abides_sublist_nopat l1 l2 (k o)
      in
      Classical.forall_intro sub
      
let abides_sublist #a (l1 l2 : list eff_label) (c : repr0 a)
  : Lemma (requires (abides (interp l1) c) /\ sublist l1 l2)
          (ensures (abides (interp l2) c))
          [SMTPat (abides (interp l2) c); SMTPat (sublist l1 l2)]
  = abides_sublist_nopat l1 l2 c

let abides_app #a (l1 l2 : list eff_label) (c : repr0 a)
  : Lemma (requires (abides (interp l1) c \/ abides (interp l2) c))
          (ensures (abides (interp (l1@l2)) c))
          [SMTPat (abides (interp (l1@l2)) c)]
  = Classical.move_requires (abides_sublist_nopat l1 (l1@l2)) c;
    Classical.move_requires (abides_sublist_nopat l2 (l1@l2)) c

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
    | Act act i k -> 
      let k' o : repr b (labs1@labs2) =
        FStar.WellFounded.axiom1 k o;
        bind _ _ _ _ (k o) f
      in
      Act act i k'

let subcomp (a:Type)
  (labs1 labs2 : list eff_label)
  (f : repr a labs1)
  : Pure (repr a labs2)
         (requires (sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let if_then_else
  (a : Type)
  (labs1 labs2 : list eff_label)
  (f : repr a labs1)
  (g : repr a labs2)
  (p : bool)
  : Type
  = repr a (labs1@labs2)

let _get () : repr int [RD] = Act Read () Return
  
[@@allow_informative_binders]
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

let get () : EFF int [RD] =
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

let put (s:state) : EFF unit [WR] =
  EFF?.reflect (Act Write s Return)

let raise #a (e:exn) : EFF a [EXN] =
  EFF?.reflect (Act Raise e Return)

exception Failure of string

let test0 (x y : int) : EFF int [RD; EXN] =
  let z = get () in
  if z < 0 then raise (Failure "error");
  x + y + z

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

(* no rollback *)
let catch #a #labs
  (f : unit -> EFF a (EXN::labs))
  (g : unit -> EFF a labs)
  : EFF a labs
=
 EFF?.reflect begin
   catch0 (reify (f ())) (reify (g ()))
 end

let rec _catchST #a #labs (t1 : repr a (RD::WR::labs)) (s0:state) : repr (a & int) labs =
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
  (f : unit -> EFF a (RD::WR::labs))
  (s0 : state)
  : EFF (a & state) labs
=
 EFF?.reflect begin
   _catchST (reify (f ())) s0
 end

let g #labs () : EFF int labs = 42  //AR: 07/03: had to hoist after removing smt_reifiablep

let test_catch #labs (f : unit -> EFF int [EXN;WR]) : EFF int [WR] =
  catch f g

let test_catch2 (f : unit -> EFF int [EXN;EXN;WR]) : EFF int [EXN;WR] =
  catch f g

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

let rec interp_rdexn_tree #a (t : repr a [RD;EXN]) (s:state) : Tot (option a) =
  match t with
  | Return x -> Some x
  | Act Read _ k ->
    FStar.WellFounded.axiom1 k s;
    interp_rdexn_tree (k s) s
  | Act Raise e k ->
    None

let interp_rdexn #a (f : unit -> EFF a [RD;EXN]) (s:state) : Tot (option a) = interp_rdexn_tree (reify (f ())) s

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
  
let handler_ty_l (l:eff_label) (b:Type) (labs:list eff_label) =
  label_ii l -> (label_oo l -> repr b labs) -> repr b labs

  //handler_ty (dpi33 (action_of l)) b labs
  //F* complains this is not a function
  //let (| _, _, a |) = action_of l in
  //handler_ty a b labs

(* A generic handler for a (single) label l, relies on the fact that
we can compare actions for equality, or equivalently map them to their
labels. *)
val handle (#a #b:_) (#labs:_) (l:eff_label)
           (f:repr a (l::labs))
           (h:handler_ty_l l b labs)
           (v: a -> repr b labs)
           : repr b labs
let rec handle #a #b #labs l f h v =
  match f with
  | Return x -> v x
  | Act act i k ->
    if label_of act = l
    then h i (fun o -> WF.axiom1 k o; handle l (k o) h v)
    else begin
      let k' o : repr b labs =
         WF.axiom1 k o;
         handle l (k o) h v
      in
      Act act i k'
    end

(* Easy enough to handle 2 labels at once *)
val handle2 (#a #b:_) (#labs:_) (l1 l2 :eff_label)
           (f:repr a (l1::l2::labs))
           (h1:handler_ty_l l1 b labs)
           (h2:handler_ty_l l2 b labs)
           (v : a -> repr b labs)
           : repr b labs
let rec handle2 #a #b #labs l1 l2 f h1 h2 v =
  match f with
  | Return x -> v x
  | Act act i k ->
    if label_of act = l1
    then h1 i (fun o -> WF.axiom1 k o; handle2 l1 l2 (k o) h1 h2 v)
    else if label_of act = l2
    then h2 i (fun o -> WF.axiom1 k o; handle2 l1 l2 (k o) h1 h2 v)
    else begin
      let k' o : repr b labs =
         WF.axiom1 k o;
         handle2 l1 l2 (k o) h1 h2 v
      in
      Act act i k'
    end

let catch0' #a #labs (t1 : repr a (EXN::labs))
                     (t2 : repr a labs)
  : repr a labs
  = handle EXN t1 (fun i k -> t2) (fun x -> Return x)
    
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
  (f : repr a (RD::WR::[]))
  : repr (state -> a & state) []
  = handle2 #a #(state -> a & state)
            #[]
            RD WR f
            (fun _  k ->  Return (fun s -> frompure (k s) s))
            (fun s' k ->  Return (fun s -> frompure (k ()) s'))
            (fun x -> Return (fun s -> (x,s)))

// not sure if this definable as-is
// should read https://www.fceia.unr.edu.ar/~mauro/pubs/haskell2019.pdf
let catchST2 #a #labs
  (f : repr a (RD::WR::labs))
  : repr (state -> a & state) labs
  = handle2 #a #(state -> a & state)
            #labs
            RD WR f
            (fun _  k -> admit ()) // what to do here?
            (fun s' k -> bind _ _ _ labs (k ()) (fun f -> Return (fun _ -> f s')))
            (fun x -> Return (fun s0 -> (x, s0)))

module L = Lattice

let trlab = function
  | RD  -> L.RD
  | WR  -> L.WR
  | EXN -> L.EXN
  
let trlab' = function
  | L.RD  -> RD
  | L.WR  -> WR
  | L.EXN -> EXN

let trlabs  = List.Tot.map trlab
let trlabs' = List.Tot.map trlab'

let rec lab_corr (l:eff_label) (ls:list eff_label)
  : Lemma (mem l ls <==> mem (trlab l) (trlabs ls))
          [SMTPat (mem l ls)] // needed for interp_into_lattice_repr below
  = match ls with
    | [] -> ()
    | l1::ls -> lab_corr l ls

(* Tied to the particular repr of Lattice.fst *)

let rec interp_into_lattice_repr #a #labs
  (t : repr a labs)
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

let interp_into_lattice #a #labs
  (f : unit -> EFF a labs)
  : Lattice.EFF a (trlabs labs)
  = Lattice.EFF?.reflect (interp_into_lattice_repr (reify (f ())))

let interp_full #a #labs
  (f : unit -> EFF a labs)
  : Tot (f:(state -> Tot (option a & state)){Lattice.abides f (Lattice.interp (trlabs labs))})
  = reify (interp_into_lattice #a #labs f)


(* Doing it directly. *)

type sem0 (a:Type) : Type = state -> Tot (option a & state)

let abides' (f : sem0 'a) (ann:annot) : prop =
    (ann RD  = false ==> (forall s0 s1. fst (f s0) == fst (f s1)))
  /\ (ann WR  = false ==> (forall s0. snd (f s0) == s0))
  /\ (ann EXN = false ==> (forall s0. Some? (fst (f s0))))

type sem (a:Type) (labs : list eff_label) = r:(sem0 a){abides' r (interp labs)}

let rec interp_sem #a #labs (t : repr a labs) : sem a labs =
  match t with
  | Return x -> fun s0 -> (Some x, s0)
  | Act Read _ k -> 
    (* Needs this trick for termination. Trying to call axiom1 within
     * `r` messes up the refinement about RD. *)
    let k : (s:state -> (r:repr0 a{r << k})) = fun s -> WF.axiom1 k s; k s in
    let r : sem a labs = fun s0 -> interp_sem #a #labs (k s0) s0 in
    r
  | Act Write s k ->
    WF.axiom1 k ();
    fun s0 -> interp_sem #a #labs (k ()) s
  | Act Raise e k -> fun s0 -> (None, s0)

(* Way back: from the pure ALG into the free one, necessarilly given
a fully normalized tree *)

let interp_from_lattice_repr #a #labs
  (t : L.repr a labs)
  : repr a [RD;EXN;WR] // conservative
  = Act Read () (fun s0 ->
     let (r, s1) = t s0 in
     match r with
     | Some x -> Act Write s1 (fun _ -> Return x)
     | None   -> Act Write s1 (fun _ -> Act Raise (Failure "") (fun _ -> unreachable ())))
