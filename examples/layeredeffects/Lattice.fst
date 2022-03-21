module Lattice

open FStar.Tactics
open FStar.List.Tot

#set-options "--print_universes --print_implicits --print_effect_args"

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

let unreachable #a () : Pure a (requires False) (ensures (fun _ -> False)) = coerce "whatever"

type eff_label =
  | RD
  | WR
  //| DIV
  | EXN

// DONE: split ST into READ/WRITE with relational prop on abides
//       ^ this was incredibly easy

// DONE  add specs (see LatticeSpec.fst)

type annot = eff_label -> bool

type state = int

type repr0 (a:Type u#aa) : Type u#aa =
  state -> Tot (option a & state)

let abides #a (f : repr0 a) (ann:annot) : prop =
    (ann RD  = false ==> (forall s0 s1. fst (f s0) == fst (f s1)))
  /\ (ann WR  = false ==> (forall s0. snd (f s0) == s0))
  /\ (ann EXN = false ==> (forall s0. Some? (fst (f s0))))

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

type repr (a:Type u#aa)
          (labs : list u#0 eff_label) // #2074
  : Type u#aa
  =
  r:(repr0 a){abides r (interp labs)}

let ann_le (ann1 ann2 : annot) : prop =
  forall x. ann1 x ==> ann2 x
  
let return (a:Type) (x:a)
  : repr a []
  =
  fun s0 -> (Some x, s0)

let bind (a b : Type)
  (labs1 labs2 : list eff_label)
  (c : repr a labs1)
  (f : (x:a -> repr b labs2))
  : Tot (repr b (labs1@labs2))
  = let r =
      fun s0 -> match c s0 with
             | Some x, s1 -> f x s1
             | None, s1 -> None, s1
    in
    r

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
 = fun s0 -> (Some (f ()), s0)
 
sub_effect PURE ~> EFF = lift_pure_eff

let get () : EFF int [RD] =
  EFF?.reflect (fun s0 -> (Some s0, s0))
  
let put (s:state) : EFF unit [WR] =
  EFF?.reflect (fun _ -> (Some (), s))

let raise #a () : EFF a [EXN] =
  EFF?.reflect (fun s0 -> (None, s0))

let test0 (x y : int) : EFF int [RD; EXN] =
  let z = get () in
  if x + z > 0
  then raise ()
  else y - z

let test1 (x y : int) : EFF int [EXN; RD; WR] =
  let z = get () in
  if x + z > 0
  then raise ()
  else (put 42; y - z)

let sublist_at_self (l1 : list eff_label)
  : Lemma (sublist (l1@l1) l1)
          [SMTPat (l1@l1)]
  = Classical.forall_intro (List.Tot.Properties.append_mem l1 l1)

let labpoly #labs (f g : unit -> EFF int labs) : EFF int labs =
  f () + g ()

(* no rollback *)
let catch #a #labs
  (f : unit -> EFF a (EXN::labs))
  (g : unit -> EFF a labs)
  : EFF a labs
= EFF?.reflect begin
  let reif : repr a labs =
    fun s0 ->
      let reif_r : repr a (EXN::labs) = reify (f ()) in
      let r0 : option a & state = reif_r s0 in
      let r1 : option a & state =
        match r0 with
        | (Some v, s1) -> (Some v, s1)
        | (None, s1) -> reify (g ()) s1
        | _ -> unreachable ()
      in
      r1
  in
  reif
  end

// TODO: haskell-like runST.
// strong update with index on state type(s)?

//AR: 07/03: this g was inlined earlier, but then the proofs were relying on smt_reifiable
let g #labs () : EFF int labs = 42

let test_catch #labs (f : unit -> EFF int [EXN;WR]) : EFF int [WR] =
  catch f g

let test_catch2 (f : unit -> EFF int [EXN;EXN;WR]) : EFF int [EXN;WR] =
  catch f g
