module Lattice

open FStar.Tactics.V2
open FStar.List.Tot

(* This example used to present a layered effect.  The effect declaration has
   been removed; the examples below use the underlying labelled state/exception
   monad directly. *)

let coerce #a #b (x:a{a == b}) : b = x

let unreachable #a () : Pure a (requires False) (ensures (fun _ -> False)) = coerce "whatever"

type eff_label =
  | RD
  | WR
  | EXN

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

type repr (a:Type)
          (labs : list eff_label)
  : Type =
  r:(repr0 a){abides r (interp labs)}

let return (a:Type) (x:a)
  : repr a [] =
  fun s0 -> (Some x, s0)

let return_l (#labs:list eff_label) (a:Type) (x:a)
  : repr a labs =
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

let (let!) #a #b #labs1 #labs2 (m : repr a labs1) (f : a -> repr b labs2)
  : repr b (labs1@labs2)
  = bind a b labs1 labs2 m f

let weaken (a:Type)
  (labs1 labs2 : list eff_label)
  (f : repr a labs1)
  : Pure (repr a labs2)
         (requires (sublist labs1 labs2))
         (ensures (fun _ -> True))
  = f

let get () : repr int [RD] =
  fun s0 -> (Some s0, s0)
  
let put (s:state) : repr unit [WR] =
  fun _ -> (Some (), s)

let raise #a () : repr a [EXN] =
  fun s0 -> (None, s0)

let test0 (x y : int) : repr int [RD; EXN] =
  let! z = get () in
  if x + z > 0
  then raise ()
  else return_l #[EXN] int (y - z)

let test1 (x y : int) : repr int [RD; EXN; WR] =
  let! z = get () in
  if x + z > 0
  then weaken int [EXN] [EXN; WR] (raise ())
  else let! _ = put 42 in
       return_l #[] int (y - z)

let sublist_at_self (l1 : list eff_label)
  : Lemma (sublist (l1@l1) l1)
          [SMTPat (l1@l1)]
  = Classical.forall_intro (List.Tot.Properties.append_mem l1 l1)

let labpoly #labs (f g : unit -> repr int labs) : repr int labs =
  sublist_at_self labs;
  weaken int (labs@labs) labs
    (let! x = f () in
     let! y = g () in
     return int (x + y))

let catch0 #a #labs (f:repr a (EXN::labs)) (g:repr a labs)
  : repr a labs
  = fun s0 ->
    let r0 : option a & state = f s0 in
    let r1 : option a & state =
      match r0 with
      | (Some v, s1) -> (Some v, s1)
      | (None, s1) -> g s1
      | _ -> unreachable ()
    in
    r1

let catch #a #labs
  (f : unit -> repr a (EXN::labs))
  (g : unit -> repr a labs)
  : repr a labs
= catch0 (f ()) (g ())

// TODO: haskell-like runST.
// strong update with index on state type(s)?

let g #labs () : repr int labs = return_l #labs int 42

let test_catch #labs (f : unit -> repr int [EXN;WR]) : repr int [WR] =
  catch f g

let test_catch2 (f : unit -> repr int [EXN;EXN;WR]) : repr int [EXN;WR] =
  catch f g
