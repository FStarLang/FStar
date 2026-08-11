module LatticeEff

open FStar.Tactics.V2
open FStar.List.Tot
open SimpleHeap

(* This example used to layer a labelled exception/state effect over ALL_h.
   The effect declaration and WP index are gone; the labelled heap/exception
   monad is written directly. *)

let coerce #a #b (x:a{a == b}) : b = x

let unreachable #a () : Pure a (requires False) (ensures (fun _ -> False)) = coerce "whatever"

type eff_label =
  | WR
  | EXN

type annot = eff_label -> bool

let interp (l : list eff_label) : annot =
  fun lab -> mem lab l
  
type state = heap

noeq type result (a:Type) =
  | V : v:a -> result a
  | E : e:exn -> result a

type repr0 (a:Type) : Type =
  state -> Tot (result a & state)

let abides #a (f : repr0 a) (ann:annot) : prop =
    (ann WR  = false ==> (forall s0. snd (f s0) == s0))
  /\ (ann EXN = false ==> (forall s0. V? (fst (f s0))))

type repr (a:Type)
          (labs : list eff_label)
  : Type =
  r:(repr0 a){abides r (interp labs)}

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

let return (a:Type) (x:a)
  : repr a [] =
  fun s0 -> (V x, s0)

let return_l (#labs:list eff_label) (a:Type) (x:a)
  : repr a labs =
  fun s0 -> (V x, s0)

let bind (a b : Type)
  (labs1 labs2 : list eff_label)
  (c : repr a labs1)
  (f : (x:a -> repr b labs2))
  : Tot (repr b (labs1@labs2))
  = let r = fun s0 ->
      match c s0 with
      | V x, s1 -> f x s1
      | E e, s1 -> E e, s1
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

let get_heap () : repr heap [] =
  fun h -> (V h, h)

let put_heap (h:heap) : repr unit [WR] =
  fun _ -> (V (), h)

let raise (#a:Type) (e:exn) : repr a [EXN] =
  fun h -> (E e, h)

exception Failure of string

let test0 (x y : int) : repr int [EXN] =
  if x + y > 0
  then raise (Failure "nope")
  else return_l #[EXN] int y

let test1 (x y : int) : repr int [EXN] =
  if x > 0
  then raise (Failure "nope")
  else return_l #[EXN] int (y - x)

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

(* no rollback *)
let catch0 #a #labs (f : repr a (EXN::labs)) (g : repr a labs) : repr a labs =
  fun h0 ->
    match f h0 with
    | V v, h1 -> V v, h1
    | E _, h1 -> g h1

let catch #a #labs (f : unit -> repr a (EXN::labs)) (g : unit -> repr a labs) : repr a labs =
  catch0 (f ()) (g ())

let g #labs () : repr int labs = return_l #labs int 42

let test_catch (f : unit -> repr int [EXN;WR]) : repr int [WR] =
  catch f g
