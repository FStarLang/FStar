module LatticeEff

open FStar.Tactics.V2
open FStar.List.Tot
open SimpleHeap
open ExampleALL
open FStar.All

// Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

let unreachable #a () : Pure a (requires False) (ensures (fun _ -> False)) = coerce "whatever"

type eff_label =
  | WR
  | EXN

type annot = eff_label -> bool

let interp (l : list eff_label) : annot =
  fun lab -> mem lab l
  
type state = heap
type wp a = all_wp_h heap a

(* more generic *)
let wpof2 #a (l : list eff_label) : wp a =
  let i = interp l in
  let wp : wp a = fun p s0 ->
    (forall r s1.
       (i WR  == false ==> s1 == s0) ==>
       (i EXN == false ==> V? r) ==>
       p r s1)
  in
  wp

type repr (a:Type u#aa)
          (labs : list u#0 eff_label)
  : Type u#0
  = unit -> ExALL a (wpof2 labs)

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

let ann_le (ann1 ann2 : annot) : prop =
  forall x. ann1 x ==> ann2 x
  
let return (a:Type) (x:a)
  : repr a []
  =
  fun () -> x

let bind (a b : Type)
  (labs1 labs2 : list eff_label)
  (c : repr a labs1)
  (f : (x:a -> repr b labs2))
  : Tot (repr b (labs1@labs2))
  = fun () -> f (c ()) ()

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

total
reifiable
reflectable
effect {
  EFF (a:Type) (_:list eff_label)
  with {repr; return; bind; subcomp; if_then_else}
}

let lift_pure_eff
 (a:Type)
 (wp : pure_wp a)
 (f : unit -> PURE a wp)
 : Pure (repr a [])
        (requires (wp (fun _ -> True)))
        (ensures (fun _ -> True))
 = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
   fun () -> f ()
 
sub_effect PURE ~> EFF = lift_pure_eff

let get_heap () : EFF heap [] =
  EFF?.reflect (fun () -> ExampleALL.get ())

let raise (#a:Type) (e:exn) : EFF a [EXN] =
  EFF?.reflect (fun () -> ExampleALL.raise_ e)

let test0 (x y : int) : EFF int [EXN] =
  if x + y > 0
  then raise (Failure "nope")
  else y

let test1 (x y : int) : EFF int [EXN] =
  if x > 0
  then raise (Failure "nope")
  else y - x

let sublist_at_self (l1 : list eff_label)
  : Lemma (sublist (l1@l1) l1)
          [SMTPat (l1@l1)]
  = Classical.forall_intro (List.Tot.Properties.append_mem l1 l1)
    
let labpoly #labs (f g : unit -> EFF int labs) : EFF int labs =
  f () + g ()

assume val try_with
  (#a:_) (#wpf:_) (#wpg:_)
  ($f : unit -> ExALL a wpf)
  ($g : unit -> ExALL a wpg)
  : ExALL a (fun p s0 -> wpf (fun r s1 -> match r with
                                  | V _ -> p r s1
                                  | _ -> wpg p s1) s0)

(* no rollback *)
let catch #a #labs (f : unit -> EFF a (EXN::labs)) (g : unit -> EFF a labs) : EFF a labs =
  EFF?.reflect begin
  fun () -> try_with (reify (f ())) (reify (g ()))
  end

let g #labs () : EFF int labs = 42

let test_catch (f : unit -> EFF int [EXN;WR]) : EFF int [WR] =
  catch f g
