module LatticeEff

open FStar.Tactics
open FStar.List.Tot
open FStar.All
module H = FStar.Heap

#set-options "--print_universes --print_implicits --print_effect_args"

// GM: Force a type equality by SMT
let coerce #a #b (x:a{a == b}) : b = x

let unreachable #a () : Pure a (requires False) (ensures (fun _ -> False)) = coerce "whatever"

type eff_label =
  // GM: Can we do this one? ALL's WPs are unary and this is a
  // relational property.
  // | RD
  | WR
  //| DIV
  | EXN

type annot = eff_label -> bool

let interp (l : list eff_label) : annot =
  fun lab -> mem lab l
  
type state = H.heap
type wp a = all_wp_h H.heap a

// boring, exponential
//let wpof1 #a (l : list eff_label) : all_wp_h H.heap a =
//  let i = interp l in
//  match i ST, i EXN with
//  | false, false ->
//    fun p s0 -> forall x. p (V x) s0
//  | true , false ->
//    fun p s0 -> forall x s1. p (V x) s1
//  | false, true ->
//    fun p s0 -> forall r. p r s0
//  | true,  true ->
//    fun p s0 -> forall r s1. p r s1

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
          (labs : list u#0 eff_label) // #2074
  : Type u#0
  = unit -> ALL a (wpof2 labs)

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

[@@allow_informative_binders]
total
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
 = fun () -> f ()
 
sub_effect PURE ~> EFF = lift_pure_eff

let get () : EFF H.heap [] =
  EFF?.reflect (fun () -> get ())

let (!) #a (r:ref a) : EFF a [] =
  EFF?.reflect (fun () -> !r)
  
let (:=) #a (r:ref a) (v:a) : EFF unit [WR] =
  EFF?.reflect (fun () -> r := v)

(* GM: The refinement is clearly crap, just trying to get a typeable
put-like thing here. *)
let put (s:state{forall s1. heap_rel s1 s}) : EFF unit [WR] =
  EFF?.reflect (fun () -> gst_put s)

let raise #a (e:exn) : EFF a [EXN] =
  EFF?.reflect (fun () -> raise e)

let test0 (r:ref int) (x y : int) : EFF int [EXN] =
  let z = !r in
  if x + z > 0
  then raise (Failure "nope")
  else y - z

let test1 (r:ref int) (x y : int) : EFF int [EXN; WR] =
  let z = !r in
  if x + z > 0
  then raise (Failure "nope")
  else (r := 42; y - z)


let sublist_at_self (l1 : list eff_label)
  : Lemma (sublist (l1@l1) l1)
          [SMTPat (l1@l1)]
  = Classical.forall_intro (List.Tot.Properties.append_mem l1 l1)
    
let labpoly #labs (f g : unit -> EFF int labs) : EFF int labs =
  f () + g ()

assume val try_with
  (#a:_) (#wpf:_) (#wpg:_)
  ($f : unit -> ALL a wpf)
  ($g : unit -> ALL a wpg)
  : ALL a (fun p s0 -> wpf (fun r s1 -> match r with
                                  | V _ -> p r s1
                                  | _ -> wpg p s1) s0)

(* no rollback *)
(* GM: NB: this looks incredibly simple, but took like an hour to get right
 * when the WP of try_with wasn't exactly what was expected :-) *)
let catch #a #labs (f : unit -> EFF a (EXN::labs)) (g : unit -> EFF a labs) : EFF a labs =
  EFF?.reflect begin
  fun () -> try_with (reify (f ())) (reify (g ()))
  end

let g #labs () : EFF int labs = 42

let test_catch (f : unit -> EFF int [EXN;WR]) : EFF int [WR] =
  catch f g
