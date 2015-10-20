(*--build-config
    options:--admit_fsi FStar.Set --verify_module Unit1;
    other-files:ext.fst set.fsi heap.fst st.fst list.fst string.fst
--*)
module Unit1

type t =
  | A
  | B
let rec comp x y = comp x y

let rec foo x =
  let rec bar y = bar y in
  foo (bar x)

let partial_app f x y =
  let g = f x in
  g y

let unit_id x = ()
let unit_pattern () = ()

let assert_0_eq_0 x = assert (0=0)

type zero = x:int{x=0}
val z: unit -> Tot zero
let z x = 0

val list_zero_to_int_assert : list zero -> Tot int
let list_zero_to_int_assert l = match l with
  | [] -> 0
  | hd::tl -> assert (hd=0); hd

val list_zero_to_zero : list zero -> Tot zero
let list_zero_to_zero l = match l with
  | [] -> 0
  | hd::tl -> hd

(* val hd_int_impure : x:list int -> int *)
let hd_int_impure l = match l with
  | hd::_ -> hd
  | [] -> failwith "Empty list"

val hd_int_impure_default_case : x:list int -> int
let hd_int_impure_default_case l = match l with
  | hd::_ -> hd
  | _ -> failwith "Empty list"

val hd_int_pure : x:list int{is_Cons x} -> Tot int
let hd_int_pure l = match l with
  | hd::_ -> hd

val square_is_nat: x:int -> Tot nat
let square_is_nat x = x * x

(* logic val infer_nat: x:int -> Tot nat *)
let infer_nat x = if x < 0 then -x else x

val check_nat: x:int -> Tot nat
let check_nat x = infer_nat x

val assert_nat: x:int -> unit
let assert_nat x =
  let assert_nat_y = infer_nat x in
  assert (assert_nat_y >= 0)

let id x = x
let church_true x y = x
let church_false x y = y

val pure_id_annot : 'a -> Tot 'a
let pure_id_annot x = x

val ml_id_annot : 'a -> 'a
let ml_id_annot x = x

val tabs_id_pure_annot_eq : a:Type -> x:a -> Pure a True (fun y -> b2t (y=x))
let tabs_id_pure_annot_eq (a:Type) x = x

let tabs_id (a:Type) (x:'a) = x

val id_pure_annot_eq : x:'a -> Pure 'a True (fun y -> b2t (y=x))
let id_pure_annot_eq x = x

val id_all_annot_eq: x:'a -> All 'a (fun h -> True) (fun h0 y h1 -> is_V y /\ h0=h1 /\ x=(V.v y))
let id_all_annot_eq x = x

val hd: list 'a -> 'a
let hd = function
  | x::_ -> x
  | _ -> failwith "empty list"

val hd_pure: l:list 'a{is_Cons l} -> Tot 'a
let hd_pure l = match l with
  | x::_ -> x

val hd_pure_alt: x:list 'a{is_Cons x} -> Tot 'a
let hd_pure_alt = function
  | hd::_ -> hd

val dup_pure: x:'a -> Tot ('a * 'a)
let dup_pure x = (x,x)

val dup_pure_eq: x:'a -> Pure ('a * 'a) True
                              (fun y -> b2t (MkTuple2._1 y=MkTuple2._2 y))
let dup_pure_eq x = (x,x)

(* the programs below are equivalent---see the refinement of the result in tc.fs/Exp_app case. *)
assume val get_0: unit -> ST int (fun _h -> True) (fun _h i _h' -> b2t (i=0))
assume val get_1: unit -> ST int (fun _h -> True) (fun _h i _h' -> b2t (i=1))
val get_false: unit -> ST bool (fun _h -> True) (fun _h b _h' -> b2t (b=false))
let get_false u = get_0 () > get_1 ()

val get_false_ANF: unit -> ST bool (fun _h -> True) (fun _h b _h' -> b2t (b=false))
let get_false_ANF u =
  let x = get_0 () in
  let y = get_1 () in
  x > y

type record = {f:option int}
val record_f_exhaustive: record -> Tot int
let record_f_exhaustive r = match r.f with (* should be able to prove that the pattern below is exhaustive for r.f *)
  | Some i -> i
  | None -> 0



val repeat : int -> nat -> Tot int
let rec repeat n count =
  match count with
  | 0 -> 0
  | _ -> repeat n (count-1)


type inat =
  | O
  | S : inat -> inat

val minus : inat -> inat -> Tot inat
let rec minus n m : inat =
  match n, m with
  | O   , _    -> O
  | S _ , O    -> n
  | S n', S m' -> minus n' m'

val ackermann: m:nat -> n:nat -> Tot nat
let rec ackermann m n =
  if m=0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))

assume type contents : Type -> Type
type seq (a:Type) =
  | Seq : c:contents a
          -> start_i:nat
          -> end_i:nat{end_i >= start_i}
          -> seq a
type message = seq char
let slength s = Seq.end_i s - Seq.start_i s
assume val impure: m:message -> ST message
                                 (requires (fun h -> True))
                                 (ensures (fun h0 n h1 -> slength n = slength m))
assume val lm_corr: l:nat -> m:message{slength m=l} -> int
val unsafe_slice: message -> i:nat -> j:nat{i<=j} -> Tot message
let unsafe_slice (Seq c _ _) n m = Seq c n m
val test_impure: l:nat{l > 0} -> m:message{slength m=l} -> int
let test_impure l m =  lm_corr (l - 1) (unsafe_slice (impure m) 1 l)


type mlist =
  | N
  | C of (nat * mlist)

val zero_list: l:mlist -> Tot bool
let rec zero_list l = match l with
  | N -> true
  | C (n, l') -> n = 0 && zero_list l'

(* this is saying: either l is a zerolist, or if first element of l is not 0, then its tail is a zero list *)
type pre (l:mlist) = (forall (n:nat) l'. ((l = C(n, l') /\ not (n = 0)) ==> zero_list l') /\ ((l = C(0, l') \/ l = N) ==> zero_list l))

(* this function promises to return a zero list *)
val do_ok: l:mlist -> Pure mlist (requires (pre l)) (ensures (fun l -> zero_list l))
let do_ok l = match l with
  | N -> N
  | C(n, l') -> if n = 0 then l else C(0, l')

val short_circuit1: x:option int{is_Some x /\ Some.v x = 0} -> nat
let short_circuit1 x = Some.v x

(* TESTING skolem variables for lambdas *)

val apply : (int -> Tot int) -> int -> Tot int
let apply f x = f x

let test_skolem_app (x:int) =
  assert (apply (fun x -> x) 0 = 0)

let test_skolem_match (x:int) =
  match apply (fun x -> x) 0  with
  | 0 -> 0

logic type T = (apply (fun x -> x) 0 = 1)

val test_skolem_refinement: x:int{T} -> Tot unit
let test_skolem_refinement x = assert false

val find: f:('a -> Tot bool) -> list 'a -> Tot (option (x:'a{f x}))
let rec find f = function
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

val test_skolem_let: x:int -> Tot (b:bool{b ==> x=0})
let test_skolem_let x =
  let found = find (fun y -> x=0) [x] in
  is_Some found

(* TESTING implicit binding of conditionally total function arguments *)
assume val id_wrap1: x:int -> Pure int (requires True) (ensures (fun y -> x=y))
assume val id_wrap2: x:int -> Pure int (requires True) (ensures (fun y -> x=y))

val use_id_wrap: l:int -> Pure int (requires True) (ensures (fun m -> m = l))
let use_id_wrap l = id_wrap1 (id_wrap2 l)

val xy_y : int -> int -> Tot int
let xy_y x y = y

val idl: l:list int -> Pure (list int) (requires True) (ensures (fun m -> l=m))
let rec idl l = match l with
  | [] -> []
  | hd::tl -> [(fun x -> xy_y hd x) hd] @ idl tl

assume val st_id_wrap: x:int -> ST int (requires (fun h -> True)) (ensures (fun h0 y h1 -> x=y))
val st_f: l:int -> ST int (requires (fun h -> True)) (ensures (fun h0 m h1 -> m = l))
let st_f l = st_id_wrap (st_id_wrap l)

(* Auto-induction *)
val factorial: nat -> Tot nat
let rec factorial n = if n = 0 then 1 else n * factorial (n - 1)

val factorial_is_positive: x:nat -> Lemma (ensures (factorial x > 0))
let rec factorial_is_positive x = match x with
  | 0 -> ()
  | n -> factorial_is_positive (n - 1) //NS:used to be:  by_induction_on e factorial_is_positive; but that seems to require a very inefficient axiom on the nat ordering

val length: list 'a -> Tot int
let rec length = function
  | [] -> 0
  | _::tl -> 1 + length tl

val length_is_nat: l:list int -> Lemma (ensures (length l >= 0))
let rec length_is_nat l = by_induction_on l length_is_nat

val poly_length_is_nat: l:list 'a -> Lemma (ensures (length l >= 0))
let rec poly_length_is_nat 'a l = by_induction_on l (poly_length_is_nat #'a)


val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
let rec map f = function
  | [] -> []
  | hd::tl -> f hd::map f tl
let plus_one x = x + 1
let test_map1 () =
  let l = [0;1;2] in
  let g = map plus_one l in
  assert (g = [1;2;3])

let test_map2 x = assert (map (fun x -> x + 1) [0;1;2] = [1;2;3])


assume val test_pred: #a:Type -> a -> a -> Tot bool
assume val test_pred_lemma_1: #a:Type -> x:a -> Lemma (forall (bad:a). test_pred x bad)

let test_pred_lemma_2    (a:Type) = qintro #a #(fun x -> forall (y:a). test_pred x y) (test_pred_lemma_1 #a)
let test_pred_lemma_unif (a:Type) = qintro (test_pred_lemma_1 #a)

val test_pred_lemma_2' : #a:Type -> Lemma (ensures (forall (x:a) (y:a). test_pred x y))
let test_pred_lemma_2'  (a:Type) = qintro #a #(fun x -> forall (y:a). test_pred x y) (test_pred_lemma_1 #a)

val test_pred_lemma_unif' : #a:Type -> Lemma (ensures (forall (x:a) (y:a). test_pred x y))
let test_pred_lemma_unif'  (a:Type) = qintro (test_pred_lemma_1 #a)

val even: nat -> Tot bool
val odd: nat -> Tot bool
let rec even x = if x=0 then true else odd (x - 1)
and odd x = if x=0 then false else even (x - 1)

let test_even1 = assert (even 4 = true)
let test_even2 = assert (even 5 = false)

let test_odd1 = assert (odd 4 = false)
let test_odd2 = assert (odd 5 = true)

assume val f_eq: #a:Type -> #p:(a -> Type) -> =arg:(u:unit -> Pure a (requires True) (ensures p)) -> Tot (x:a{p x})
assume val g_eq_c: unit -> Pure int (requires True) (ensures (fun x -> x >= 0))
let h_test_eq :nat = f_eq g_eq_c

module TestParser
assume type tint : int -> Type

type t1 = x:int{x >= 0} -> tint x
type t2 = x:int -> res:tint x
type t3 = (a:Type) -> (x:int) -> result:list a{result=[] /\ x=18}
type t4 = x:nat & y:nat{y > x}
type t4' = (x:nat) & y:nat{y > x}
type t4'' = (x:nat) & (y:nat{y > x}) //parentheses are not significant
type t5 = x:int{x=0} * y:int
//type t5' = x:int{x=0} * tint x
//parses but fails name-binding; x is not in scope in the 2nd component
type t6 = (int * int) -> int
type t7 = int * int -> int

type t8 = x:int * int -> int
//type t8' = x:int * int -> tint x //x is not in scope to the right of the arrow
type t8' = x:(int * int) -> tint (fst x)

type t9 = x:int & tint x -> int
type t9' = y:(x:int & tint x) -> tint (dfst y)

type ta = (x:int) -> (y:int -> tint y) -> tint x
type tb = x:int -> (y:int -> tint y) -> tint x
type tc = x:int -> f:(y:int -> Tot int) -> tint (f 0)

let f1 (x: y:int &  z:tint y{z=z /\ y=0}) = x
let f2 (x: y:int *  z:tint 0{z=z}) = x
let f3 (x: y:int -> z:tint y{z=z /\ y=0})= x
let f4 (#a:Type) (l:list a) (#x:int) (v:tint x) = l
let f5 (l:list int) (v:tint 0) = f4 l v

type s0 (x:int) (y:int -> Tot int) = tint (y 0)
type s1 (x: y:int &  z:tint y{z=z /\ y=0}) = tint (dfst x)
type s2 (x: y:int *  z:tint 0{z=z}) = tint (fst x)
type s3 (x: y:int -> z:tint y{z=z /\ y=0}) = tint ((fun x -> 0) x)

module MoreUnificationTests
type t : int -> Type
assume val f: int -> Tot int
assume val g: #x:int -> t (f x) -> Tot unit
let h1 (x: t (f 0)) = g x
let h2 (x: t ((fun x -> f (x - 1)) 1)) = g x


module WPsAndTriples
type as_requires (#a:Type) (wp:PureWP a)  = wp (fun x -> True)
type as_ensures  (#a:Type) (wlp:PureWP a) (x:a) = ~ (wlp (fun y -> ~(y=x)))
assume val as_Pure: #a:Type -> #b:(a -> Type)
          -> #wp:(x:a -> PureWP (b x))
          -> #wlp:(x:a -> PureWP (b x))
          -> =f:(x:a -> PURE (b x) (wp x) (wlp x))
          -> x:a -> Pure (b x) (as_requires (wp x))
                               (as_ensures (wlp x))

val f : x:int -> PURE int (fun 'p -> x > 0 /\ 'p (x + 1)) (fun 'p -> x > 0 ==> 'p (x + 1))
let f x = assert (x > 0); x + 1

val h : #req:(int -> Type) -> #ens:(int -> int -> Type) -> =f:(x:int -> Pure int (req x) (ens x)) -> y:int -> Pure int (req y) (ens y)
let h f x = f x

val g : x:int -> Pure int (x > 0) (fun y -> y == x + 1)
let g = h (as_Pure f)

module WPsAndTriples_ST
open FStar.Heap
type as_requires (#a:Type) (wp:STWP_h heap a)  = wp (fun x h -> True)
type as_ensures  (#a:Type) (wlp:STWP_h heap a) (h0:heap) (x:a) (h1:heap) = ~ (wlp (fun y h1' -> y<>x \/ h1<>h1') h0)
assume val as_ST: #a:Type -> #b:(a -> Type)
          -> #wp:(x:a -> STWP_h heap (b x))
          -> #wlp:(x:a -> STWP_h heap (b x))
          -> =f:(x:a -> STATE (b x) (wp x) (wlp x))
          -> x:a -> ST (b x) (as_requires (wp x))
                             (as_ensures (wlp x))

let f x = !x * !x

val h : #req:(ref int -> heap -> Type)
     -> #ens:(ref int -> heap -> int -> heap -> Type)
     -> =f:(x:ref int -> ST int (req x) (ens x))
     -> y:ref int -> ST int (req y) (ens y)
let h f x = f x

val g : x:ref int -> ST int (fun h -> True) (fun h0 y h1 -> h0=h1 /\ y >= 0)
let g = h (as_ST f)

module RefinementInference
type erased : Type -> Type
assume val reveal: erased 'a -> GTot 'a
assume val consHd : #a:Type -> l:list a{is_Cons l} -> Tot a
assume val elift1_p : #a:Type -> #b:Type -> #p:(a->Type) -> =f:(=x:a{p x} ->Tot b) -> r:erased a{p (reveal r) } -> Tot (erased b)

val ghostConsHd : a:Type -> l:erased (list a){is_Cons (reveal l)} -> Tot (erased a)
let ghostConsHd (a:Type) l = elift1_p consHd l

(*** PROJECTORS ***)
module Projectors1
type t = 
  | T : x:int -> y:nat -> t

val f : t:t -> Tot int
let f t = t.x

type s = 
  | S : x:bool -> y:nat -> s

let g s : bool = s.x

type u = {x:char; y:int} 
let h u : char = u.x

type v = 
  | V : field1:int -> field2:nat -> v

module Projectors2
open Projectors1
let f x = x.field1
