module Unit1.Basic
open FStar.All
open FStar.BaseTypes

type t =
  | A
  | B
let rec comp x y : Dv unit = comp x y

let rec foo x : Dv unit =
  let rec bar y : Dv unit = bar y in
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

let one = match (fun x -> x) with | f -> f 1

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

val hd_int_impure_default_case : x:list int -> ML int
let hd_int_impure_default_case l = match l with
  | hd::_ -> hd
  | _ -> failwith "Empty list"

val hd_int_pure : x:list int{Cons? x} -> Tot int
let hd_int_pure l = match l with
  | hd::_ -> hd

val square_is_nat: x:int -> Tot nat
let square_is_nat x = op_Multiply x x

(* val infer_nat: x:int -> Tot nat *)
let infer_nat x = if x < 0 then -x else x

val check_nat: x:int -> Tot nat
let check_nat x = infer_nat x

val assert_nat: x:int -> ML unit
let assert_nat x =
  let assert_nat_y = infer_nat x in
  assert (assert_nat_y >= 0)

let id x = x
let church_true x y = x
let church_false x y = y

val pure_id_annot : 'a -> Tot 'a
let pure_id_annot x = x

val ml_id_annot : 'a -> ML 'a
let ml_id_annot x = x

val tabs_id_pure_annot_eq : a:eqtype -> x:a -> Pure a True (fun y -> b2t (y=x))
let tabs_id_pure_annot_eq a x = x

let tabs_id (a:Type) (x:'a) = x

val id_pure_annot_eq : #a:eqtype -> x:a -> Pure a True (fun y -> b2t (y=x))
let id_pure_annot_eq #a x = x

val id_all_annot_eq: #a:eqtype -> x:a -> All a (fun h -> True) (fun h0 y h1 -> V? y /\ h0==h1 /\ x=(V?.v y))
let id_all_annot_eq #a x = x

val hd: list 'a -> ML 'a
let hd = function
  | x::_ -> x
  | _ -> failwith "empty list"

val hd_pure: l:list 'a{Cons? l} -> Tot 'a
let hd_pure l = match l with
  | x::_ -> x

val hd_pure_alt: x:list 'a{Cons? x} -> Tot 'a
let hd_pure_alt = function
  | hd::_ -> hd

val dup_pure: x:'a -> Tot ('a * 'a)
let dup_pure x = (x,x)

val dup_pure_eq: #a:eqtype -> x:a -> Pure (a * a) True
                              (fun y -> b2t (Mktuple2?._1 y=Mktuple2?._2 y))
let dup_pure_eq #a x = (x,x)

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

assume type contents : Type0 -> Type0
noeq type seq (a:Type0) =
  | Seq : c:contents a
          -> start_i:nat
          -> end_i:nat{end_i >= start_i}
          -> seq a
type message = seq char
let slength s = Seq?.end_i s - Seq?.start_i s
assume val impure: m:message -> ST message
                                 (requires (fun h -> True))
                                 (ensures (fun h0 n h1 -> slength n = slength m))
assume val lm_corr: l:nat -> m:message{slength m=l} -> ML int
val unsafe_slice: message -> i:nat -> j:nat{i<=j} -> Tot message
let unsafe_slice (Seq c _ _) n m = Seq c n m
val test_impure: l:nat{l > 0} -> m:message{slength m=l} -> ML int
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

val short_circuit1: x:option int{Some? x /\ Some?.v x = 0} -> Tot nat
let short_circuit1 x = Some?.v x

(* TESTING skolem variables for lambdas *)

val apply : (int -> Tot int) -> int -> Tot int
let apply f x = f x

let test_skolem_app (x:int) =
  assert (apply (fun x -> x) 0 = 0)

let test_skolem_match (x:int) =
  match apply (fun x -> x) 0  with
  | 0 -> 0

type _T = (apply (fun x -> x) 0 = 1)

val test_skolem_refinement: x:int{_T} -> Tot unit
let test_skolem_refinement x = assert false

val find: f:('a -> Tot bool) -> list 'a -> Tot (option (x:'a{f x}))
let rec find f = function
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

val test_skolem_let: x:int -> Tot (b:bool{b ==> x=0})
let test_skolem_let x =
  let found = find (fun y -> x=0) [x] in
  Some? found

(* TESTING implicit binding of conditionally total function arguments *)
assume val id_wrap1: x:int -> Pure int (requires True) (ensures (fun y -> x=y))
assume val id_wrap2: x:int -> Pure int (requires True) (ensures (fun y -> x=y))

val use_id_wrap: l:int -> Pure int (requires True) (ensures (fun m -> m = l))
let use_id_wrap l = id_wrap1 (id_wrap2 l)

val xy_y : int -> int -> Tot int
let xy_y x y = y

open FStar.List.Tot
val idl: l:list int -> Pure (list int) (requires True) (ensures (fun m -> l=m))
let rec idl l = match l with
  | [] -> []
  | hd::tl -> [(fun x -> xy_y hd x) hd] @ idl tl

assume val st_id_wrap: x:int -> ST int (requires (fun h -> True)) (ensures (fun h0 y h1 -> x=y))
val st_f: l:int -> ST int (requires (fun h -> True)) (ensures (fun h0 m h1 -> m = l))
let st_f l = st_id_wrap (st_id_wrap l)

(* Auto-induction *)
val factorial: nat -> Tot nat
let rec factorial n = if n = 0 then 1 else op_Multiply n (factorial (n - 1))

val factorial_is_positive: x:nat -> Lemma (ensures (factorial x > 0))
let rec factorial_is_positive x = match x with
  | 0 -> ()
  | n -> factorial_is_positive (n - 1) //NS:used to be:  by_induction_on e factorial_is_positive; but that seems to require a very inefficient axiom on the nat ordering

val length: list 'a -> Tot int
let rec length = function
  | [] -> 0
  | _::tl -> 1 + length tl

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

let test_pred_lemma_2    (a:Type) = FStar.Classical.forall_intro #a #(fun x -> forall (y:a). test_pred x y) (test_pred_lemma_1 #a)
let test_pred_lemma_unif (a:Type) = FStar.Classical.forall_intro (test_pred_lemma_1 #a)

val test_pred_lemma_2' : #a:Type -> Lemma (ensures (forall (x:a) (y:a). test_pred x y))
let test_pred_lemma_2'  (#a:Type) = FStar.Classical.forall_intro #a #(fun x -> forall (y:a). test_pred x y) (test_pred_lemma_1 #a)

val test_pred_lemma_unif' : #a:Type -> Lemma (ensures (forall (x:a) (y:a). test_pred x y))
let test_pred_lemma_unif'  (#a:Type) = FStar.Classical.forall_intro (test_pred_lemma_1 #a)

val even: nat -> Tot bool
val odd: nat -> Tot bool
let rec even x = if x=0 then true else odd (x - 1)
and odd x = if x=0 then false else even (x - 1)

let test_even1 = assert (even 4 = true)
let test_even2 = assert (even 5 = false)

let test_odd1 = assert (odd 4 = false)
let test_odd2 = assert (odd 5 = true)

assume val f_eq: #a:Type -> #p:(a -> Type) -> $arg:(u:unit -> Pure a (requires True) (ensures p)) -> Tot (x:a{p x})
assume val g_eq_c: u:unit -> Pure int (requires True) (ensures (fun x -> x >= 0))
let h_test_eq : nat = f_eq #int g_eq_c //NS: 05.28: Needed to add the #int


(** AR: 05/14: adding testcases for now deprecated logic qualifier **)
val logic_test0: int -> GTot Type0
let logic_test0 n = True \/ True

val logic_test1 : Type0
let logic_test1 = forall (_:unit). True

val logic_test2:
	#a : Type ->
	#b : Type ->
	#c : Type ->
	g : (b -> c -> Tot Type0) ->
	f : (a -> b -> Tot Type0) ->
	Tot (a -> c -> Tot Type0)
let logic_test2 #a #b #c g f = fun x z -> exists (y : b). True

val logic_test3:
	#a : Type ->
	#b : Type ->
	#c : Type ->
	g : (b -> c -> Tot Type0) ->
	f : (a -> b -> Tot Type0) ->
	Lemma (ensures ( forall (x : a) (z : c).
		((logic_test2 #a #b #c g f) x z) <==> (exists (y : b). True)
	))
let logic_test3 #a #b #c g f = ()

val logic_test4: a:Type -> Tot Type0
let logic_test4 a = exists (x : a). True

val logic_test5: a:Type -> Lemma (ensures ((logic_test4 a) <==> (exists (x : a). True)))
let logic_test5 a = ()

(*
 * #1078
 *)
unfold let language_1078 = string -> GTot Type

noeq type star_1078 (l: string -> GTot Type) : language_1078 =
  | Star_nil : star_1078 l ""
  | Star_append : s1:string -> s2:string ->
      l s1 -> star_1078 l s2 -> star_1078 l s1

(*
 * #1169
 *)
[@(expect_failure [189])]
type boom_1169 =
| B_1169 : forall (x: int). boom_1169
