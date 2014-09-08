module Unit1
open Prims.PURE
open Prims.ALL

let partial_app f x y = 
  let g = f x in
  g y

let unit_id x = ()
let unit_pattern () = ()

val assert_0_eq_0: unit -> Tot unit
let assert_0_eq_0 x = assert (0==0)

val assert_0_eq_1: unit -> Tot unit
let assert_0_eq_1 () = assert (0==1) //should fail

type zero = x:int{x==0}
val z: unit -> Tot zero
let z x = 0

val list_zero_to_int_assert : list zero -> Tot int
let list_zero_to_int_assert l = match l with
  | [] -> 0
  | hd::tl -> assert (hd==0); hd

val list_zero_to_zero : list zero -> Tot zero
let list_zero_to_zero l = match l with
  | [] -> 0
  | hd::tl -> hd

val hd_int_inexhaustive : x:list int -> int
let hd_int_inexhaustive l = match l with
  | hd::_ -> hd //should fail

val hd_int_impure : x:list int -> int
let hd_int_impure l = match l with
  | hd::_ -> hd
  | [] -> failwith "Empty list"

val hd_int_impure_default_case : x:list int -> int
let hd_int_impure_default_case l = match l with
  | hd::_ -> hd
  | _ -> failwith "Empty list"

val hd_int_pure : x:list int{b2t (is_Cons x)} -> Tot int
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

val tabs_id_pure_annot_eq : 'a:Type -> x:'a -> Pure 'a True (fun y => y==x)
let tabs_id_pure_annot_eq ('a:Type) x = x

let tabs_id ('a:Type) (x:'a) = x

val id_pure_annot_eq : x:'a -> Pure 'a True (fun y => y==x)
let id_pure_annot_eq x = x

val id_all_annot_eq: x:'a -> All 'a (fun h => True) (fun h0 y h1 => b2t (is_V y) /\ h0==h1 /\ x==(V.v y)) (SomeRefs EmptySet)
let id_all_annot_eq x = x

val hd: list 'a -> 'a
let hd = function
  | x::_ -> x
  | _ -> failwith "empty list"

val hd_pure: l:list 'a{b2t (is_Cons l)} -> Tot 'a
let hd_pure l = match l with
  | x::_ -> x

val dup_pure: x:'a -> Tot ('a * 'a)
let dup_pure x = (x,x)

val dup_pure_eq: x:'a -> Pure ('a * 'a) True (fun y => MkTuple2._1 y==MkTuple2._2 y)
let dup_pure_eq x = (x,x)

(* val test_st : m:mode -> State unit *)
(*                             (fun 'p h0 => (forall h1. SelHeap h1 moderef==SelHeap h0 moderef ==> 'p () h1)) *)
(* let test_st (m:mode) = *)
(*   let cur = rd "hello" in *)
(*   let z = f 0 in *)
(*   ST.write moderef cur *)


(* val test_match: m:mode *)
(*              -> Wys unit (Requires (fun cur => (if cur.p_or_s==Sec then cur.prins==m.prins else Subset cur.prins m.prins))) *)
(*                          (Ensures _ (fun m1 a m2 => True)) *)
(* let test_match (m:mode) = *)
(*   let cur = get_mode () in *)
(*   (match cur.p_or_s with *)
(*    | Sec -> assert (cur.prins == m.prins) *)
(*    | _ -> assert (Subset cur.prins m.prins)) *)


(* val mem: x:'a -> l:list 'a -> bool *)
(* let rec mem x l = match l with *)
(*   | [] -> false *)
(*   | hd::tl -> x=hd || mem x tl *)

(* val hd: x:list 'a{b2t (is_Cons x)} -> Tot 'a *)
(* let hd = function *)
(*   | hd::_ -> hd *)



    
    

