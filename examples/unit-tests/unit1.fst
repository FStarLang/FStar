module Unit1

(* val assert_0_eq_0: unit -> PURE.Tot unit *)
(* let assert_0_eq_0 () = assert (0==0) *)

(* val assert_0_eq_1: unit -> PURE.Tot unit *)
(* let assert_0_eq_1 () = assert (0==1) //should fail *)

(* type zero = x:int{x==0} *)
(* val z: unit -> PURE.Tot zero *)
(* let z () = 0 *)

(* val list_zero_to_int_assert : list zero -> PURE.Tot int *)
(* let list_zero_to_int_assert l = match l with *)
(*   | [] -> 0 *)
(*   | hd::tl -> assert (hd==0); hd *)

(* val list_zero_to_zero : list zero -> PURE.Tot zero *)
(* let list_zero_to_zero l = match l with *)
(*   | [] -> 0 *)
(*   | hd::tl -> hd *)

(* val hd_int_inexhaustive : x:list int -> int *)
(* let hd_int_inexhaustive l = match l with *)
(*   | hd::_ -> hd //should fail *)

(* val hd_int_impure : x:list int -> int *)
(* let hd_int_impure l = match l with *)
(*   | hd::_ -> hd *)
(*   | [] -> failwith "Empty list" *)

(* val hd_int_impure_default_case : x:list int -> int *)
(* let hd_int_impure_default_case l = match l with *)
(*   | hd::_ -> hd *)
(*   | _ -> failwith "Empty list" *)

(* val hd_int_pure : x:list int{b2t (is_Cons x)} -> PURE.Tot int *)
(* let hd_int_pure l = match l with *)
(*   | hd::_ -> hd *)

(* val square_is_nat: x:int -> PURE.Tot nat *)
(* let square_is_nat x = x * x *)

let infer_nat x = if x < 0 then -x else x

(* val check_nat: x:int -> PURE.Tot nat *)
(* let check_nat x = infer_nat x *)

val assert_nat: x:int -> unit
let assert_nat x = 
  let assert_nat_y = infer_nat x in 
  assert (assert_nat_y >= 0)

(* let id x = x *)
(* let church_true x y = x *)
(* let church_false x y = y *)

(* val pure_id_annot : 'a -> PURE.Tot 'a *)
(* let pure_id_annot x = x *)

(* val ml_id_annot : 'a -> 'a *)
(* let ml_id_annot x = x *)

(* val tabs_id_pure_annot_eq : 'a:Type -> x:'a -> PURE.Pure 'a True (fun y => y==x) *)
(* let tabs_id_pure_annot_eq 'a x = x *)

(* val id_pure_annot_eq : x:'a -> PURE.Pure 'a True (fun y => y==x) *)
(* let id_pure_annot_eq x = x *)

(* val id_all_annot_eq: x:'a -> ALL.All 'a (fun h => True) (fun h0 y h1 => b2t (is_V y) /\ h0==h1 /\ x==(V.v y)) (SomeRefs EmptySet) *)
(* let id_all_annot_eq x = x *)

(* val hd: list 'a -> 'a *)
(* let hd = function *)
(*   | x::_ -> x *)
(*   | _ -> failwith "empty list" *)

(* val hd_pure: l:list 'a{b2t (is_Cons l)} -> PURE.Tot 'a *)
(* let hd_pure l = match l with *)
(*   | x::_ -> x *)

(* val dup_pure: x:'a -> PURE.Tot ('a * 'a) *)
(* let dup_pure x = (x,x) *)

(* val dup_pure_eq: x:'a -> PURE.Pure ('a * 'a) True (fun y => MkTuple2._1 y==MkTuple2._2 y)o *)
(* let dup_pure_eq x = (x,x) *)

(* (\* (\\* val mem: x:'a -> l:list 'a -> bool *\\) *\) *)
(* (\* (\\* let rec mem x l = match l with  *\\) *\) *)
(* (\* (\\*   | [] -> false *\\) *\) *)
(* (\* (\\*   | hd::tl -> x=hd || mem x tl *\\) *\) *)

(* (\* (\\* (\\\* val hd: x:list 'a{b2t (is_Cons x)} -> PURE.Tot 'a *\\\) *\\) *\) *)
(* (\* (\\* (\\\* let hd = function *\\\) *\\) *\) *)
(* (\* (\\* (\\\*   | hd::_ -> hd *\\\) *\\) *\) *)



                
                 

