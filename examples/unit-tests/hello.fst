module UnitTests

val assert_0_eq_0: unit -> PURE.Tot unit
let assert_0_eq_0 () = assert (0==0)

val assert_0_eq_1: unit -> PURE.Tot unit
let assert_0_eq_1 () = assert (0==1) //should fail

type zero = x:int{x==0}
val z: unit -> PURE.Tot zero
let z () = 0

val list_zero_to_int_assert : list zero -> PURE.Tot int
let list_zero_to_int_assert l = match l with
  | [] -> 0
  | hd::tl -> assert (hd==0); hd

val list_zero_to_zero : list zero -> PURE.Tot zero
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

val hd_int_pure : x:list int{b2t (is_Cons x)} -> PURE.Tot int
let hd_int_pure l = match l with
  | hd::_ -> hd

val square_is_nat: x:int -> PURE.Tot nat
let square_is_nat x = x * x

let infer_nat x = if x < 0 then -x else x

val check_nat: x:int -> PURE.Tot nat
let check_nat x = infer_nat x 


(* val hd: x:list 'a{b2t (is_Cons x)} -> PURE.Tot 'a *)
(* let hd = function *)
(*   | hd::_ -> hd *)



                
                 

