module Hello

(* val a1: unit -> PURE.Tot unit *)
(* let a1 () = assert (0==0) *)

(* val a2: unit -> PURE.Tot unit *)
(* let a2 () = assert (0==1) //should fail *)

type zero = x:int{x==0}
(* val lz_to_i : list zero -> PURE.Tot int *)
(* let lz_to_i l = match l with *)
(*   | [] -> 0 *)
(*   | hd::tl -> assert (hd==0); hd *)

val z: unit -> PURE.Tot zero
let z () = 0

(* val lz_to_z : list zero -> PURE.Tot zero *)
(* let lz_to_z l = match l with *)
(*   | [] -> 0 *)
(*   | hd::tl -> hd *)

(* val hd_int : x:list int{b2t (is_Cons x)} -> PURE.Tot int *)
(* let hd_int l = match l with *)
(*   | hd::_ -> hd *)

(* val hd: x:list 'a{b2t (is_Cons x)} -> PURE.Tot 'a *)
(* let hd = function *)
(*   | hd::_ -> hd *)



                
                 

