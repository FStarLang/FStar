module DelimitedReleaseReify

open FStar.DM4F.Heap.IntStoreFixed
open FStar.DM4F.IntStoreFixed
open Rel

module List = FStar.List.Tot

type label =
| Low
| High

type env = id ->  Tot label
(* type iexpr = unit -> IS int *)
(* type bexpr = unit -> IS bool *)
type iexpr = heap -> Tot int
type bexpr = heap -> Tot bool
type prog (i:int) = vl:list id{List.length vl = i /\ List.noRepeats vl} -> ISNull unit

let sel = index

type low_equiv (h : rel heap) (env:env) = (forall (x:id). (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x))

let rel_eq (#a:Type) (#b:eqtype) (r:rel a) ($f:a -> Tot b) : Tot bool =
  match r with | R hl hr -> f hl = f hr

let get_result (#a:Type) ($f:unit -> IS a) (h:heap) : Tot a
= fst (reify (f ()) h)

val iexpr_eq : rel heap -> iexpr -> Tot bool
(* let iexpr_eq r e = rel_eq #heap #int r (get_result e) *)
let iexpr_eq r e = rel_eq #heap #int r e

val bexpr_eq : rel heap -> bexpr -> Tot bool
(* let bexpr_eq r e = rel_eq #heap #bool r (get_result e) *)
let bexpr_eq r e = rel_eq #heap #bool r e


let get_heap (#a:Type) ($f:a -> ISNull unit) (x:a) (h:heap) : Tot heap
= let _, h = reify (f x) h in h

(* val for_all: ('a -> Tot bool) -> list 'a -> Tot bool *)
(* let rec for_all f l = match l with *)
(*     | [] -> true *)
(*     | hd::tl -> if f hd then for_all f tl else false *)

type del_rel (i:int) (env:env) (vl:list id{List.length vl = i}) (ihel:list iexpr) (bhel:list bexpr) (c:prog i) =
  forall h.
    List.noRepeats vl /\
    low_equiv h env /\
    List.for_all (iexpr_eq h) ihel /\
    List.for_all (bexpr_eq h) bhel
      ==> low_equiv (R (get_heap c vl (R?.l h)) (get_heap c vl (R?.r h))) env

reifiable
val test : prog 3
reifiable
let test [x;y;z] =
  let tmp1 = read y in
  let tmp2 = read z in
  write x (tmp1 + tmp2)

val verify_test (x y z: id):
  Lemma begin
    let n = 3 in
    let l = [x ; y ; z] in
    let res h = fst (reify (let tmp1 = read y in let tmp2 = read z in tmp1 + tmp2) h) in
    let env : env = fun r ->
      if r = y || r = z then High
      else Low
    in
    del_rel n env l [res] [] test
  end
let verify_test x y z = ()

reifiable
val sum : prog 6
let sum [y ; x1 ; x2 ; x3 ; x4 ; x5] =
  write y (read x1 + read x2 + read x3 + read x4 + read x5)
  (* upd h y ((sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5)) *)

(* The variant with 4 variables seems to work... *)
(* val verify_sum (x1 x2 x3 x4 x5 y : id): *)
(*   Lemma begin *)
(*     let n = 6 in *)
(*     let l = [x1 ; x2 ; x3 ; x4 ; x5] in *)
(*     let env : env = fun r -> *)
(*       if r = x1 || r = x2 || r = x3 || r = x4 || r = x5 then High else Low *)
(*     in *)
(*     let sum_val h = fst (reify (read x1 + read x2 + read x3 + read x4 + read x5) h) in *)
(*     del_rel n env (y::l) [sum_val] [] sum *)
(*   end *)
(* let verify_sum x1 x2 x3 x4 x5 y = () *)

(* val sum_swap : prog 6 *)
(* let sum_swap [x1;x2;x3;x4;x5;y] h = *)
(*   let tmp1 = sel h x1 in *)
(*   let h = upd h x1 (sel h x2) in *)
(*   let h = upd h x2 (sel h x3) in *)
(*   let h = upd h x3 (sel h x4) in *)
(*   let h = upd h x4 (sel h x5) in *)
(*   let h = upd h x5 tmp1 in *)
(*   upd h y ((sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5)) *)

(* val verify_sum_swap (x1 x2 x3 x4 x5 y : ref int): *)
(*   Lemma *)
(*     (del_rel 6 *)
(*       (fun r -> *)
(*         if r = y then Low *)
(*         else if List.mem r [x1;x2;x3;x4;x5] then High *)
(*         else Low) *)
(*       [x1;x2;x3;x4;x5;y] *)
(*       [fun h -> sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5] *)
(*       [] *)
(*       sum_swap) *)
(* let verify_sum_swap x1 x2 x3 x4 x5 y = () *)

(* val sum_att : prog 6 *)
(* let sum_att [x1;x2;x3;x4;x5;y] h = *)
(*   let tmp1 = sel h x1 in *)
(*   let h = upd h x2 tmp1 in *)
(*   let h = upd h x3 tmp1 in *)
(*   let h = upd h x4 tmp1 in *)
(*   let h = upd h x5 tmp1 in *)
(*   upd h y ((sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5)) *)

(* (\* This does not verify, as expected *\) *)
(* (\* *)
(* val verify_sum_att (x1 x2 x3 x4 x5 y : ref int): *)
(*   Lemma *)
(*     (del_rel 6 *)
(*       (fun r -> *)
(*         if r = y then Low *)
(*         else if List.mem r [x1;x2;x3;x4;x5] then High *)
(*         else Low) *)
(*       [x1;x2;x3;x4;x5;y] *)
(*       [fun h -> sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5] *)
(*       sum_att) *)
(* let verify_sum_att x1 x2 x3 x4 x5 y = () *)
(* *\) *)


(* val wallet : prog 3 *)
(* let wallet [x_h;k;x_l] h = *)
(*   if (sel h x_h >= sel h k) then *)
(*     let h = upd h x_h (sel h x_h - sel h k) in *)
(*     let h = upd h x_l (sel h x_l + sel h k) in *)
(*     h *)
(*   else *)
(*     h *)

(* val verify_wallet (x_h k x_l : ref int): *)
(*   Lemma *)
(*     (del_rel 3 *)
(*       (fun r -> *)
(*         if r = x_h then High *)
(*         else Low) *)
(*       [x_h; k; x_l] *)
(*       [] *)
(*       [fun h -> sel h x_h >= sel h k] *)
(*       wallet) *)
(* let verify_wallet x_h k x_l = () *)

(* // This is not accepted *)
(* //val wallet_attack_loop : prog 4 *)
(* val wallet_attack_loop : vl:list(ref int){List.length vl = 4 /\ List.noRepeats vl} -> h:heap -> GTot heap (decreases (sel h (List.hd vl))) *)
(* let rec wallet_attack_loop [n;x_h;k;x_l] h = *)
(*   if sel h n <= 0 then *)
(*     h *)
(*   else *)
(*     let h = upd h k (pow2 (sel h n - 1)) in *)
(*     let h = wallet [x_h;k;x_l] h in *)
(*     let h = upd h n (sel h n - 1) in *)
(*     wallet_attack_loop [n;x_h;k;x_l] h *)

(* val wallet_attack : prog 4 *)
(* let wallet_attack [n;x_h;k;x_l] h = *)
(*  let h = upd h x_l 0 in *)
(*  wallet_attack_loop [n;x_h;k;x_l] h *)

(* (\* This does not verify, as expected *)
(*    Howver, also does not verify wieht x_h : Low, which should be fine *\) *)
(* (\* *)
(* val verify_wallet_attack (n x_h k x_l : ref int): *)
(*   Lemma *)
(*     (del_rel 4 *)
(*       (fun r -> *)
(*         if r = x_h then High *)
(*         else Low) *)
(*       [n; x_h; k; x_l] *)
(*       [] *)
(*       [fun h -> sel h x_h >= sel h k] *)
(*       wallet_attack) *)
(* let verify_wallet_attack n x_h k x_l = () *)
(* *\) *)
