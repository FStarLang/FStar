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
val sum4 : prog 4
let sum4 [y ; x1 ; x2 ; x3 ] =
  write y (read x1 + read x2 + read x3 )

val verify_sum4 (x1 x2 x3 y : id):
  Lemma begin
    let n = 4  in
    let l = [x1 ; x2 ; x3 ] in
    assert_norm (List.length l == n - 1) ;
    let env : env = fun r ->
      (* expanding the definition of mem here seems faster to verify *)
      if List.mem r l then High else Low
    in
    let sum4_val h = fst (reify (read x1 + read x2 + read x3 ) h) in
    del_rel n env (y::l) [sum4_val] [] sum4
  end
let verify_sum4 x1 x2 x3 y = ()


reifiable
val sum : prog 6
let sum [y ; x1 ; x2 ; x3 ; x4 ; x5] =
  write y (read x1 + read x2 + read x3 + read x4 + read x5)

(* The variant with 4 variables seems to work... *)
(* This works with either more z3rlimit or putting the scrutinee of the match in a separate let at the smt-encoding level *)
val verify_sum (x1 x2 x3 x4 x5 y : id):
  Lemma begin
    let n = 6 in
    let l = [x1 ; x2 ; x3 ; x4 ; x5] in
    let env : env = fun r ->
      (* expanding the definition of mem here seems faster to verify *)
      if List.mem r l then High else Low
    in
    let sum_val h = fst (reify (read x1 + read x2 + read x3 + read x4 + read x5) h) in
    del_rel n env (y::l) [sum_val] [] sum
  end
let verify_sum x1 x2 x3 x4 x5 y = ()


(* Does not verify !!! *)
(* #set-options "--z3rlimit 100" *)

(* reifiable *)
(* val sum_swap : prog 6 *)
(* let sum_swap [y ; x1 ; x2 ; x3 ; x4 ; x5] = *)
(*   let tmp1 = read x1 in *)
(*   write x1 (read x2) ; *)
(*   write x2 (read x3) ; *)
(*   write x3 (read x4) ; *)
(*   write x4 (read x5) ; *)
(*   write x5 tmp1 ; *)
(*   write y (read x1 + read x2 + read x3 + read x4 + read x5) *)

(* val verify_sum_swap (x1 x2 x3 x4 x5 y : id): *)
(*   Lemma begin *)
(*     let n = 6 in *)
(*     let l = [x1;x2;x3;x4;x5] in *)
(*     let env : env = fun r -> *)
(*       if List.mem r l then High *)
(*       else Low *)
(*     in *)
(*     let sum_val h = fst (reify (read x1 + read x2 + read x3 + read x4 + read x5) h) in *)
(*     del_rel n env (y::l) [sum_val] [] sum_swap *)
(*   end *)
(* let verify_sum_swap x1 x2 x3 x4 x5 y = () *)

(* #set-options "--z3rlimit 5" *)

reifiable
val sum_att : prog 6
let sum_att [y ; x1 ; x2 ; x3 ; x4 ; x5] =
  let tmp1 = read x1 in
  write x2 tmp1 ;
  write x3 tmp1 ;
  write x4 tmp1 ;
  write x5 tmp1 ;
  write y ((read x1 + read x2 + read x3 + read x4 + read x5))

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


#set-options "--z3rlimit 10"
reifiable
val wallet : prog 3
let wallet [x_h ; k ; x_l] =
  if (read x_h >= read k) then
    write x_h (read x_h - read k) ;
    write x_l (read x_l + read k)

val verify_wallet (x_h k x_l : id):
  Lemma begin
    let n = 3 in
    let env : env = fun r -> if r = x_h then High else Low in
    let l = [x_h ; k ; x_l] in
    let b h = fst (reify (read x_h >= read k) h) in
    del_rel n env l [] [b] wallet
  end
let verify_wallet x_h k x_l = ()

#set-options "--z3rlimit 5"

(* Not accepted yet *)

(* reifiable *)
(* val wallet_attack_loop : *)
(*   h0:heap -> *)
(*   n:id -> *)
(*   vl:list id{List.length vl = 4 /\ List.noRepeats vl} -> *)
(*   IntStore unit (requires (fun h -> h == h0 /\ List.hd vl == n)) *)
(*     (ensures (fun _ _ _ -> True)) *)
(*     (decreases (sel h0 n)) *)
(* let rec wallet_attack_loop h0 n l = *)
(*   assert (List.length l = 4) ; *)
(*   match l with *)
(*   | [n ; x_h ; k ; x_l] -> *)
(*     let x = read n in *)
(*     assert (sel h0 n == x) ; *)
(*     if x > 0 then *)
(*       write k (pow2 (x - 1)) ; *)
(*       wallet [x_h;k;x_l] ; *)
(*       write n (x - 1) ; *)
(*       let h = IS?.get () in *)
(*       assert (sel h n = x - 1) ; *)
(*       wallet_attack_loop h n l *)
(*   | _ -> () *)

(* val wallet_attack : prog 4 *)
(* let wallet_attack [n;x_h;k;x_l] h = *)
(*  let h = upd h x_l 0 in *)
(*  wallet_attack_loop [n;x_h;k;x_l] h *)

(* (\* This does not verify, as expected *)
(*    Howver, also does not verify with x_h : Low, which should be fine *\) *)
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
