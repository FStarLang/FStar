module Delimited_Release

open FStar.Heap
open Rel

type label =
| Low
| High

type env = ref int ->  Tot label
type iexpr = heap -> GTot int 
type bexpr = heap -> GTot bool
type prog (i:int) = vl:list(ref int){List.Tot.length vl = i /\ List.Tot.noRepeats vl} -> heap -> GTot heap

type low_equiv (h : rel heap) (env:env) = (forall (x:ref int). (Low? (env x) ==> sel (R?.l h) x = sel (R?.r h) x))

val iexpr_eq : rel heap -> iexpr -> GTot bool
let iexpr_eq (R hl hr) e = e hl = e hr

val bexpr_eq : rel heap -> bexpr -> GTot bool
let bexpr_eq (R hl hr) e = e hl = e hr

val g_for_all: ('a -> GTot bool) -> list 'a -> GTot bool
let rec g_for_all f l = match l with
    | [] -> true
    | hd::tl -> if f hd then g_for_all f tl else false


type del_rel (i:int) (env:env) (vl : list (ref int){List.Tot.length vl = i}) (ihel : list iexpr) (bhel : list bexpr) (c:prog i) =
  forall h.
    (List.Tot.noRepeats vl /\
    low_equiv h env /\ 
    g_for_all (iexpr_eq h) ihel /\
    g_for_all (bexpr_eq h) bhel) 
      ==> low_equiv (R (c vl (R?.l h)) (c vl (R?.r h))) env

val test : prog 3
let test [x;y;z] h = 
  let tmp1 = sel h y in 
  let tmp2 = sel h z in 
  upd h x (tmp1 + tmp2)

val verify_test (x y z: ref int): 
  Lemma 
    (del_rel 3
      (fun r ->
        if r = x then Low
        else if r = y then High
        else if r = z then High
        else Low) 
      [x;y;z] 
      [fun h -> sel h y + sel h z] 
      []
      test)
let verify_test x y z = ()


val sum : prog 6
let sum [x1;x2;x3;x4;x5;y] h = 
  upd h y ((sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5))

val verify_sum (x1 x2 x3 x4 x5 y : ref int): 
  Lemma 
    (del_rel 6
      (fun r ->
        if r = y then Low
        else if List.Tot.mem r [x1;x2;x3;x4;x5] then High
        else Low) 
      [x1;x2;x3;x4;x5;y] 
      [fun h -> sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5] 
      []
      sum)
let verify_sum x1 x2 x3 x4 x5 y = ()

val sum_swap : prog 6
let sum_swap [x1;x2;x3;x4;x5;y] h = 
  let tmp1 = sel h x1 in 
  let h = upd h x1 (sel h x2) in 
  let h = upd h x2 (sel h x3) in 
  let h = upd h x3 (sel h x4) in 
  let h = upd h x4 (sel h x5) in 
  let h = upd h x5 tmp1 in 
  upd h y ((sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5))
  
val verify_sum_swap (x1 x2 x3 x4 x5 y : ref int): 
  Lemma 
    (del_rel 6
      (fun r ->
        if r = y then Low
        else if List.Tot.mem r [x1;x2;x3;x4;x5] then High
        else Low) 
      [x1;x2;x3;x4;x5;y] 
      [fun h -> sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5] 
      []
      sum_swap)
let verify_sum_swap x1 x2 x3 x4 x5 y = ()

val sum_att : prog 6
let sum_att [x1;x2;x3;x4;x5;y] h = 
  let tmp1 = sel h x1 in 
  let h = upd h x2 tmp1 in 
  let h = upd h x3 tmp1 in 
  let h = upd h x4 tmp1 in 
  let h = upd h x5 tmp1 in 
  upd h y ((sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5))

(* This does not verify, as expected *)
(*
val verify_sum_att (x1 x2 x3 x4 x5 y : ref int): 
  Lemma 
    (del_rel 6
      (fun r ->
        if r = y then Low
        else if List.Tot.mem r [x1;x2;x3;x4;x5] then High
        else Low) 
      [x1;x2;x3;x4;x5;y] 
      [fun h -> sel h x1 + sel h x2 + sel h x3 + sel h x4 + sel h x5] 
      sum_att)
let verify_sum_att x1 x2 x3 x4 x5 y = ()
*)


val wallet : prog 3
let wallet [x_h;k;x_l] h = 
  if (sel h x_h >= sel h k) then
    let h = upd h x_h (sel h x_h - sel h k) in 
    let h = upd h x_l (sel h x_l + sel h k) in 
    h 
  else
    h

val verify_wallet (x_h k x_l : ref int): 
  Lemma 
    (del_rel 3
      (fun r ->
        if r = x_h then High
        else Low) 
      [x_h; k; x_l] 
      []
      [fun h -> sel h x_h >= sel h k]
      wallet)
let verify_wallet x_h k x_l = ()

// This is not accepted
//val wallet_attack_loop : prog 4
val wallet_attack_loop : vl:list(ref int){List.Tot.length vl = 4 /\ List.Tot.noRepeats vl} -> h:heap -> GTot heap (decreases (sel h (List.Tot.hd vl)))
let rec wallet_attack_loop [n;x_h;k;x_l] h = 
  if sel h n <= 0 then 
    h 
  else 
    let h = upd h k (pow2 (sel h n - 1)) in 
    let h = wallet [x_h;k;x_l] h in
    let h = upd h n (sel h n - 1) in 
    wallet_attack_loop [n;x_h;k;x_l] h

val wallet_attack : prog 4
let wallet_attack [n;x_h;k;x_l] h = 
 let h = upd h x_l 0 in 
 wallet_attack_loop [n;x_h;k;x_l] h

(* This does not verify, as expected 
   Howver, also does not verify wieht x_h : Low, which should be fine *)
(*
val verify_wallet_attack (n x_h k x_l : ref int): 
  Lemma 
    (del_rel 4
      (fun r ->
        if r = x_h then High
        else Low) 
      [n; x_h; k; x_l] 
      []
      [fun h -> sel h x_h >= sel h k]
      wallet_attack)
let verify_wallet_attack n x_h k x_l = ()
*)
