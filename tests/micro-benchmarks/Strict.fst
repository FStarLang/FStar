module Strict

#set-options "--warn_error -328" // let rec unused in body

[@@strict_on_arguments [0]]
inline_for_extraction
let sum0 (x y : int) : int = x + y

let t00     = sum0 3 2
let t01 x   = sum0 x 2
let t02 y   = sum0 3 y
let t03 x y = sum0 x y

(* Marked recursive, but not really. Should reduce anyway in extraction. *)
[@@strict_on_arguments [0]]
inline_for_extraction
let rec sum1 (x y : int) : int = x + y

let t11     = sum1 3 2
let t12 x   = sum1 x 2
let t13 y   = sum1 3 y
let t14 x y = sum1 x y

(* Actually recursive *)
[@@strict_on_arguments [0]]
inline_for_extraction
let rec sum2 (x y : nat) : int =
  if x = 0 then y
  else sum2 (x - 1) (y + 1)

let t20     = sum2 3 2
let t21 x   = sum2 x 2
let t22 y   = sum2 3 y
let t23 x y = sum2 x y


open FStar.List.Tot
open FStar.Ghost
inline_for_extraction noextract
let coerce_eq (#a:Type) (#b:Type) (_:squash (a == b)) (x:a) : b = x

inline_for_extraction noextract
let tupdesc = erased (list Type0)

inline_for_extraction noextract
let rec tup (d : tupdesc) : Type0 =
  match d with
  | [] -> unit
  | h :: t -> h & tup t

inline_for_extraction noextract
let rec at (d : tupdesc) (i : nat{i < length d}) : Type0 =
  match d with
  | [] -> unit
  | h :: t ->
    if i = 0 then h
    else at t (i - 1)

inline_for_extraction noextract
let rec remove (d : tupdesc) (i : nat{i < length d}) : (d' : tupdesc { length d' = length d - 1}) =
  match d with
  | [] -> []
  | h :: t ->
    if i = 0 then t
    else h :: remove t (i - 1)

(* This guy can extract as it is, but using unbounded integers
and a LOT of casts. *)
[@@strict_on_arguments [1]]
inline_for_extraction
let rec bring (#d : tupdesc) (i : nat{i < length d}) (x : tup d)
  : at d i & tup (remove d i)
  =
  if i = 0 then x
  else
    let h : erased _ = hd d in
    let t : erased _ = tail d in
    let unfold xh, xt = x <: tup (reveal h :: t) in
    let unfold (y, z) = bring (i - 1) xt in
    (* Why do I need to coerce? *)
    let unfold y : at d i = coerce_eq () y in
    (y, (xh, z))

(* Specialized versions look nicer: *)
let bring0 (#d : tupdesc{length d > 0}) = bring #d 0
let bring1 (#d : tupdesc{length d > 1}) = bring #d 1
let bring2 (#d : tupdesc{length d > 2}) = bring #d 2
let bring3 (#d : tupdesc{length d > 3}) = bring #d 3
