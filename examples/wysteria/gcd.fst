(*--build-config
    options:--admit_fsi Set --admit_fsi Wysteria --codegen Wysteria --trace_error;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst wysteria.fsi
 --*)

(* Millionaire's with 2 parties *)

module SMC

open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) -> True

val read_fn: unit -> Wys nat (fun m0 -> Mode.m m0 = Par /\
                                        (exists p. Mode.ps m0 = singleton p))
                             (fun m0 r -> True)
let read_fn x = read #nat ()

val gcd: a:int -> b:int -> Dv int
let rec gcd a b =
  if a = b then a
  else if a > b then gcd (a - b) b
  else gcd a (b - a)

val gcd1: unit -> Wys int (pre (Mode Par ab)) post
let gcd1 _ =
 let x = as_par alice_s read_fn in
 let y = as_par bob_s read_fn in

 let g:unit -> Wys int (pre (Mode Sec ab)) post =
   fun _ -> gcd (unbox_s x) (unbox_s y)
 in

 as_sec ab g
;;

let x = main ab gcd1 in
wprint x
