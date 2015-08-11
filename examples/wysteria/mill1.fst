(*--build-config
    options:--admit_fsi Set --admit_fsi Wysteria --codegen Wysteria;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst wysteria.fsi
 --*)

(* Millionaire's with 2 parties *)

module SMC

open Wysteria

(*let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s*)

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) -> True

(*val mill1: unit -> Wys bool (pre (Mode Par ab)) post
let mill1 _ =
 let x = as_par alice_s (read #nat) in
 let y = as_par bob_s (read #nat) in

 let g:unit -> Wys bool (pre (Mode Sec ab)) post =
   fun _ -> (unbox_s x) > (unbox_s y)
 in

 as_sec ab g*)

let g x = x - 2 

;;

let f x = (g x) + 2 in
wprint #nat (f 2)

//let _ = main ab mill1 in ()
