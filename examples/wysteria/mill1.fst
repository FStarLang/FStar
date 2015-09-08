(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst $LIB/list.fst $LIB/st2.fst wysteria.fsi
 --*)

(* Millionaire's with 2 parties *)

module SMC

open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

val read_fn: unit -> Wys nat (fun m0 -> Mode.m m0 = Par /\
                                        (exists p. Mode.ps m0 = singleton p))
                             (fun m0 r t -> True)
let read_fn x = read #nat ()

val mill1: unit -> Wys bool (pre (Mode Par ab)) post
let mill1 _ =
  let x = as_par alice_s read_fn in  
  let y = as_par bob_s read_fn in
  
  let g:unit -> Wys bool (pre (Mode Sec ab)) post =
    fun _ -> (unbox_s x) > (unbox_s y)
  in

  as_sec ab g
;;

let x = main ab mill1 in
wprint x
