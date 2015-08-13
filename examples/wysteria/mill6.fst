(*--build-config
    options:--admit_fsi Set --admit_fsi Wysteria --codegen Wysteria;
    variables:LIB=../../lib;
    other-files:$LIB/ghost.fst $LIB/ext.fst $LIB/set.fsi $LIB/heap.fst $LIB/st.fst $LIB/all.fst wysteria.fsi lib.fst
 --*)

module SMC

open Wysteria
open WLib

let alice_s = singleton alice
let bob_s = singleton bob
let charlie_s = singleton charlie
let ab = union alice_s bob_s
let bc = union bob_s charlie_s
let abc = union ab charlie_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

val read_fn: unit -> Wys nat (fun m0 -> Mode.m m0 = Par /\
                                        (exists p. Mode.ps m0 = singleton p))
                             (fun m0 r -> True)
let read_fn x = read #nat ()

val mill8_sec: ps:prins
               -> w:Wire int{forall p. mem p ps <==> w_contains p w}
               -> unit
               -> Wys prin (pre (Mode Par ps))  post
let mill8_sec ps w _ =

  let f: prev:prin{w_contains prev w}
         -> p:prin{w_contains p w} -> y:int{w_select p w = y}
         -> Wys (prev:prin{w_contains prev w}) (fun m0 -> b2t (m0 = Mode Sec ps)) (fun m0 r -> True) =
    fun prev p y ->
      let y' = projwire_s prev w in
      if y > y' then p else prev
  in
  
  let g:unit -> Wys (p:prin{w_contains p w}) (pre (Mode Sec ps)) (post #(p:prin{w_contains p w})) =
    fun _ ->
      let p = choose ps in
      let ps' = remove p ps in
      wfold ps' w f p
  in
  
  as_sec ps g

val mill8: unit -> Wys bool (pre (Mode Par abc)) post
let mill8 _ =
  let x = as_par alice_s read_fn in
  let y = as_par bob_s read_fn in
  let z = as_par charlie_s read_fn in

  let wa = mkwire_p alice_s x in
  let wb = mkwire_p bob_s y in
  let wc = mkwire_p charlie_s z in

  let w1 = concat_wire wa wb in
  let w2 = concat_wire w1 wc in

  (* call mill for 2 parties *)
  let _ = as_par ab (mill8_sec ab w1) in

  (* call mill for 3 parties *)
  let _ = as_par abc (mill8_sec #abc w2) in

  true
;;

let x = main abc mill8 in wprint x
