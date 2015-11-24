(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst listproperties.fst st2.fst ordset.fsi ../../prins.fsi ../ffi.fst ../wysteria.fsi
 --*)

(* 3-party gps *)

module SMC

open FStar.List
open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let charlie_s = singleton charlie
let ab = union alice_s bob_s
let abc = union ab charlie_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

val gps_h:
  Box int alice_s -> Box int bob_s -> Box int charlie_s
  -> Wys (Wire prin abc) (pre (Mode Par abc)) post
let gps_h b_a b_b b_c =
  let g: p1:prin{mem p1 abc} -> p2:prin{mem p2 abc} -> p3:prin{mem p3 abc}
         -> Box int (singleton p1) -> Box int (singleton p2) -> Box int (singleton p3)
	 -> unit
	 -> Wys (Box prin (singleton p1)) (pre (Mode Sec abc)) post =
    fun p1 p2 p3 n1 n2 n3 _ ->
    let n1 = unbox_s n1 in
    let n2 = unbox_s n2 in
    let n3 = unbox_s n3 in
    let d2 = if n1 > n2 then n1 - n2 else n2 - n1 in
    let d3 = if n1 > n3 then n1 - n3 else n3 - n1 in
    let p = if d2 > d3 then p3 else p2 in
    box (singleton p1) p
  in

  let b1 = as_sec abc (g alice bob charlie b_a b_b b_c) in
  let b2 = as_sec abc (g bob alice charlie b_b b_a b_c) in
  let b3 = as_sec abc (g charlie alice bob b_c b_a b_b) in

  let w1 = mkwire_p (singleton alice) b1 in
  let w2 = mkwire_p (singleton bob) b2 in
  let w3 = mkwire_p (singleton charlie) b3 in

  let w_ab = concat_wire w1 w2 in
  concat_wire w_ab w3

val gps:
  ps:prins{ps = abc} -> w:Wire int ps -> Wys (Wire prin ps) (pre (Mode Par abc)) post
let gps ps w =
  let g: p:prin{mem p abc} -> unit -> Wys int (pre (Mode Par (singleton p))) post =
    fun p _ -> projwire_p p w
  in

  let b_a = as_par (singleton alice) (g alice) in
  let b_b = as_par (singleton bob) (g bob) in
  let b_c = as_par (singleton charlie) (g charlie) in

  gps_h b_a b_b b_c
