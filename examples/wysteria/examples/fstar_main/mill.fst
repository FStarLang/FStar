(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO --admit_fsi Smciface;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../../prins.fsi ../ffi.fst ../wysteria.fsi
 --*)

(* Millionaire's with 2 parties *)

module SMC

open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

val mill: ps:prins{ps = ab} -> w:Wire int ps -> Wys (Wire bool ps) (pre (Mode Par ab)) post
let mill ps w =
  let g:unit -> Wys (Wire bool ps) (pre (Mode Sec ps)) post =
    fun _ ->
    let x = projwire_s #int #ab alice w in
    let y = projwire_s #int #ab bob w in
    mkwire_s ab (x > y)
  in

  as_sec ab g
