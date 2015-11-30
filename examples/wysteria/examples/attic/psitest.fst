(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../../prins.fsi ../ffi.fst ../wysteria.fsi
 --*)

(* PSI *)

module SMC

open FStar.List.Tot
open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

type pre_with (m:mode) (t:Type) = fun m0 -> m0 = m /\ t

val psi_m: l1:Box (list int) alice_s -> l2:Box (list int) bob_s
           -> Wys (list int) (pre (Mode Par ab)) post
let psi_m l1 l2 =
  admitP (b2t (List.length (v_of_box l2) > 0));
  let g: unit
	 -> Wys (list int) (pre (Mode Sec ab)) post =
    fun _ ->
    let x = unbox_s l1 in let y = unbox_s l2 in
    FFI.list_intersect x y
  in

  as_sec ab g

val psi: ps:prins{ps = ab} -> w:Wire (list int) ps -> Wys (Wire (list int) ab) (pre (Mode Par ab)) post
let psi ps w =
  let proj: p:prin{FStar.OrdSet.mem p ab} -> unit -> Wys (list int) (pre (Mode Par (singleton p))) post =
    fun p _ -> projwire_p p w
  in
  let l1 = as_par alice_s (proj alice) in
  let l2 = as_par bob_s (proj bob) in
  let l = psi_m l1 l2 in
  let trivial: unit -> Wys (list int) (pre (Mode Par ab)) post =
    fun _ -> l
  in
  mkwire_p ab (as_par ab trivial)
