(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
 --*)

(* Millionaire's for any 2 parties *)

module SMC

open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let charlie_s = singleton charlie
let ab = union alice_s bob_s
let bc = union bob_s charlie_s
let abc = union ab charlie_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

val read_fn: unit -> Wys int (fun m0 -> Mode.m m0 = Par /\
                                  (exists p. Mode.ps m0 = singleton p))
                          (fun m0 r t -> True)
let read_fn x = w_read_int ()

val mill3_sec: #p1:prin -> #p2:prin
               -> x:Box int (singleton p1) -> y:Box int (singleton p2)
               -> unit
               -> Wys bool (pre (Mode Par (union (singleton p1) (singleton p2)))) post
let mill3_sec #p1 #p2 x y _ =
  let s = union (singleton p1) (singleton p2) in
  let g:unit -> Wys bool (pre (Mode Sec s)) post =
   fun _ -> (unbox_s x) > (unbox_s y)
  in
  as_sec s g

val mill3: unit -> Wys bool (pre (Mode Par abc)) post
let mill3 _ =
  let x = as_par alice_s read_fn in
  let y = as_par bob_s read_fn in
  let z = as_par charlie_s read_fn in

  let _ = as_par ab (mill3_sec #alice #bob x y) in
  let _ = as_par bc (mill3_sec #bob #charlie y z) in

  true
;;

let x = main abc mill3 in
print_bool x
