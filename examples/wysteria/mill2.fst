(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst list.fst st2.fst wysteria.fsi
 --*)

(* Millionaire's with 2 parties, secure block as a separate function *)

module SMC

open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

val mill2_sec: x:Box nat alice_s -> y:Box nat bob_s -> Wys bool (pre (Mode Par ab)) post
let mill2_sec x y =
  let g:unit -> Wys bool (pre (Mode Sec ab)) post =
    fun _ -> (unbox_s x) > (unbox_s y)
  in
  as_sec ab g

val mill2: unit -> Wys bool (pre (Mode Par ab)) post
let mill2 _ =
  let x = as_par alice_s (read #nat) in
  let y = as_par bob_s (read #nat) in
  mill2_sec x y

;;

let _ = main ab mill2 in ()
