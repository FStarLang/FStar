(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../prins.fsi ffi.fst wysteria.fsi
 --*)

(* Median *)

module SMC

open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

type pre  (m:mode)  = fun m0 -> b2t (m0 = m)
type post (#a:Type) = fun (m:mode) (x:a) (t:trace) -> True

val read_fn: unit -> Wys int (fun m0 -> Mode.m m0 = Par /\
                                 (exists p. Mode.ps m0 = singleton p))
                          (fun m0 r t -> True)
let read_fn x = w_read_int ()

type distinct (x1:int) (x2:int) (y1:int) (y2:int) =
  x1 =!= x2 /\ x1 =!= y1 /\ x1 =!= y2 /\ x2 =!= y1 /\ x2 =!= y2 /\ y1 =!= y2

type eq_one (n:int) (x1:int) (x2:int) (x3:int) (x4:int) = n = x1 \/ n = x2 \/ n = x3 \/ n = x4

assume val sort: x1:int -> x2:int -> y1:int -> y2:int{distinct x1 x2 y1 y2}
                 -> GTot (r:(int * int * int * int){MkTuple4._1 r < MkTuple4._2 r      /\
		                           MkTuple4._2 r < MkTuple4._3 r      /\
					   MkTuple4._3 r < MkTuple4._4 r      /\
					   eq_one (MkTuple4._1 r) x1 x2 y1 y2 /\
					   eq_one (MkTuple4._2 r) x1 x2 y1 y2 /\
					   eq_one (MkTuple4._3 r) x1 x2 y1 y2 /\
					   eq_one (MkTuple4._4 r) x1 x2 y1 y2})

val median_spec: x1:int -> x2:int -> y1:int -> y2:int{distinct x1 x2 y1 y2} -> GTot int
let median_spec x1 x2 y1 y2 =
  let p = sort x1 x2 y1 y2 in
  MkTuple4._2 p

val monolithic_median: x1:int -> x2:int -> y1:int -> y2:int -> Tot int
let monolithic_median x1 x2 y1 y2 =
  let a = x1 > y1 in
  let x3 = if a then x1 else x2 in
  let y3 = if a then y2 else y1 in
  let d = x3 > y3 in
  if d then y3 else x3

type median_pre (x1:int) (x2:int) (y1:int) (y2:int) =
  x1 < x2 /\ y1 < y2 /\ distinct x1 x2 y1 y2

val monolithic_median_correctness:
  x1:int -> x2:int -> y1:int -> y2:int
  -> Lemma (requires (True))
          (ensures (median_pre x1 x2 y1 y2 ==> monolithic_median x1 x2 y1 y2 =
	                                      median_spec x1 x2 y1 y2))
let monolithic_median_correctness x1 x2 y1 y2 = ()

val mono_median: unit -> Wys int (pre (Mode Par ab)) post
let mono_median _ =
  let x1 = as_par alice_s read_fn in
  let x2 = as_par alice_s read_fn in
  let y1 = as_par bob_s read_fn in
  let y2 = as_par bob_s read_fn in

  let g:unit -> Wys int (pre (Mode Sec ab)) post =
    fun _ -> //commenting it out for circuit backend: monolithic_median (unbox_s x1) (unbox_s x2) (unbox_s y1) (unbox_s y2)
    let x1 = unbox_s x1 in let x2 = unbox_s x2 in let y1 = unbox_s y1 in let y2 = unbox_s y2 in
    let a = x1 > y1 in
    let x3 = if a then x1 else x2 in
    let y3 = if a then y2 else y1 in
    let d = x3 > y3 in
    if d then y3 else x3    
  in
  
  as_sec ab g

val opt_median: unit -> Wys int (pre (Mode Par ab)) post
let opt_median _ =
  let x1 = as_par alice_s read_fn in
  let x2 = as_par alice_s read_fn in
  let y1 = as_par bob_s read_fn in
  let y2 = as_par bob_s read_fn in

  let cmp:
    x:Box int alice_s -> y:Box int bob_s -> unit
    -> Wys bool (pre (Mode Sec ab)) (fun _ r _ ->
    	                            b2t (r = ((v_of_box x) > (v_of_box y)))) =
    fun x y _ -> (unbox_s x) > (unbox_s y)
  in

  let select:
    #p:prin -> b:bool -> n1:Box int (singleton p) -> n2:Box int (singleton p) -> unit
    -> Wys int (pre (Mode Par (singleton p)))
            (fun _ r _ -> (b       ==> r = v_of_box n1) /\
	               ((not b) ==> r = v_of_box n2)) =
    fun #p b n1 n2 _ -> if b then (unbox_p n1) else (unbox_p n2)
  in

  let select_s:
    b:bool -> n1:Box int alice_s -> n2:Box int bob_s -> unit
    -> Wys int (pre (Mode Sec ab))
            (fun _ r _ -> (b       ==> r = v_of_box n2) /\
	               ((not b) ==> r = v_of_box n1)) =
    fun b n1 n2 _ -> if b then (unbox_s n2) else (unbox_s n1)
  in

  let g:
    unit -> Wys int (pre (Mode Par ab))
                 (fun _ r _ -> b2t (r = monolithic_median (v_of_box x1) (v_of_box x2)
		                                       (v_of_box y1) (v_of_box y2))) =
    fun _ ->
      let a = as_sec ab (cmp x1 y1) in
      let x3 = as_par alice_s (select #alice a x1 x2) in
      let y3 = as_par bob_s (select #bob a y2 y1) in
      let d = as_sec ab (cmp x3 y3) in
      let r = as_sec ab (select_s d x3 y3) in
      r

  in

  unbox_p (as_par ab g)
;;

let x = main ab mono_median in
print_int x;
let y = main ab opt_median in
print_int y
