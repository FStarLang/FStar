(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi Wysteria --admit_fsi Prins --admit_fsi FStar.OrdSet --admit_fsi FStar.IO;
    other-files:ghost.fst ext.fst set.fsi heap.fst st.fst all.fst io.fsti list.fst listTot.fst st2.fst ordset.fsi ../../prins.fsi ../ffi.fst ../wysteria.fsi
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

val mono_median_h:
  x:Box (int * int) alice_s -> y:Box (int * int) bob_s
  -> Wys int (pre (Mode Par ab))
          (fun _ r t -> (median_pre (fst (v_of_box x)) (snd (v_of_box x))
                                      (fst (v_of_box y)) (snd (v_of_box y)) ==>
	              r = median_spec (fst (v_of_box x)) (snd (v_of_box x))
                                      (fst (v_of_box y)) (snd (v_of_box y))) /\
		      t = [TMsg #int r])
  let mono_median_h x y =
  let g:unit -> Wys int (pre (Mode Sec ab))
               (fun _ r t -> (median_pre (fst (v_of_box x)) (snd (v_of_box x))
                                      (fst (v_of_box y)) (snd (v_of_box y)) ==>
			   r = median_spec (fst (v_of_box x)) (snd (v_of_box x))
                                           (fst (v_of_box y)) (snd (v_of_box y))) /\
			   t = [])
    =
    fun _ -> //commenting it out for circuit backend: monolithic_median (unbox_s x1) (unbox_s x2) (unbox_s y1) (unbox_s y2)
    let x = unbox_s x in let y = unbox_s y in
    let x1 = fst x in let x2 = snd x in let y1 = fst y in let y2 = snd y in
    let a = x1 > y1 in
    let x3 = if a then x1 else x2 in
    let y3 = if a then y2 else y1 in
    let d = x3 > y3 in
    (if d then y3 else x3)
  in
  
  as_sec ab g

(* val mono_median_h': *)
(*   x1:Box int alice_s -> x2:Box int alice_s -> y1:Box int bob_s -> y2:Box int bob_s *)
(*   -> Wys int (pre (Mode Par ab)) *)
(*     (fun _ r t -> median_pre (v_of_box x1) (v_of_box x2) (v_of_box y1) (v_of_box y2) ==> *)
(*                r = median_spec (v_of_box x1) (v_of_box x2) (v_of_box y1) (v_of_box y2) /\ *)
(* 	       t = [TMsg #int r]) *)
(* let mono_median_h' x1 x2 y1 y2 = *)
(*   let mk_t: p:prin -> z1:Box int (singleton p) -> z2:Box int (singleton p) -> unit *)
(*             -> Wys (int * int) (pre (Mode Par (singleton p))) *)
(* 	          (fun _ r t -> r = (v_of_box z1, v_of_box z2) /\ t = []) = *)
(*     fun p z1 z2 _ -> *)
(*     mk_tuple (unbox_p z1) (unbox_p z2) *)
(*   in *)

(*   let t1 = as_par alice_s (mk_t alice x1 x2) in *)
(*   let t2 = as_par bob_s (mk_t bob y1 y2) in *)
  
(*   mono_median_h t1 t2 *)

val opt_median_h:
  x:Box (int * int) alice_s -> y:Box (int * int) bob_s
  -> Wys int (pre (Mode Par ab))
          (fun _ r _ -> median_pre (fst (v_of_box x)) (snd (v_of_box x))
                                     (fst (v_of_box y)) (snd (v_of_box y)) ==>
	             r = median_spec (fst (v_of_box x)) (snd (v_of_box x))
                                     (fst (v_of_box y)) (snd (v_of_box y)))
let opt_median_h x y =
  let fst_p: p:prin -> x:Box (int * int) (singleton p) -> unit
             -> Wys int (pre (Mode Par (singleton p))) (fun _ r _ -> b2t (r = fst (v_of_box x))) =
    fun p x _ -> fst (unbox_p x)
  in
  let snd_p: p:prin -> x:Box (int * int) (singleton p) -> unit
             -> Wys int (pre (Mode Par (singleton p))) (fun _ r _ -> b2t (r = snd (v_of_box x))) =
    fun p x _ -> snd (unbox_p x)
  in

  let x1 = as_par alice_s (fst_p alice x) in
  let x2 = as_par alice_s (snd_p alice x) in
  let y1 = as_par bob_s (fst_p bob y) in
  let y2 = as_par bob_s (snd_p bob y) in

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

val opt_median_h':
  x1:Box int alice_s -> x2:Box int alice_s -> y1:Box int bob_s -> y2:Box int bob_s
  -> Wys int (pre (Mode Par ab))
    (fun _ r _ -> median_pre (v_of_box x1) (v_of_box x2) (v_of_box y1) (v_of_box y2) ==>
               r = median_spec (v_of_box x1) (v_of_box x2) (v_of_box y1) (v_of_box y2))
let opt_median_h' x1 x2 y1 y2 =
  let mk_t: p:prin -> z1:Box int (singleton p) -> z2:Box int (singleton p) -> unit
            -> Wys (int * int) (pre (Mode Par (singleton p)))
	          (fun _ r _ -> b2t (r = (v_of_box z1, v_of_box z2))) =
    fun p z1 z2 _ ->
    mk_tuple (unbox_p z1) (unbox_p z2)
  in

  let t1 = as_par alice_s (mk_t alice x1 x2) in
  let t2 = as_par bob_s (mk_t bob y1 y2) in
  
  opt_median_h t1 t2

val mono_median: ps:prins{ps = ab} -> w:Wire (int * int) ps -> Wys (Wire int ab) (pre (Mode Par ab)) post
let mono_median ps w =
  let proj: p:prin{FStar.OrdSet.mem p ab} -> unit -> Wys (int * int) (pre (Mode Par (singleton p))) post =
    fun p _ -> projwire_p p w
  in
  let t1 = as_par alice_s (proj alice) in
  let t2 = as_par bob_s (proj bob) in
  let x = mono_median_h t1 t2 in
  let trivial: unit -> Wys int (pre (Mode Par ab)) post =
    fun _ -> x
  in
  mkwire_p ab (as_par ab trivial)

val opt_median: ps:prins{ps = ab} -> w:Wire (int * int) ps -> Wys (Wire int ab) (pre (Mode Par ab)) post
let opt_median ps w =
  let proj: p:prin{FStar.OrdSet.mem p ab} -> unit -> Wys (int * int) (pre (Mode Par (singleton p))) post =
    fun p _ -> projwire_p p w
  in
  let t1 = as_par alice_s (proj alice) in
  let t2 = as_par bob_s (proj bob) in
  let x = opt_median_h t1 t2 in

  let trivial: unit -> Wys int (pre (Mode Par ab)) post =
    fun _ -> x
  in
  mkwire_p ab (as_par ab trivial)
