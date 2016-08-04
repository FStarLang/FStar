module Median

open Prins
open FFI
open Wysteria

let alice_s = singleton alice
let bob_s = singleton bob
let ab = union alice_s bob_s

//this fails ?
//type pre (m:mode) = fun m0 -> m0 == m

assume val get_mode: unit -> Wys mode (fun m -> True)
                                     (fun m r t -> r = m)

type distinct (x1:int) (x2:int) (y1:int) (y2:int) =
  x1 =!= x2 /\ x1 =!= y1 /\ x1 =!= y2 /\ x2 =!= y1 /\ x2 =!= y2 /\ y1 =!= y2

type eq_one (n:int) (x1:int) (x2:int) (x3:int) (x4:int) = n = x1 \/ n = x2 \/ n = x3 \/ n = x4

assume val sort: x1:int -> x2:int -> y1:int -> y2:int{distinct x1 x2 y1 y2}
                 -> GTot (r:(int * int * int * int){
		     let Mktuple4 a b c d = r in
		     a < b /\ b < c /\ c < d /\
		     eq_one a x1 x2 y1 y2  /\
		     eq_one b x1 x2 y1 y2  /\
		     eq_one c x1 x2 y1 y2  /\
		     eq_one d x1 x2 y1 y2})

val median_spec: x1:int -> x2:int -> y1:int -> y2:int{distinct x1 x2 y1 y2} -> GTot int
let median_spec x1 x2 y1 y2 =
  let p = sort x1 x2 y1 y2 in
  Mktuple4._2 p

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
  x:box (int * int) alice_s -> y:box (int * int) bob_s
  -> Wys int (fun m -> m = Mode Par ab)
          (fun _ r t -> (median_pre (fst (v_of_box x)) (snd (v_of_box x))
                                      (fst (v_of_box y)) (snd (v_of_box y)) ==>
	              r = median_spec (fst (v_of_box x)) (snd (v_of_box x))
                                      (fst (v_of_box y)) (snd (v_of_box y))) /\
		      t == [TMsg #int r])
  let mono_median_h x y =
  let g:unit -> Wys int (fun m -> m = Mode Sec ab)
               (fun _ r t -> (median_pre (fst (v_of_box x)) (snd (v_of_box x))
                                      (fst (v_of_box y)) (snd (v_of_box y)) ==>
			   r = median_spec (fst (v_of_box x)) (snd (v_of_box x))
                                           (fst (v_of_box y)) (snd (v_of_box y))) /\
			   t == [])
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

val optimized_trace: x:int * int -> y:int * int -> Tot trace
let optimized_trace x y =
  let x1, x2, y1, y2 = fst x, snd x, fst y, snd y in
  let a = x1 > y1 in
  let x3 = if a then x1 else x2 in
  let y3 = if a then y2 else y1 in
  let d = x3 > y3 in
  let m = if d then y3 else x3 in

  (TMsg #bool a)     ::
  (TScope alice_s [])::
  (TScope bob_s [])  ::
  (TMsg #bool d)     ::
  (TMsg #int m)      ::[]

val opt_fn_trace: x:int * int -> y:int * int -> Tot trace
let opt_fn_trace x y =
  (TScope alice_s [])::
  (TScope alice_s [])::
  (TScope bob_s [])  ::
  (TScope bob_s [])  ::
  [TScope ab (optimized_trace x y)]

val opt_median_h:
  x:box (int * int) alice_s -> y:box (int * int) bob_s
  -> Wys int (fun m -> m = Mode Par ab)
          (fun _ r t -> (median_pre (fst (v_of_box x)) (snd (v_of_box x))
                                      (fst (v_of_box y)) (snd (v_of_box y)) ==>
	              r = median_spec (fst (v_of_box x)) (snd (v_of_box x))
                                      (fst (v_of_box y)) (snd (v_of_box y))) /\
		      t == opt_fn_trace (v_of_box x) (v_of_box y))
let opt_median_h x y =
  let fst_p: p:prin -> x:box (int * int) (singleton p) -> unit
             -> Wys int (fun m -> m = Mode Par (singleton p)) (fun _ r t -> r = fst (v_of_box x) /\ t == []) =
    fun p x _ -> fst (unbox_p x)
  in
  let snd_p: p:prin -> x:box (int * int) (singleton p) -> unit
             -> Wys int (fun m -> m = Mode Par (singleton p)) (fun _ r t -> r = snd (v_of_box x) /\ t == []) =
    fun p x _ -> snd (unbox_p x)
  in

  let fst_alice: unit -> Wys int (fun m -> m = Mode Par alice_s)
                              (fun _ r t -> r = fst (v_of_box x) /\ t == []) =
    fun _ -> fst (unbox_p x)
  in
  let snd_alice: unit -> Wys int (fun m -> m = Mode Par alice_s)
                              (fun _ r t -> r = snd (v_of_box x) /\ t == []) =
    fun _ -> snd (unbox_p x)
  in
  let fst_bob: unit -> Wys int (fun m -> m = Mode Par bob_s)
                            (fun _ r t -> r = fst (v_of_box y) /\ t == []) =
    fun _ -> fst (unbox_p y)
  in
  let snd_bob: unit -> Wys int (fun m -> m = Mode Par bob_s)
                            (fun _ r t -> r = snd (v_of_box y) /\ t == []) =
    fun _ -> snd (unbox_p y)
  in

  let x1 = as_par #int #(fun m -> m = Mode Par alice_s) #(fun _ r t -> r = fst (v_of_box x) /\ t == []) alice_s fst_alice in
  let x2 = as_par #int #(fun m -> m = Mode Par alice_s) #(fun _ r t -> r = snd (v_of_box x) /\ t == []) alice_s snd_alice in
  let y1 = as_par #int #(fun m -> m = Mode Par bob_s) #(fun _ r t -> r = fst (v_of_box y) /\ t == []) bob_s fst_bob in
  let y2 = as_par #int #(fun m -> m = Mode Par bob_s) #(fun _ r t -> r = snd (v_of_box y) /\ t == []) bob_s snd_bob in

  let cmp:
    x:box int alice_s -> y:box int bob_s -> unit
    -> Wys bool (fun m -> m = Mode Sec ab)
               (fun _ r t -> r = ((v_of_box x) > (v_of_box y)) /\ t == []) =
    fun x y _ -> (unbox_s x) > (unbox_s y)
  in

  let select_alice:
    b:bool -> n1:box int alice_s -> n2:box int alice_s -> unit
    -> Wys int (fun m -> m = Mode Par alice_s)
            (fun _ r t -> (b       ==> r = v_of_box n1) /\
	               ((not b) ==> r = v_of_box n2) /\ t == []) =
    fun b n1 n2 _ -> if b then (unbox_p n1) else (unbox_p n2)
  in

  let select_bob:
    b:bool -> n1:box int bob_s -> n2:box int bob_s -> unit
    -> Wys int (fun m -> m = Mode Par bob_s)
            (fun _ r t -> (b       ==> r = v_of_box n1) /\
	               ((not b) ==> r = v_of_box n2) /\ t == []) =
    fun b n1 n2 _ -> if b then (unbox_p n1) else (unbox_p n2)
  in

  let select_s:
    b:bool -> n1:box int alice_s -> n2:box int bob_s -> unit
    -> Wys int (fun m -> m = Mode Sec ab)
            (fun _ r t -> (b       ==> r = v_of_box n2) /\
	               ((not b) ==> r = v_of_box n1) /\ t == []) =
    fun b n1 n2 _ -> if b then (unbox_s n2) else (unbox_s n1)
  in

  let g:
    unit -> Wys int (fun m -> m = Mode Par ab)
                 (fun _ r t -> (r = monolithic_median (v_of_box x1) (v_of_box x2)
  		                                   (v_of_box y1) (v_of_box y2)) /\
			    (t == optimized_trace (v_of_box x) (v_of_box y))) =
    fun _ ->
      let a = as_sec ab (cmp x1 y1) in
      let x3 = as_par alice_s (select_alice a x1 x2) in
      let y3 = as_par bob_s (select_bob a y2 y1) in
      let d = as_sec ab (cmp x3 y3) in
      let r = as_sec ab (select_s d x3 y3) in
      r

  in

  unbox_p (as_par ab g)

val optimized_median_secure_for_alice:
  x1:(int * int) -> x2:(int * int) -> y:(int * int)
  -> Lemma (requires (median_pre (fst x1) (snd x1) (fst y) (snd y) /\
		     median_pre (fst x2) (snd x2) (fst y) (snd y) /\  
                     median_spec (fst x1) (snd x1) (fst y) (snd y) =
                     median_spec (fst x2) (snd x2) (fst y) (snd y)))
	  (ensures (opt_fn_trace x1 y == opt_fn_trace x2 y))
let optimized_median_secure_for_alice x1 x2 y =()

val optimized_median_secure_for_bob:
  x:(int * int) -> y1:(int * int) -> y2:(int * int)
  -> Lemma (requires (median_pre (fst x) (snd x) (fst y1) (snd y1) /\
		     median_pre (fst x) (snd x) (fst y2) (snd y2) /\  
                     median_spec (fst x) (snd x) (fst y1) (snd y1) =
                     median_spec (fst x) (snd x) (fst y2) (snd y2)))
	  (ensures (opt_fn_trace x y1 == opt_fn_trace x y2))
let optimized_median_secure_for_bob x y1 y2 =()
