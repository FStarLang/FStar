module SL.ConcurrentExamples

open SL.Base
open SL.AutoTactic

let left  r () : ST int (fun p m -> exists v. m == r |> v /\ p 1 (r |> v)) [ii r] by (sl_auto ()) = 1
let right r () : ST int (fun p m -> exists v. m == r |> v /\ p 2 (r |> v)) [ii r] by (sl_auto ()) = 2

let par1 (r:ref int) (s:ref int) : ST int (fun p m -> exists v w. m == (r |> v <*> s |> w) /\ p 3 (r |> v <*> s |> w)) [] by (sl_auto ())
=
  let (x, y) = par (left r) (right s) in
  x + y

let par2 (r:ref int) (s:ref int) : ST int (fun p m -> exists v w. m == (r |> v <*> s |> w) /\ p 3 (r |> v <*> s |> w))
			            [ii r; ii s] by (sl_auto ())
=
  let (x, y) = par (left s) (right r) in
  x + y


let par3 (r s t : ref int) : ST int (fun p m -> exists v w u. m == (r |> v <*> s |> w <*> t |> u) /\ p 5 (r |> v <*> s |> w <*> t |> u)) [] by (sl_auto ())
=
  let (x, z) = par (fun () -> par2 r s) (right t) in
  x + z

(* Funny, the VC for this is much smaller and verifies a lot quicker *)
#push-options "--use_two_phase_tc false"
let par3' (r s t : ref int) : ST int (fun p m -> exists v w u. m == (r |> v <*> s |> w <*> t |> u) /\ p 5 (r |> v <*> s |> w <*> t |> u)) [] by (sl_auto ())
=
  let (x, z) = par (fun () -> par2 r s) (right t) in
  x + z
#pop-options

let ret (x:'a) () : ST 'a (fun p m -> m == emp /\ p x m) [] =
  x

let set_to_2 (r : ref int) () : ST int (fun p m -> exists v. m == (r |> v) /\ p 1 (r |> 2)) [ii r] =
  r := 2;
  1

(* Actually changing a reference *)
let par_set (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> 2)) [ii r] by (sl_auto ())
=
  let (x, y) = par (set_to_2 r) (ret 2) in
  x + y


(* This is explicit about the frames of the parallel composition, but still requires
 * non-trivial frame reasoning *)
(* Does not work now, we haven't implemented par_exp in the tactic (do we want to? probably not *)
//let l (x:'a) : ST 'a (fun p m -> m == emp /\ p x m) [] = x
//let test03' (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 (r |> v)) [] by (sl_auto ())
//=
//  let (x, y) = par_exp emp emp (fun () -> l 1) (fun () -> l 2) in
//  x + y


(* open FStar.Tactics *)
(* module T = FStar.Tactics *)

(* let _ = *)
(*   assert (dfst #int #(fun j -> int) (| 1, 2 |) == 1) *)
(*       by (dump "1"; compute (); dump "2") *)
      
let test_acq (r:ref int) (l:lock [ii r] (fun _ -> True)) : ST int (fun p m -> m == emp /\ (forall v. p 3 (r |> v))) [ii r]
  by (sl_auto ())
    
  =
  acquire l;
  3

let test_acq_rel (r:ref int) (l:lock [ii r] (fun _ -> True)) : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ())
  =
  acquire l;
  let v = !r in
  release l

let set_and_ret (r:ref int) (l : lock [ii r] (fun _ -> True)) (n : nat) () : ST int (fun p m -> m == emp /\ p n emp) [] by (sl_auto ()) =
  acquire l;
  r := n;
  release l;
  n

//#set-options "--print_implicits"

(* Note: final heap is empty, it is the lock that owns `r` *)
let test06 (r:ref int) : ST int (fun p m -> exists v. m == r |> v /\ p 3 emp) [] by (sl_auto ()) =
  let l = mklock #(fun _ -> True) [ii r]  in
  let (x, y) = par (set_and_ret r l 1) (set_and_ret r l 2) in
  x + y

let test07 () : ST int (fun p m -> m == emp /\ (forall r. p 3 (r |> 5))) [] by (sl_auto ()) =
  let r = alloc 5 in
  3
  

let test08 (r : ref int) : ST int (fun p m -> exists v. m == (r |> v) /\ (forall r'. p v (r |> v <*> r' |> v))) [ii r] by (sl_auto ()) =
  let v = !r in
  let r' = alloc v in
  v
  
let test09 (r : ref int) : ST int (fun p m -> exists v. m == (r |> v) /\ (forall r'. p v (r' |> v <*> r |> v))) [ii r] by (sl_auto ()) =
  let v = !r in
  let r' = alloc v in
  v

let test10 () : ST int (fun p m -> m == emp /\ (forall i m. p i m)) [] by (sl_auto ()) =
  let r = alloc 3 in
  test08 r

let test11 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 3 in
  r := 22;
  free r

let non_neg_inv (r:ref int) : memory -> Type0 =
  //fun m -> exists v. m == r |> v /\ v >= 0
  fun m -> exists v. v >= 0 /\ mem_eq (m == r |> v)

open FStar.Tactics

let take_and_incr (r:ref int) (l : lock [ii r] (fun m -> non_neg_inv r m)) : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  acquire l;
  r := !r + 1;
  release l


//#set-options "--debug SL.ConcurrentExamples --debug_level Tac"
//#set-options "--print_full_names --prn"

let test12 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  //let _ = par (fun () -> take_and_incr r l) (fun () -> take_and_incr r l) in
  //acquire l;
  //let v = !r in
  //assert (v >= 0);
  ()
  //free r

let test13 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  //let _ = par (fun () -> take_and_incr r l) (fun () -> take_and_incr r l) in
  acquire l;
  //let v = !r in
  //assert (v >= 0);
  free r

let test14 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  let _ = par (fun () -> take_and_incr r l) (fun () -> take_and_incr r l) in
  acquire l;
  //let v = !r in
  //assert (v >= 0);
  free r

let test15 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  let _ = par (fun () -> take_and_incr r l) (fun () -> take_and_incr r l) in
  acquire l;
  let v = !r in
  //assert (v >= 0);
  free r

let test16 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let l = mklock #(fun m -> non_neg_inv r m) [ii r] in
  let _ = par (fun () -> take_and_incr r l) (fun () -> take_and_incr r l) in
  acquire l;
  let v = !r in
  assert (v >= 0);
  free r

(* Double locks... hey, if it works for 1 and 2, it works for n *)

let test17 (r s : ref int) : ST unit (fun p m -> exists v u. m == (r |> v <*> s |> u) /\ p () emp) [] by (sl_auto ()) =
  let l = mklock #(fun m -> True) [ii r; ii s] in
  ()

(* Same thing with the list backwards... should be robust *)
let test17' (r s : ref int) : ST unit (fun p m -> exists v u. m == (r |> v <*> s |> u) /\ p () emp) [] by (sl_auto ()) =
  let l = mklock #(fun m -> True) [ii s; ii r] in
  ()

let test18 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 0 in
  let s = alloc 1 in
  let l = mklock #(fun m -> True) [ii r; ii s] in
  ()

(* Coupled references *)
let test19 () : ST unit (fun p m -> m == emp /\ p () emp) [] by (sl_auto ()) =
  let r = alloc 1 in
  let s = alloc 1 in
  let l = mklock #(fun m -> exists v u. m == (r |> u <*> s |> v) /\ v == u)  [ii r; ii s] in
  ()
  
let test20 () : ST unit (fun p m -> m == emp /\ (forall m'. p () m')) [] by (sl_auto ()) =
  let r = alloc 1 in
  let s = alloc 1 in
  let l = mklock #(fun m -> exists v u. m == (r |> u <*> s |> v) /\ v == u)  [ii r; ii s] in
  acquire l;
  ()

let test21 () : ST unit (fun p m -> m == emp /\ (forall m'. p () m')) [] by (sl_auto ()) =
  let r = alloc 1 in
  let s = alloc 1 in
  let l = mklock #(fun m -> exists v u. m == (r |> u <*> s |> v) /\ v == u)  [ii r; ii s] in
  acquire l;
  let v = !r in
  let u = !s in
  ()

let test22 () : ST unit (fun p m -> m == emp /\ (forall m'. p () m')) [] by (sl_auto ()) =
  let r = alloc 1 in
  let s = alloc 1 in
  let l = mklock #(fun m -> exists v u. mem_eq (m == (r |> u <*> s |> v)) /\ v == u)  [ii r; ii s] in
  acquire l;
  let v = !r in
  let u = !s in
  assert (v == u); (* Requires destructing a heap equality in the context *)
  ()

(* Calling an unknown procedure, can still conclude the invariant *)
assume val kinda_havoc : unit -> ST unit (fun p m -> m == emp /\ p () emp) []
let test23 () : ST unit (fun p m -> m == emp /\ (forall m'. p () m')) [] by (sl_auto ()) =
  let r = alloc 1 in
  let s = alloc 1 in
  let l = mklock #(fun m -> exists v u. mem_eq (m == (r |> u <*> s |> v)) /\ v == u)  [ii r; ii s] in
  kinda_havoc ();
  acquire l;
  let v = !r in
  let u = !s in
  assert (v == u); (* Requires destructing a heap equality in the context *)
  ()
