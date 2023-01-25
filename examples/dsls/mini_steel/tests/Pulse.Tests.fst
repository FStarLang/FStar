module Pulse.Tests
module T = FStar.Tactics
open Pulse.Syntax
open Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Pulse.Steel.Wrapper
open Steel.FractionalPermission
open FStar.Ghost
#push-options "--print_universes --print_implicits"
let expects = ()
let provides = ()


(* Start up the solver and feed it the initial context *)
let warmup (x:int) = assert (x + 1 > x)

%splice_t[test_true] (check (`(true)))

%splice_t[test_write_10] (check  (`(
   fun (x:ref u32)
     (#n:erased u32) -> 
     (expects (
        pts_to x full_perm n))
     (provides (fun _ ->
        pts_to x full_perm 0ul))
     (
       write x 1ul;
       write x 0ul
     )
   )))


%splice_t[test_read] (check (`(
  fun (r:ref u32)
    (#n:erased u32) (#p:perm) ->
    (expects (
       pts_to r p n))
    (provides (fun x ->
       pts_to r p x))
    (
       read r 
    )
)))       

%splice_t[test_read_with_alt_post] (check (`(
  fun (r:ref u32)
    (#n:erased u32) (#p:perm) ->
    (expects (
       pts_to r p n))
    (provides (fun _ -> 
       pts_to r p n))
    (
       read r
    )
)))

//Bound variable escapes scope
[@@ expect_failure]
%splice_t[test_read_alt_write] (check (`(
  fun (r:ref u32)
    (#n:erased u32) ->
    (expects (
       pts_to r full_perm n))
    (
       let x = read r in
       write r x
    )
)))


%splice_t[swap] (check (`(
  fun (r1 r2:ref u32)
    (#n1 #n2:erased u32) ->
    (expects  (
      pts_to r1 full_perm n1 `star` 
      pts_to r2 full_perm n2))
    (provides (fun _ ->
      pts_to r1 full_perm n2 `star` 
      pts_to r2 full_perm n1))
    (
      let x = read r1 in
      let y = read r2 in
      write r1 y;
      write r2 x
    )
)))


%splice_t[call_swap2] (check (`(
  fun (r1 r2:ref u32)
    (#n1 #n2:erased u32) ->
    (expects  (
      pts_to r1 full_perm n1 `star` 
      pts_to r2 full_perm n2))
    (provides (fun _ -> 
      pts_to r1 full_perm n1 `star` 
      pts_to r2 full_perm n2))
    (
      swap r1 r2;
      swap r1 r2
    )
)))


//
// atomic and stt bind, framing, etc.
//

%splice_t[read_atomic] (check (`(
  fun (r1:ref u32) (r2:ref u32) (n1:erased u32) (n2:erased u32) ->
    (expects (
       pts_to r1 full_perm n1 `star`
       pts_to r2 full_perm n2))
    (provides (fun _ ->
       pts_to r1 full_perm n1 `star`
       pts_to r2 full_perm n2))
    (
      let x = read_explicit r2 n2 full_perm in
      read_atomic r1 n1 full_perm
    )
)))

%splice_t[ghost_read_atomic] (check (`(
  fun (r:ref u32) (n:erased u32) ->
    (expects (pts_to r full_perm n))
    (provides (fun _ -> pts_to r full_perm n))
    (
      let x = ghost_noop () in
      Pulse.Steel.Wrapper.read_atomic r n full_perm
    )
)))

%splice_t[ghost_read] (check (`(
  fun (r:ref u32) (n:erased u32) ->
    (expects (pts_to r full_perm n))
    (provides (fun _ -> pts_to r full_perm n))
    (
      let x = ghost_noop () in
      Pulse.Steel.Wrapper.read_explicit r n full_perm
    )
)))
