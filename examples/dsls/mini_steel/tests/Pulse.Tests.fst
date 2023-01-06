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

%splice_t[test_syntax] (check  (`(
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


%splice_t[test_read2] (check (`(
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

%splice_t[test_read_alt_with_post] (check (`(
  fun (r:ref u32)
    (#n:erased u32) (#p:perm) ->
    (expects (
       pts_to r p n))
    (provides (fun _ -> 
       pts_to r p n))
    (
       read_alt r
    )
)))

%splice_t[test_read_alt_with_post2] (check (`(
    fun (r1 r2:ref u32) 
      (#n1 #n2:erased u32) (#p1 #p2:perm) ->
      (expects (
         pts_to r1 p1 n1 `star`
         pts_to r2 p2 n2))
      (provides (fun _ -> 
         pts_to r1 p1 n1 `star`
         pts_to r2 p2 n2))
      (
         read_alt r2
      )
)))

%splice_t[test_read_refine] (check (`(
      fun (r:ref u32)
        (#n:erased u32) (#p:perm) ->
        (expects (
           pts_to r p n))
        (
           read_refine r
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
       let x = read_alt r in
       write r x
    )
)))


%splice_t[test_swap2] (check (`(
  fun (r1 r2:ref u32)
    (#n1 #n2:erased u32) ->
    (expects  (
      pts_to r1 full_perm n1 `star` 
      pts_to r2 full_perm n2))
    (provides (fun _ ->
      pts_to r1 full_perm n2 `star` 
      pts_to r2 full_perm n1))
    (
      let x = read_refine r1 in
      let y = read_refine r2 in
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
      test_swap2 r1 r2;
      test_swap2 r1 r2
    )
)))
