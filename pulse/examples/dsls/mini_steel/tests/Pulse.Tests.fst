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
   fun (x:ref u32) (#n:erased u32) -> 
     (expects (
        pts_to x full_perm n)) //(reveal n)))
     (provides (fun _ ->
        pts_to x full_perm 0ul))
     (
       let _ = write n x 1ul in
       write (hide 1ul) x 0ul
     )
   )))

%splice_t[test_read2] (check (`(
  fun (n:erased u32) (r:ref u32) ->
    (expects (
       pts_to r full_perm (reveal n)))
    (provides (fun x ->
       pts_to r full_perm x))
    (
       read n r 
    )
)))       

%splice_t[test_read_alt_with_post] (check (`(
  fun (n:erased u32)
    (r:ref u32) ->
    (expects (
       pts_to r full_perm (reveal n)))
    (provides (fun _ -> 
       pts_to r full_perm (reveal n)))
    (
       read_alt n r
    )
)))

%splice_t[test_read_alt_with_post2] (check (`(
    fun (n:erased u32)
      (r1 r2:ref u32) ->
      (expects (
         pts_to r1 full_perm (reveal n) `star`
         pts_to r2 full_perm (reveal n)))
      (provides (fun _ -> 
         pts_to r1 full_perm (reveal n) `star`
         pts_to r2 full_perm (reveal n)))
      (
         read_alt n r2
      )
)))

%splice_t[test_read_refine] (check (`(
      fun (n:erased u32)
        (r:ref u32) ->
        (expects (
           pts_to r full_perm (reveal n)))
        (
           read_refine n r
        )
)))

%splice_t[test_write] (check (`(
     fun (n:erased u32)
       (r1:ref u32)
       (x:u32)
       (r2:ref u32) ->
       (expects (
          pts_to r1 full_perm (reveal n) `star`
          pts_to r2 full_perm (reveal n)))
       (
          write n r2 x
       )
)))

//Bound variable escapes scope
[@@ expect_failure]
%splice_t[test_read_alt_write] (check (`(
  fun (n:erased u32)
    (r:ref u32) ->
    (expects (
       pts_to r full_perm (reveal n)))
    (
       let x = read_alt n r in
       write n r x
    )
)))


[@@ expect_failure]
%splice_t[read_implicit] (check (`(
  fun (#n:erased u32)
    (r:ref u32) ->
    (expects (
       pts_to r full_perm (reveal n)))
    (
       read_implicit r
    )
)))
    
%splice_t[test_swap2] (check (`(
  fun (n1 n2:erased u32)
    (r1 r2:ref u32) ->
    (expects  (
      pts_to r1 full_perm (reveal n1) `star` 
      pts_to r2 full_perm (reveal n2)))
    (provides (fun _ ->
      pts_to r1 full_perm (reveal n2) `star` 
      pts_to r2 full_perm (reveal n1)))
    (
      let x = read_refine n1 r1 in
      let y = read_refine n2 r2 in
      write n1 r1 y;
      write n2 r2 x
    )
)))


%splice_t[call_swap2] (check (`(
  fun (n1 n2:erased u32)
    (r1 r2:ref u32) ->
    (expects  (
      pts_to r1 full_perm (reveal n1) `star` 
      pts_to r2 full_perm (reveal n2)))
    (provides (fun _ -> 
      pts_to r1 full_perm (reveal n1) `star` 
      pts_to r2 full_perm (reveal n2)))
    (
      test_swap2 n1 n2 r1 r2;
      test_swap2 n2 n1 r1 r2
    )
)))
