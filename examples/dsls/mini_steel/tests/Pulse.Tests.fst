module Pulse.Tests
module T = FStar.Tactics
open Pulse.Syntax
open Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Pulse.Steel.Wrapper
open Steel.FractionalPermission
open FStar.Ghost

module U32 = FStar.UInt32

#push-options "--print_universes --print_implicits"
let expects = ()
let provides = ()
let while = ()

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
// swap with elim_pure, bind of ghost and stt
//

%splice_t[swap_with_elim_pure] (check (`(
  fun (r1:ref u32) (r2:ref u32) (n1:erased u32) (n2:erased u32) ->
    (expects (pts_to r1 full_perm n1 `star` pts_to r2 full_perm n2))
    (provides (fun _ ->
               pts_to r1 full_perm n2 `star` pts_to r2 full_perm n1))
    (
      let x = read_pure r1 in
      let y = read_pure r2 in
      elim_pure (eq2_prop (reveal n1) x);
      elim_pure (eq2_prop (reveal n2) y);
      write r1 y;
      write r2 x
    )
)))

%splice_t[swap_with_elim_pure_and_atomic] (check (`(
  fun (r1:ref u32) (r2:ref u32) (n1:erased u32) (n2:erased u32) ->
    (expects (pts_to r1 full_perm n1 `star` pts_to r2 full_perm n2))
    (provides (fun _ ->
               pts_to r1 full_perm n2 `star` pts_to r2 full_perm n1))
    (
      let x = read_atomic r1 in
      let y = read_atomic r2 in
      elim_pure (eq2_prop (reveal n1) x);
      elim_pure (eq2_prop (reveal n2) y);
      write_atomic r1 y;
      write_atomic r2 x
    )
)))

%splice_t[intro_pure_example] (check (`(
  fun (r:ref u32) (n1:erased u32) (n2:erased u32) ->
    (expects (pts_to r full_perm n1 `star` pure (eq2_prop (reveal n1) (reveal n2))))
    (provides (fun x -> pts_to r full_perm n2 `star` pure (eq2_prop (reveal n2) (reveal n1))))
    (
      elim_pure (eq2_prop (reveal n1) (reveal n2));
      intro_pure (eq2_prop (reveal n2) (reveal n1)) ()
    )
)))

%splice_t[if_example] (check (`(
  fun (r:ref u32) (n:erased u32{eq2_prop (U32.v (reveal n)) 1}) (b:bool) ->
    (expects (pts_to r full_perm n))
    (provides (fun _ -> pts_to r full_perm (U32.add (reveal n) 2ul)))
    (
      let x = read_atomic r in
      elim_pure (eq2_prop (reveal n) x);
      if b
      then write r (U32.add x 2ul)
      else write_atomic r 3ul
    )
)))

%splice_t[elim_intro_exists] (check (`(
  fun (r:ref u32) ->
    (expects (exists_ (fun (n:u32) -> pts_to r full_perm n)))
    (provides (fun _ -> exists_ (fun (n:u32) -> pts_to r full_perm n)))
    (
      let n = elim_exists (fun (n:u32) -> pts_to r full_perm n) in
      let reveal_n = stt_ghost_reveal u32 n in
      elim_pure (eq2_prop (reveal n) reveal_n);
      intro_exists u32 (fun n -> pts_to r full_perm n) reveal_n
    )
)))

%splice_t[while_test] (check (`(
  fun (r:ref u32) ->
    (expects (exists_ (fun (b:bool) -> exists_ (fun (n:u32) -> pts_to r full_perm n))))
    (provides (fun _ -> exists_ (fun (n:u32) -> pts_to r full_perm n)))
    (
      while
        (fun b -> exists_ (fun (n:u32) -> pts_to r full_perm n))
        (
          let b = elim_exists (fun (b:bool) -> exists_ (fun (n:u32) -> pts_to r full_perm n)) in
          return_stt_noeq #bool true
        )
        (
          intro_exists bool (fun b -> exists_ (fun (n:u32) -> pts_to r full_perm n)) true;
          return_stt_noeq #unit ()
        )
    )
)))

#set-options "--fuel 2 --ifuel 2"

[@@ expect_failure]
%splice_t[while_count] (check (`(
  fun (r:ref u32) ->
    (expects (exists_ (fun (n:u32) -> pts_to r full_perm n)))
    (provides (fun _ -> pts_to r full_perm 10ul))
    (
      let n = elim_exists (fun (n:u32) -> pts_to r full_perm n) in
      let x = read_pure r in
      elim_pure (eq2_prop (reveal n) x);
      let b = return_stt #bool (x <> 10ul) in
      elim_pure (eq2_prop b (x <> 10ul));
      let _ =
        let reveal_n = stt_ghost_reveal u32 n in
        elim_pure (eq2_prop (reveal n) reveal_n);
        intro_pure (iff_prop (b2t b) (reveal_n =!= 10ul)) ();
        intro_exists u32 (fun n -> pts_to r full_perm n `star` pure (iff_prop (b2t b) (n =!= 10ul))) reveal_n;
        intro_exists bool (fun b -> exists_ u#0 u32 (fun n -> pts_to r full_perm n `star` pure (iff_prop (b2t b) (n =!= 10ul)))) b in

      while
        (fun b -> exists_ (fun (n:u32) -> pts_to r full_perm n `star` pure (iff_prop (b2t b) (n =!= 10ul))))
     
        (
          let b = elim_exists (fun (b:bool) -> exists_ u#0 u32 (fun n -> pts_to r full_perm n `star` pure (iff_prop (b2t b) (n =!= 10ul)))) in
          let n = elim_exists (fun (n:u32) -> pts_to r full_perm n `star` pure (iff_prop (b2t (reveal b)) (n =!= 10ul))) in
          elim_pure (iff_prop (b2t (reveal b)) (reveal n =!= 10ul));
          let x = read_pure r in
          elim_pure (eq2_prop (reveal n) x);
          let b_res = return_stt #bool (x <> 10ul) in
          elim_pure (eq2_prop b_res (x <> 10ul));

          let _ =
            let reveal_n = stt_ghost_reveal u32 n in
            elim_pure (eq2_prop (reveal n) reveal_n);
            intro_pure (iff_prop (b2t b_res) (reveal_n =!= 10ul)) ();
            intro_exists u32 (fun n -> pts_to r full_perm n `star` pure (iff_prop (b2t b_res) (n =!= 10ul))) reveal_n in
          
          return_stt_noeq #bool b_res
        )

        (stt_admit unit);

      stt_admit unit
    )
)))
