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

#push-options "--ide_id_info_off"
#push-options "--print_universes --print_implicits"
let expects = ()
let provides = ()
let while = ()
let intro = ()
let par = ()
let invariant = ()

[@@ expect_failure]
%splice_t[tuple_test] (check (`(
  fun (r:ref (U32.t & U32.t)) (n1:erased U32.t) (n2:erased U32.t) ->
           (expects (pts_to r full_perm (reveal n1, reveal n2)))
    (provides (fun _ -> pts_to r full_perm (reveal n1, reveal n2)))
    (
      read #(U32.t & U32.t) r
    )
)))

(* Start up the solver and feed it the initial context *)
let warmup (x:int) = assert (x + 1 > x)

%splice_t[test_true] (check (`(true)))

%splice_t[test_write_10] (check  (`(
   fun (x:ref U32.t)
     (#n:erased U32.t) -> 
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
  fun (r:ref U32.t)
    (#n:erased U32.t) (#p:perm) ->
    (expects (
       pts_to r p n))
    (provides (fun x ->
       pts_to r p x))
    (
       let x = read r in
       return_stt_noeq x
    )
)))

//Bound variable escapes scope
[@@ expect_failure]
%splice_t[test_read_alt_write] (check (`(
  fun (r:ref U32.t)
    (#n:erased U32.t) ->
    (expects (
       pts_to r full_perm n))
    (
       let x = read r in
       write r x
    )
)))


%splice_t[swap] (check (`(
  fun (r1 r2:ref U32.t)
    (#n1 #n2:erased U32.t) ->
    (expects  (
      pts_to r1 full_perm n1 *
      pts_to r2 full_perm n2))
    (provides (fun _ ->
      pts_to r1 full_perm n2 *
      pts_to r2 full_perm n1))
    (
      let x = read r1 in
      let y = read r2 in
      write r1 y;
      write r2 x
    )
)))


%splice_t[call_swap2] (check (`(
  fun (r1 r2:ref U32.t)
    (#n1 #n2:erased U32.t) ->
    (expects  (
      pts_to r1 full_perm n1 *
      pts_to r2 full_perm n2))
    (provides (fun _ -> 
      pts_to r1 full_perm n1 *
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
  fun (r1:ref U32.t) (r2:ref U32.t) (n1:erased U32.t) (n2:erased U32.t) ->
    (expects (pts_to r1 full_perm n1 * pts_to r2 full_perm n2))
    (provides (fun _ ->
               pts_to r1 full_perm n2 * pts_to r2 full_perm n1))
    (
      let x = read r1 in
      let y = read r2 in
      write r1 y;
      write r2 x
    )
)))

%splice_t[swap_with_elim_pure_and_atomic] (check (`(
  fun (r1:ref U32.t) (r2:ref U32.t) (n1:erased U32.t) (n2:erased U32.t) ->
    (expects (pts_to r1 full_perm n1 * pts_to r2 full_perm n2))
    (provides (fun _ ->
               pts_to r1 full_perm n2 * pts_to r2 full_perm n1))
    (
      let x = read_atomic r1 in
      let y = read_atomic r2 in
      write_atomic r1 y;
      write_atomic r2 x
    )
)))

%splice_t[intro_pure_example] (check (`(
  fun (r:ref U32.t) (n1:erased U32.t) (n2:erased U32.t) ->
    (expects (pts_to r full_perm n1 * pure (eq2_prop (reveal n1) (reveal n2))))
    (provides (fun x -> pts_to r full_perm n2 * pure (eq2_prop (reveal n2) (reveal n1))))
    (
       ()
    )
)))

%splice_t[if_example] (check (`(
  fun (r:ref U32.t) (n:erased U32.t{eq2_prop (U32.v (reveal n)) 1}) (b:bool) ->
    (expects (pts_to r full_perm n))
    (provides (fun _ -> pts_to r full_perm (U32.add (reveal n) 2ul)))
    (
      let x = read_atomic r in
      if b
      then write r (U32.add x 2ul)
      else write_atomic r 3ul
    )
)))

//#push-options "--ugly --print_implicits"
%splice_t[elim_intro_exists] (check (`(
  fun (r:ref U32.t) ->
    (expects (exists n. pts_to r full_perm n))
    (provides (fun _ -> exists n. pts_to r full_perm n))
    (
      intro (exists n. pts_to r full_perm n) _
    )
)))

// type dummy = | PatVars
// assume val fresh : dummy
// let tm = (`(
//   fun (r:ref UInt32.t) ->
//     (expects (exists_ (fun n -> pts_to r full_perm n)))
//     (provides (fun _ -> exists_ (fun n -> pts_to r full_perm n)))
//     (
//       let n = elim_exists _ in
//       let PatVars p n = fresh in
//       assert (pts_to r p n);
//       let reveal_n = stt_ghost_reveal UInt32.t n in
//       intro_exists (fun n -> pts_to r full_perm n) reveal_n
//     )
// ))

%splice_t[while_test] (check (`(
  fun (r:ref U32.t) ->
    (expects (exists (b:bool) n. pts_to r full_perm n))
    (provides (fun _ -> exists n. pts_to r full_perm n))
    (
      intro (exists (b:bool) n. pts_to r full_perm n) false _;
      while
        (invariant (fun b -> exists n. pts_to r full_perm n))
        (
          intro (exists n. pts_to r full_perm n) _;
          return_stt_noeq true
        )
        (
          intro (exists (b:bool) n. pts_to r full_perm n) true _;
          return_stt_noeq ()
        )
    )
)))


assume
val pred (b:bool) : vprop
assume
val read_pred (_:unit) (#b:erased bool)
    : stt bool (pred b) (fun r -> pred r)
    
%splice_t[while_test_alt] (check (`(
  fun (r:ref U32.t) ->
    (expects (exists (b:bool) n. pts_to r full_perm n * pred b))
    (provides (fun _ -> exists n. pts_to r full_perm n * pred false))
    (
      while
        (invariant (fun b -> exists n. pts_to r full_perm n * pred b))
        (
          let x = read_pred () in
          return_stt_noeq x
        )
        (
          ()
        )
    )
)))

#set-options "--fuel 2 --ifuel 2"


%splice_t[infer_read_ex] (check (`(
  fun (r:ref U32.t) ->
    (expects (exists n. pts_to r full_perm n))
    (provides (fun _ -> exists n. pts_to r full_perm n))
    (
        let x = read r in
        ()
    ))))


%splice_t[while_count] (check (`(
  let open FStar.UInt32 in
  fun (r:ref t) ->
    (expects (exists n. pts_to r full_perm n))
    (provides (fun _ -> pts_to r full_perm 10ul))
    (
      while
        (invariant (fun b ->
            exists n. pts_to r full_perm n *
                 pure (eq2_prop b (n <> 10ul))))
        (let x = read r in
         return_stt_noeq (x <> 10ul))
        ( 
          let x = read r in
          if x <^ 10ul
          then (write r (x +^ 1ul); ())
          else (write r (x -^ 1ul); ())
        );
      ())
)))


%splice_t[test_par] (check (`(
  fun (r1 r2:ref U32.t) (n1 n2:erased U32.t) ->
    (expects (pts_to r1 full_perm n1 *
              pts_to r2 full_perm n2))
    (provides (fun _ -> pts_to r1 full_perm 1ul *
                     pts_to r2 full_perm 1ul))
    (
      par
        (pts_to r1 full_perm n1)
        (write r1 1ul)
        (fun _ -> pts_to r1 full_perm 1ul)

        (pts_to r2 full_perm n2)
        (write r2 1ul)
        (fun _ -> pts_to r2 full_perm 1ul)
    )
)))
