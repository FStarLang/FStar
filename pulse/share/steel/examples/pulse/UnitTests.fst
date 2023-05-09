module UnitTests
module T = FStar.Tactics
open Pulse.Syntax
open Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost

module U32 = FStar.UInt32

open Pulse.Steel.Wrapper
open Tests.Common

#push-options "--ide_id_info_off"
#push-options "--print_universes --print_implicits"

(* Start up the solver and feed it the initial context *)
let warmup (x:int) = assert (x + 1 > x)


%splice_t[test_tot_let] (check (`(
  fun (r:ref U32.t) ->
      (expects (pts_to r full_perm 0ul))
      (provides (fun _ -> pts_to r full_perm 1ul))
      (
        let x = tot 1ul in
        r := x
      )

)))

// %splice_t[test_tot_let] (check (`(
//   fun (r:ref U32.t) ->
//       (expects (pts_to r full_perm 1ul))
//       (provides (fun _ -> pts_to r full_perm 1ul))
//       (
//         let x = !r in
//         r := x
//       )

// )))


// [@@ expect_failure]
// %splice_t[tuple_test] (check (`(
//   fun (r:ref (U32.t & U32.t)) (n1:erased U32.t) (n2:erased U32.t) ->
//            (expects (pts_to r full_perm (reveal n1, reveal n2)))
//     (provides (fun _ -> pts_to r full_perm (reveal n1, reveal n2)))
//     (
//       read #(U32.t & U32.t) r
//     )
// )))

// %splice_t[test_true] (check (`(true)))

// %splice_t[test_write_10] (check  (`(
//    fun (x:ref U32.t)
//      (#n:erased U32.t) -> 
//      (expects (
//         pts_to x full_perm n))
//      (provides (fun _ ->
//         pts_to x full_perm 0ul))
//      (
//        x := 1ul;
//        x := 0ul
//      )
//    )))


// %splice_t[test_read] (check (`(
//   fun (r:ref U32.t)
//     (#n:erased U32.t) (#p:perm) ->
//     (expects (
//        pts_to r p n))
//     (provides (fun x ->
//        pts_to r p x))
//     (
//        let x = !r in
//        return x
//     )
// )))

// //Bound variable escapes scope
// [@@ expect_failure]
// %splice_t[test_read_alt_write] (check (`(
//   fun (r:ref U32.t)
//     (#n:erased U32.t) ->
//     (expects (
//        pts_to r full_perm n))
//     (
//        let x = !r in
//        r := x
//     )
// )))


// %splice_t[swap] (check (`(
//   fun (r1 r2:ref U32.t)
//     (#n1 #n2:erased U32.t) ->
//     (expects  (
//       pts_to r1 full_perm n1 *
//       pts_to r2 full_perm n2))
//     (provides (fun _ ->
//       pts_to r1 full_perm n2 *
//       pts_to r2 full_perm n1))
//     (
//       let x = !r1 in
//       let y = !r2 in
//       r1 := y;
//       r2 := x
//     )
// )))


// %splice_t[call_swap2] (check (`(
//   fun (r1 r2:ref U32.t)
//     (#n1 #n2:erased U32.t) ->
//     (expects  (
//       pts_to r1 full_perm n1 *
//       pts_to r2 full_perm n2))
//     (provides (fun _ -> 
//       pts_to r1 full_perm n1 *
//       pts_to r2 full_perm n2))
//     (
//       swap r1 r2;
//       swap r1 r2
//     )
// )))


// //
// // swap with elim_pure, bind of ghost and stt
// //

// %splice_t[swap_with_elim_pure] (check (`(
//   fun (r1:ref U32.t) (r2:ref U32.t) (n1:erased U32.t) (n2:erased U32.t) ->
//     (expects (pts_to r1 full_perm n1 * pts_to r2 full_perm n2))
//     (provides (fun _ ->
//                pts_to r1 full_perm n2 * pts_to r2 full_perm n1))
//     (
//       let x = !r1 in
//       let y = !r2 in
//       r1 := y;
//       r2 := x
//     )
// )))

// %splice_t[swap_with_elim_pure_and_atomic] (check (`(
//   fun (r1:ref U32.t) (r2:ref U32.t) (n1:erased U32.t) (n2:erased U32.t) ->
//     (expects (pts_to r1 full_perm n1 * pts_to r2 full_perm n2))
//     (provides (fun _ ->
//                pts_to r1 full_perm n2 * pts_to r2 full_perm n1))
//     (
//       let x = read_atomic r1 in
//       let y = read_atomic r2 in
//       write_atomic r1 y;
//       write_atomic r2 x
//     )
// )))

// %splice_t[intro_pure_example] (check (`(
//   fun (r:ref U32.t) (n1:erased U32.t) (n2:erased U32.t) ->
//     (expects (pts_to r full_perm n1 * pure (eq2_prop (reveal n1) (reveal n2))))
//     (provides (fun x -> pts_to r full_perm n2 * pure (eq2_prop (reveal n2) (reveal n1))))
//     (
//        ()
//     )
// )))

// %splice_t[if_example] (check (`(
//   fun (r:ref U32.t) (n:erased U32.t{eq2_prop (U32.v (reveal n)) 1}) (b:bool) ->
//     (expects (pts_to r full_perm n))
//     (provides (fun _ -> pts_to r full_perm (U32.add (reveal n) 2ul)))
//     (
//       let x = read_atomic r in
//       if b
//       then r := (U32.add x 2ul)
//       else write_atomic r 3ul
//     )
// )))

// //#push-options "--ugly --print_implicits"
// %splice_t[elim_intro_exists] (check (`(
//   fun (r:ref U32.t) ->
//     (expects (exists n. pts_to r full_perm n))
//     (provides (fun _ -> exists n. pts_to r full_perm n))
//     (
//       intro (exists n. pts_to r full_perm n) _
//     )
// )))

// // type dummy = | PatVars
// // assume val fresh : dummy
// // let tm = (`(
// //   fun (r:ref UInt32.t) ->
// //     (expects (exists_ (fun n -> pts_to r full_perm n)))
// //     (provides (fun _ -> exists_ (fun n -> pts_to r full_perm n)))
// //     (
// //       let n = elim_exists _ in
// //       let PatVars p n = fresh in
// //       assert (pts_to r p n);
// //       let reveal_n = stt_ghost_reveal UInt32.t n in
// //       intro_exists (fun n -> pts_to r full_perm n) reveal_n
// //     )
// // ))

// %splice_t[while_test] (check (`(
//   fun (r:ref U32.t) ->
//     (expects (exists (b:bool) n. pts_to r full_perm n))
//     (provides (fun _ -> exists n. pts_to r full_perm n))
//     (
//       intro (exists (b:bool) n. pts_to r full_perm n) false _;
//       while
//         (invariant (fun b -> exists n. pts_to r full_perm n))
//         (
//           intro (exists n. pts_to r full_perm n) _;
//           return true
//         )
//         (
//           intro (exists (b:bool) n. pts_to r full_perm n) true _;
//           return ()
//         )
//     )
// )))


// assume
// val pred (b:bool) : vprop
// assume
// val read_pred (_:unit) (#b:erased bool)
//     : stt bool (pred b) (fun r -> pred r)
    
// %splice_t[while_test_alt] (check (`(
//   fun (r:ref U32.t) ->
//     (expects (exists (b:bool) n. pts_to r full_perm n * pred b))
//     (provides (fun _ -> exists n. pts_to r full_perm n * pred false))
//     (
//       while
//         (invariant (fun b -> exists n. pts_to r full_perm n * pred b))
//         (
//           let x = read_pred () in
//           return x
//         )
//         (
//           ()
//         )
//     )
// )))

// #set-options "--fuel 2 --ifuel 2"


// %splice_t[infer_read_ex] (check (`(
//   fun (r:ref U32.t) ->
//     (expects (exists n. pts_to r full_perm n))
//     (provides (fun _ -> exists n. pts_to r full_perm n))
//     (
//         let x = !r in
//         ()
//     ))))


// %splice_t[while_count] (check (`(
//   let open FStar.UInt32 in
//   fun (r:ref t) ->
//     (expects (exists n. pts_to r full_perm n))
//     (provides (fun _ -> pts_to r full_perm 10ul))
//     (
//       while
//         (invariant (fun b ->
//             exists n. pts_to r full_perm n *
//                  pure (eq2_prop b (n <> 10ul))))
//         (let x = !r in
//          return (x <> 10ul))
//         ( 
//           let x = !r in
//           if x <^ 10ul
//           then (r := x +^ 1ul; ())
//           else (r := x -^ 1ul; ())
//         );
//       ())
// )))


// %splice_t[test_par] (check (`(
//   fun (r1 r2:ref U32.t) (n1 n2:erased U32.t) ->
//     (expects (pts_to r1 full_perm n1 *
//               pts_to r2 full_perm n2))
//     (provides (fun _ -> pts_to r1 full_perm 1ul *
//                         pts_to r2 full_perm 1ul))
//     (
//       par
//         (pts_to r1 full_perm n1)
//         (r1 := 1ul)
//         (fun _ -> pts_to r1 full_perm 1ul)

//         (pts_to r2 full_perm n2)
//         (r2 := 1ul)
//         (fun _ -> pts_to r2 full_perm 1ul)
//     )
// )))

// // A test for rewrite
// let mpts_to (r:ref U32.t) (n:erased U32.t) : vprop = pts_to r full_perm n

// %splice_t[rewrite_test] (check (`(
// 		fun (r:ref U32.t) (n:erased U32.t) ->
// 				(expects (mpts_to r n))
// 				(provides (fun _ -> mpts_to r 1ul))
// 				(
// 						rewrite (mpts_to r n) (pts_to r full_perm n);
// 						r := 1ul;
// 						rewrite (pts_to r full_perm 1ul) (mpts_to r 1ul)
// 				)
// )))

// %splice_t[test_local] (check (`(
//   fun (r:ref U32.t) (n:erased U32.t) ->
//     (expects (pts_to r full_perm n))
//     (provides (fun _ -> pts_to r full_perm 0ul))
//     (
//       let x = local 0ul in
//       let y = !x in
//       r := y;
//       intro (exists n. pts_to x full_perm n) _
//     )
// )))

// %splice_t[count_local] (check (`(
//   fun (r:ref int) (n:int) ->
//     (expects (pts_to r full_perm (hide 0)))
//     (provides (fun _ -> pts_to r full_perm n))
//     (
//       let i = local 0 in
//       while
//         (invariant (fun b -> exists m. pts_to i full_perm m *
//                              pure (eq2_prop b (m <> n))))
//         (let m = !i in return (m <> n))
//         (let m = !i in i := m + 1; ());
//       let x = !i in
//       r := x;
//       intro (exists m. pts_to i full_perm m) _
//     )
// )))

// let rec sum_spec (n:nat) : nat =
//   if n = 0 then 0 else n + sum_spec (n - 1)

// let zero : nat = 0

// %splice_t[sum] (check (`(
//   fun (r:ref nat) (n:nat) ->
//     (expects (exists n. pts_to r full_perm n))
//     (provides (fun _ -> pts_to r full_perm (sum_spec n)))
//     (
//       let i = local zero in
//       let sum = local zero in
//       intro (exists b. exists m s.
//                        pts_to i full_perm m *
//                        pts_to sum full_perm s *
//                        pure (and_prop (eq2_prop s (sum_spec m)) (eq2_prop b (m <> n)))) (zero <> n);
//       while
//         (invariant (fun b -> exists m s.
//                              pts_to i full_perm m *
//                              pts_to sum full_perm s *
//                              pure (and_prop (eq2_prop s (sum_spec m)) (eq2_prop b (m <> n)))))
//         (let m = !i in return (m <> n))
//         (let m = !i in
//          let s = !sum in
//          i := (m + 1);
//          sum := s + m + 1;
//          intro (exists b. exists m s.
//                           pts_to i full_perm m *
//                           pts_to sum full_perm s *
//                           pure (and_prop (eq2_prop s (sum_spec m)) (eq2_prop b (m <> n)))) (m + 1 <> n));
//       let s = !sum in
//       r := s;
//       intro (exists m. pts_to i full_perm m) _;
//       intro (exists s. pts_to sum full_perm s) _
//     )
// )))

// %splice_t[if_then_else_in_specs] (check (`(
//   fun (r:ref U32.t) ->
//       (expects (if true
//                 then pts_to r full_perm 0ul
//                 else pts_to r full_perm 1ul))
//       (provides (fun _ -> if true
//                           then pts_to r full_perm 1ul
//                           else pts_to r full_perm 0ul))
                               
//       (
//         // need this for typechecking !r on the next line,
//         //   with inference of implicits
//         rewrite (if true then pts_to r full_perm 0ul else pts_to r full_perm 1ul)
//                 (pts_to r full_perm 0ul);
//         let x = !r in
//         r := U32.add x 1ul
//       )

// )))

// %splice_t[if_then_else_in_specs2] (check (`(
//   fun (r:ref U32.t) (b:bool) ->
//       (expects (pts_to r full_perm (if b then 0ul else 1ul)))
//       (provides (fun _ -> pts_to r full_perm (if b then 1ul else 2ul)))
//       (
//         let x = !r in
//         r := U32.add x 1ul
//       )

// )))
