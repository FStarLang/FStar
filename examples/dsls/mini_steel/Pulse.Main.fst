module Pulse.Main

module T = FStar.Tactics
module R = FStar.Reflection
module RT = Refl.Typing
open FStar.Tactics
open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker
open Pulse.Elaborate.Pure
open Pulse.Elaborate
open Pulse.Soundness

open Pulse.Parser
module P = Pulse.Syntax.Printer

let main' (t:term) (pre:term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.typing g (fst r) (snd r)})
  = T.print (P.term_to_string t);
    match Pulse.Soundness.Common.check_top_level_environment g with
    | None -> T.fail "pulse main: top-level environment does not include stt at the expected types"
    | Some g ->
      let (| ty, pre_typing |) = check_tot g [] pre in
      if ty = Tm_VProp
      then let pre_typing : tot_typing g [] pre Tm_VProp = E pre_typing in
           let (| t, c, t_typing |) = check g [] t pre pre_typing None in
           let refl_e = elab_src_typing t_typing in
           let refl_t = elab_pure_comp c in
           soundness_lemma g [] t c t_typing;
           (refl_e, refl_t)
      else T.fail "pulse main: cannot typecheck pre at type vprop"

let main t pre : RT.dsl_tac_t = main' t pre

let erased_lid = ["Pulse"; "Steel"; "Wrapper"; "erased"]
let hide_lid = ["Pulse"; "Steel"; "Wrapper"; "hide"]
let reveal_lid = ["Pulse"; "Steel"; "Wrapper"; "reveal"]
let u32_lid = ["Pulse"; "Steel"; "Wrapper"; "u32"]
let ref_lid = ["Pulse"; "Steel"; "Wrapper"; "ref"]
let pts_to_lid = ["Pulse"; "Steel"; "Wrapper"; "pts_to"]
let read_lid = ["Pulse"; "Steel"; "Wrapper"; "read"]
let write_lid = ["Pulse"; "Steel"; "Wrapper"; "write"]

[@@plugin]
let parse_and_check (s:string) : RT.dsl_tac_t = main (parse s) Tm_Emp

let err a = either a string

let error #a msg : T.Tac (err a) = Inr msg

let (let?) (o:err 'a) (f:'a -> T.Tac (err 'b)) 
  : T.Tac (err 'b)
  = match o with
    | Inr msg -> Inr msg
    | Inl v -> f v

let unexpected_term msg t = 
  error (Printf.sprintf "Unexpected term (%s): %s"
                            msg
                            (T.term_to_string t))

let readback_ty (t:R.term)
  : T.Tac (err term)
  = try match Checker.readback_ty t with
        | None -> unexpected_term "readback_ty failed" t
        | Some t -> Inl #term t
    with 
      | TacticFailure msg -> 
        unexpected_term msg t
      | _ ->
        unexpected_term "readback failed" t

let readback_comp (t:R.term)
  : T.Tac (err comp)
  = try match Checker.readback_comp t with
        | None -> unexpected_term "computation" t
        | Some c -> Inl #comp c
    with
      | TacticFailure msg -> 
        unexpected_term msg t
      | _ ->
        unexpected_term "readback failed" t

let transate_binder (b:R.binder)
  : T.Tac (err (binder & option qualifier))
  = let bv, (aq, attrs) = R.inspect_binder b in
    match attrs, aq with
    | _::_, _ -> error "Unexpected attribute"
    | _, R.Q_Meta _ -> error "Unexpected binder qualifier"
    | _ -> 
      let q = Checker.readback_qual aq in
      RT.pack_inspect_binder b;  // This does not have SMTPat
      let bv_view = R.inspect_bv bv in
      assume (bv_view.bv_ppname == "_" /\ bv_view.bv_index == 0);
      let? b_ty' = readback_ty bv_view.bv_sort in      
      Inl ({binder_ty=b_ty';binder_ppname=bv_view.bv_ppname}, q)


let rec translate_term' (t:R.term)
  : T.Tac (err term)
  = match R.inspect_ln t with
    | R.Tv_Abs x body ->
      let? b, q = transate_binder x in
      begin
      match R.inspect_ln body with
      | R.Tv_AscribedT body t None false -> (
        match? readback_comp t with
        | C_ST st ->
          let? body = translate_st_term body in
          Inl (Tm_Abs b q st.pre body (Some st.post))
        | _ -> 
          let? body = translate_st_term body in
          Inl (Tm_Abs b q Tm_Emp body None)
      )

      | _ -> 
        let? body = translate_term body in
        Inl (Tm_Abs b q Tm_Emp body None)
      end

    | _ -> 
      unexpected_term "translate_term'" t

and translate_st_term (t:R.term)
  : T.Tac (err term)
  = match R.inspect_ln t with 
    | R.Tv_App _ _ -> (
      let? t = readback_ty t in
      match t with
      | Tm_PureApp head q arg -> Inl (Tm_STApp head q arg)
      | _ -> Inl t
    )

    | R.Tv_Let false [] bv def body ->
      let? def = translate_st_term def in 
      let? body = translate_st_term body in 
      Inl (Tm_Bind def body)

    | _ ->
      unexpected_term "st_term" t
  
and translate_term (t:R.term)
  : T.Tac (err term)
  = match readback_ty t with
    | Inl t -> Inl t
    | _ -> translate_term' t

let check' (t:R.term) (g:RT.fstar_top_env)
  : T.Tac (r:(R.term & R.typ){RT.typing g (fst r) (snd r)})
  = match translate_term t with
    | Inr msg -> T.fail (Printf.sprintf "Failed to translate term: %s" msg)
    | Inl t -> 
      T.print (Printf.sprintf "Translated term is\n%s\n" (P.term_to_string t));
      main t Tm_Emp g

[@@plugin]
let check (t:R.term) : RT.dsl_tac_t = check' t

  // let e = parse "fun (n:Pulse.Steel.Wrapper.erased) { emp } -> (fun (r:Pulse.Steel.Wrapper.ref) { emp } -> (fun (x:Pulse.Steel.Wrapper.u32) {((Pulse.Steel.Wrapper.pts_to r) (Pulse.Steel.Wrapper.reveal n))} -> (Pulse.Steel.Wrapper.write (n, r, x))))" in

// // "(fun (n:erased) (r:ref) (x:u32) -> \
// //             { pts_to r (reveal n) } call: write(r, x))"
// let bar = (
// Tm_Abs
//   (mk_binder "n" (Tm_FVar erased_lid))  //n:erased u32
//   Tm_Emp
//   (Tm_Abs
//      (mk_binder "r" (Tm_FVar ref_lid))  //r:ref
//      Tm_Emp
//      (Tm_Abs
//         (mk_binder "x" (Tm_FVar u32_lid))  //x:u32
//         (Tm_PureApp
//           (Tm_PureApp
//              (Tm_FVar pts_to_lid)
//              (mk_bvar "r" 1))
//           (Tm_PureApp
//              (Tm_FVar reveal_lid)
//              (mk_bvar "n" 2))
//         )
//         (Tm_STApp
//            (Tm_PureApp
//               (Tm_PureApp
//                  (Tm_FVar write_lid)
//                  (mk_bvar "n" 2)
//               )
//               (mk_bvar "r" 1)
//            )
//            (mk_bvar "x" 0)
//         )
//      )
//   )
// )

// [@@plugin]
// let check_bar (_:unit) : RT.dsl_tac_t =
//   main bar Tm_Emp

// // fun (n:erased) (r1:ref) (x:u32) (r2:ref) -> \\
// //   {pts_to r1 (reveal n) `star` pts_to r2 (reveal n)} call: write (r1, x))

// let baz = (
// Tm_Abs
//   (mk_binder "n" (Tm_FVar erased_lid))  // n:erased
//   Tm_Emp
//   (
//     Tm_Abs
//       (mk_binder "r1" (Tm_FVar ref_lid))  // r1:ref
//       Tm_Emp
//       (
//         Tm_Abs
//           (mk_binder "x" (Tm_FVar u32_lid))  // x:u32
//           Tm_Emp
//           (
//             Tm_Abs
//               (mk_binder "r2" (Tm_FVar ref_lid))  // r2:ref
//               (
//                 Tm_Star
//                   (
//                     Tm_PureApp
//                       (
//                         Tm_PureApp
//                           (Tm_FVar pts_to_lid)
//                           (mk_bvar "r2" 0)
//                       )
//                       (
//                         Tm_PureApp
//                           (Tm_FVar reveal_lid)
//                           (mk_bvar "n" 3)
//                       )
//                   )
//                   (
//                     Tm_PureApp
//                       (
//                         Tm_PureApp
//                           (Tm_FVar pts_to_lid)
//                           (mk_bvar "r1" 2)
//                       )
//                       (
//                         Tm_PureApp
//                           (Tm_FVar reveal_lid)
//                           (mk_bvar "n" 3)
//                       )
//                   )
//               )
//               (
//                 Tm_STApp
//                   (
//                     Tm_PureApp
//                       (
//                         Tm_PureApp
//                           (Tm_FVar write_lid)
//                           (mk_bvar "n" 3)
//                       )
//                       (mk_bvar "r1" 2)
//                   )
//                   (mk_bvar "x" 1)
//               )
//           )
//       )
//   )
// )

// [@@plugin]
// let check_baz (_:unit) : RT.dsl_tac_t =
//   main baz Tm_Emp
