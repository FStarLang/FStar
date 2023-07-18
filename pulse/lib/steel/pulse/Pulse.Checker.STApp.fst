module Pulse.Checker.STApp

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common
open Pulse.Prover
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer

module Prover = Pulse.Prover

module FV = Pulse.Typing.FV
let debug_log (g:env) (f:unit -> T.Tac unit) : T.Tac unit = if RU.debug_at_level (fstar_env g) "st_app" then f () else ()

let canon_comp (c:comp_st) : comp_st = 
  match readback_comp (elab_comp c) with
  | None -> c
  | Some (C_Tot _) -> c //should be impossible
  | Some c' ->
    c'
  
let canonicalize_st_typing (#g:env) (#t:st_term) (#c:comp_st) (d:st_typing g t c)
  : st_typing g t (canon_comp c)
  = let c' = canon_comp c in
    let x = fresh g in
    assume ( ~(x `Set.mem` freevars (comp_post c)) /\
            ~(x `Set.mem` freevars (comp_post c')) );
    assume (st_equiv_pre c c');
    let st_eq 
      : st_equiv g c c'
      = ST_VPropEquiv g c c' x (magic()) (magic()) (magic()) (magic()) (magic())
    in
    T_Equiv _ _ _ _ d st_eq

let coerce_eq (#a #b:Type) (x:a) (_:squash (a === b)) : y:b { y == x } = x

#push-options "--z3rlimit_factor 4 --fuel 1 --ifuel 1"
let check_st_app
  (g:env)
  (t:st_term { Tm_STApp? t.term })
  (ctxt:vprop)
  (ctxt_typing:tot_typing g ctxt tm_vprop)
  (post_hint:post_hint_opt g)
  : T.Tac (checker_result_t g ctxt post_hint) =

  let g = push_context "st_app" t.range g in
  let range = t.range in
  let Tm_STApp { head; arg_qual=qual; arg } = t.term in
  let (| head, ty_head, dhead |) = check_term g head in
  debug_log g (fun _ ->
    T.print (Printf.sprintf "st_app: head = %s, ty_head = %s\n"
               (P.term_to_string head)
               (P.term_to_string ty_head)));
    
  match is_arrow ty_head with
  | Some ({binder_ty=formal;binder_ppname=ppname}, bqual, comp_typ) ->
    is_arrow_tm_arrow ty_head;
    debug_log g (fun _ ->
      T.print (Printf.sprintf "st_app, readback comp as %s\n"
                 (P.comp_to_string comp_typ)));
    
    assert (ty_head ==
            tm_arrow ({binder_ty=formal;binder_ppname=ppname}) bqual comp_typ);
    
    if qual = bqual
    then
      let (| arg, darg |) = check_term_with_expected_type g arg formal in
      match comp_typ with
      | C_ST res
      | C_STAtomic _ res
      | C_STGhost _ res ->
        // This is a real ST application
        let d : st_typing _ _ (open_comp_with comp_typ arg) =
          T_STApp g head formal qual comp_typ arg (E dhead) (E darg) in
        let d = canonicalize_st_typing d in
        let t = wr (Tm_STApp {head; arg_qual=qual; arg}) in
        let c = (canon_comp (open_comp_with comp_typ arg)) in
        let d : st_typing g t c = d in

        repack (try_frame_pre ctxt_typing d) post_hint t.range
       | _ ->
         fail g (Some t.range) "Expected an effectful application; got a pure term (could it be partially applied by mistake?)"
     else fail g (Some t.range) (Printf.sprintf "Unexpected qualifier in head type %s of stateful application: head = %s, arg = %s"
                 (P.term_to_string ty_head)
                 (P.term_to_string head)
                 (P.term_to_string arg))

  | _ -> fail g (Some t.range) (Printf.sprintf "Unexpected head type in impure application: %s" (P.term_to_string ty_head))
#pop-options

// #push-options "--fuel 0 --ifuel 1 --z3rlimit_factor 2"
// let check_stapp
//   (allow_inst:bool)
//   (g:env)
//   (t:st_term{Tm_STApp? t.term})
//   (pre:term)
//   (pre_typing:tot_typing g pre tm_vprop)
//   (post_hint:post_hint_opt g)
//   (frame_pre:bool)
//   (check':bool -> check_t)
//   : T.Tac (checker_result_t g pre post_hint frame_pre) =
//   // maybe_log t;
//   let range = t.range in
//   let Tm_STApp { head; arg_qual=qual; arg } = t.term in

//   //
//   // c is the comp remaining after applying head to arg,
//   //
//   // let infer_logical_implicits_and_check
//   //   (t:term)
//   //   (c:comp{C_Tot? c}) : T.Tac _ =

//   //   match c with
//   //   | C_Tot ty ->
//   //     begin match is_arrow ty with
//   //           | Some (_, Some Implicit, _) -> 
//   //             //Some implicits to follow
//   //             let t = Pulse.Checker.Inference.infer g t ty pre range in
//   //             check' false g t pre pre_typing post_hint
//   //           | _ ->
//   //             T.fail "Unexpected c in infer_logical_implicits_and_check"
//   //     end

//   //   | _ ->
//   //     T.fail "Unexpected c in infer_logical_implicits_and_check" in

//   let check_st_app ()  : T.Tac (checker_result_t g pre post_hint frame_pre) =
//     let g = push_context "st_app" t.range g in        
//     let (| head, ty_head, dhead |) = check_term g head in
//     debug_log g (fun _ ->
//         T.print (Printf.sprintf "st_app: head = %s, ty_head = %s\n"
//                    (P.term_to_string head)
//                    (P.term_to_string ty_head)));
//     match is_arrow ty_head with
//     | Some ({binder_ty=formal;binder_ppname=ppname}, bqual, comp_typ) ->
//         is_arrow_tm_arrow ty_head;
//         debug_log g (fun _ ->
//          T.print (Printf.sprintf "st_app, readback comp as %s\n"
//                    (P.comp_to_string comp_typ)));
    
//         assert (ty_head ==
//                 tm_arrow ({binder_ty=formal;binder_ppname=ppname}) bqual comp_typ);
//         if qual = bqual
//         then
//          let (| arg, darg |) = check_term_with_expected_type g arg formal in
//          match comp_typ with
//          | C_ST res
//          | C_STAtomic _ res
//          | C_STGhost _ res ->
//            // This is a real ST application
//            let d : st_typing _ _ (open_comp_with comp_typ arg) = T_STApp g head formal qual comp_typ arg (E dhead) (E darg) in
//            let d' = canonicalize_st_typing d in
//           //  T.print (Printf.sprintf "ST application trying to frame, context: %s and pre: %s\n"
//           //             (Pulse.Syntax.Printer.term_to_string pre)
//           //             (Pulse.Syntax.Printer.term_to_string (comp_pre (open_comp_with comp_typ arg))));
//           if frame_pre
//           then repack (try_frame_pre pre_typing d') post_hint
//           else if Some? post_hint
//           then T.fail "stapp: frame_pre is false but post_hint is set, bailing"
//           else (| _, _, d' |)
//          | _ ->
//            fail g (Some t.range) "Expected an effectful application; got a pure term (could it be partially applied by mistake?)"
//         else 
//          fail g (Some t.range) (Printf.sprintf "Unexpected qualifier in head type %s of stateful application: head = %s, arg = %s"
//                                   (P.term_to_string ty_head)
//                                   (P.term_to_string head)
//                                   (P.term_to_string arg))
    
//      | _ -> fail g (Some t.range) (Printf.sprintf "Unexpected head type in impure application: %s" (P.term_to_string ty_head))
//   in

//   let g = push_context "pure_app" t.range g in    
//   let pure_app = tm_pureapp head qual arg in
//   let t, ty = instantiate_term_implicits g pure_app in
//   match is_arrow ty with
//   | Some (_, Some Implicit, _) -> 
//     //Some implicits to follow
//     let t = Pulse.Checker.Inference.infer g t ty pre range in
//     check' false g t pre pre_typing post_hint frame_pre
//   | _ ->
//     check_st_app ()
// #pop-options
