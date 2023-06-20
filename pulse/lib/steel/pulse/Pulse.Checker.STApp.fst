module Pulse.Checker.STApp

module T = FStar.Tactics.V2
module RT = FStar.Reflection.Typing

open Pulse.Syntax
open Pulse.Typing
open Pulse.Checker.Pure
open Pulse.Checker.Common
module RU = Pulse.RuntimeUtils
module P = Pulse.Syntax.Printer

module FV = Pulse.Typing.FV

let check_stapp
  (allow_inst:bool)
  (g:env)
  (t:st_term{Tm_STApp? t.term})
  (pre:term)
  (pre_typing:tot_typing g pre tm_vprop)
  (post_hint:post_hint_opt g)
  (check':bool -> check_t)
  : T.Tac (checker_result_t g pre post_hint) =
  // maybe_log t;
  let range = t.range in
  let Tm_STApp { head; arg_qual=qual; arg } = t.term in

  //
  // c is the comp remaining after applying head to arg,
  //
  let infer_logical_implicits_and_check
    (t:term)
    (c:comp{C_Tot? c}) : T.Tac _ =

    match c with
    | C_Tot ty ->
      begin match is_arrow ty with
            | Some (_, Some Implicit, _) -> 
              //Some implicits to follow
              let t = Pulse.Checker.Inference.infer g t ty pre range in
              check' false g t pre pre_typing post_hint
            | _ ->
              T.fail "Unexpected c in infer_logical_implicits_and_check"
      end

    | _ ->
      T.fail "Unexpected c in infer_logical_implicits_and_check" in

  T.or_else
    (fun _ -> 
      let g = push_context "pure_app" t.range g in    
      let pure_app = tm_pureapp head qual arg in
      let t, ty = instantiate_term_implicits g pure_app in
      infer_logical_implicits_and_check t (C_Tot ty))
    (fun _ ->
      let g = push_context "st_app" t.range g in        
      let (| head, ty_head, dhead |) = check_term g head in
      if RU.debug_at_level (fstar_env g) "st_app" then
        T.print (Printf.sprintf "st_app: head = %s, ty_head = %s\n"
                   (P.term_to_string head)
                   (P.term_to_string ty_head));
      match is_arrow ty_head with
      | Some ({binder_ty=formal;binder_ppname=ppname}, bqual, comp_typ) ->
        is_arrow_tm_arrow ty_head;
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
           let d = T_STApp g head formal qual comp_typ arg (E dhead) (E darg) in
          //  T.print (Printf.sprintf "ST application trying to frame, context: %s and pre: %s\n"
          //             (Pulse.Syntax.Printer.term_to_string pre)
          //             (Pulse.Syntax.Printer.term_to_string (comp_pre (open_comp_with comp_typ arg))));
           repack (try_frame_pre pre_typing d) post_hint
         | _ ->
           let t = tm_pureapp head qual arg in
           let comp_typ = open_comp_with comp_typ arg in
           infer_logical_implicits_and_check t comp_typ
        else 
         fail g None (Printf.sprintf "(%s) Unexpected qualifier in head type %s of stateful application: head = %s, arg = %s"
                                (T.range_to_string t.range)
                                (P.term_to_string ty_head)
                                (P.term_to_string head)
                                (P.term_to_string arg))
    
     | _ -> fail g None (Printf.sprintf "Unexpected head type in impure application: %s" (P.term_to_string ty_head)))
