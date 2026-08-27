open Prims
type lcomp_with_binder =
  (FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option *
    FStarC_TypeChecker_Common.lcomp)
let dbg_bind : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Bind"
let dbg_Coercions : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "Coercions"
let dbg_Dec : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Dec"
let dbg_Extraction : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "Extraction"
let dbg_LayeredEffects : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "LayeredEffects"
let dbg_LayeredEffectsApp : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "LayeredEffectsApp"
let dbg_Pat : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Pat"
let dbg_Rel : Prims.bool FStarC_Effect.ref= FStarC_Debug.get_toggle "Rel"
let dbg_ResolveImplicitsHook : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "ResolveImplicitsHook"
let dbg_Return : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "Return"
let dbg_Simplification : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "Simplification"
let dbg_SMTEncodingReify : Prims.bool FStarC_Effect.ref=
  FStarC_Debug.get_toggle "SMTEncodingReify"
let new_implicit_var (reason : Prims.string) (r : FStarC_Range_Type.t)
  (env : FStarC_TypeChecker_Env.env) (k : FStarC_Syntax_Syntax.typ)
  (unrefine : Prims.bool) :
  (FStarC_Syntax_Syntax.term * (FStarC_Syntax_Syntax.ctx_uvar *
    FStarC_Range_Type.t) * FStarC_TypeChecker_Common.guard_t)=
  FStarC_TypeChecker_Env.new_implicit_var_aux reason r env k
    FStarC_Syntax_Syntax.Strict FStar_Pervasives_Native.None unrefine
let close_guard_implicits (env : FStarC_TypeChecker_Env.env)
  (solve_deferred : Prims.bool) (xs : FStarC_Syntax_Syntax.binders)
  (g : FStarC_TypeChecker_Env.guard_t) : FStarC_TypeChecker_Common.guard_t=
  let uu___ =
    let uu___1 = FStarC_Options.eager_subtyping () in
    if uu___1 then true else solve_deferred in
  if uu___
  then
    let uu___1 =
      let uu___2 =
        FStarC_Class_Listlike.to_list (FStarC_CList.listlike_clist ())
          g.FStarC_TypeChecker_Common.deferred in
      FStarC_List.partition
        (fun uu___3 ->
           match uu___3 with
           | (uu___4, uu___5, p) ->
               FStarC_TypeChecker_Rel.flex_prob_closing env xs p) uu___2 in
    match uu___1 with
    | (solve_now, defer) ->
        ((let uu___3 = FStarC_Effect.op_Bang dbg_Rel in
          if uu___3
          then
            (FStarC_Format.print_string "SOLVE BEFORE CLOSING:\n";
             FStarC_List.iter
               (fun uu___6 ->
                  match uu___6 with
                  | (uu___7, s, p) ->
                      let uu___8 =
                        FStarC_TypeChecker_Rel.prob_to_string env p in
                      FStarC_Format.print2 "%s: %s\n" s uu___8) solve_now;
             FStarC_Format.print_string " ...DEFERRED THE REST:\n";
             FStarC_List.iter
               (fun uu___8 ->
                  match uu___8 with
                  | (uu___9, s, p) ->
                      let uu___10 =
                        FStarC_TypeChecker_Rel.prob_to_string env p in
                      FStarC_Format.print2 "%s: %s\n" s uu___10) defer;
             FStarC_Format.print_string "END\n")
          else ());
         (let g1 =
            let uu___3 =
              let uu___4 =
                FStarC_Class_Listlike.from_list
                  (FStarC_CList.listlike_clist ()) solve_now in
              {
                FStarC_TypeChecker_Common.guard_f =
                  (g.FStarC_TypeChecker_Common.guard_f);
                FStarC_TypeChecker_Common.deferred_to_tac =
                  (g.FStarC_TypeChecker_Common.deferred_to_tac);
                FStarC_TypeChecker_Common.deferred = uu___4;
                FStarC_TypeChecker_Common.univ_ineqs =
                  (g.FStarC_TypeChecker_Common.univ_ineqs);
                FStarC_TypeChecker_Common.implicits =
                  (g.FStarC_TypeChecker_Common.implicits)
              } in
            FStarC_TypeChecker_Rel.solve_non_tactic_deferred_constraints
              false env uu___3 in
          let g2 =
            let uu___3 =
              FStarC_Class_Listlike.from_list
                (FStarC_CList.listlike_clist ()) defer in
            {
              FStarC_TypeChecker_Common.guard_f =
                (g1.FStarC_TypeChecker_Common.guard_f);
              FStarC_TypeChecker_Common.deferred_to_tac =
                (g1.FStarC_TypeChecker_Common.deferred_to_tac);
              FStarC_TypeChecker_Common.deferred = uu___3;
              FStarC_TypeChecker_Common.univ_ineqs =
                (g1.FStarC_TypeChecker_Common.univ_ineqs);
              FStarC_TypeChecker_Common.implicits =
                (g1.FStarC_TypeChecker_Common.implicits)
            } in
          g2))
  else g
let check_uvars (r : FStarC_Range_Type.t) (t : FStarC_Syntax_Syntax.typ) :
  unit=
  let uvs = FStarC_Syntax_Free.uvars t in
  let uu___ =
    let uu___1 =
      FStarC_Class_Setlike.is_empty
        (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Free.ord_ctx_uvar) uvs in
    Prims.not uu___1 in
  if uu___
  then
    (FStarC_Options.push ();
     FStarC_Options.set_option "hide_uvar_nums" (FStarC_Options.Bool false);
     FStarC_Options.set_option "print_implicits" (FStarC_Options.Bool true);
     (let uu___5 =
        let uu___6 =
          FStarC_Class_Show.show
            (FStarC_FlatSet.showable_set FStarC_Syntax_Free.ord_ctx_uvar
               FStarC_Syntax_Print.showable_ctxu) uvs in
        let uu___7 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
        FStarC_Format.fmt2
          "Unconstrained unification variables %s in type signature %s; please add an annotation"
          uu___6 uu___7 in
      FStarC_Errors.log_issue FStarC_Class_HasRange.hasRange_range r
        FStarC_Errors_Codes.Error_UnconstrainedUnificationVar ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic uu___5));
     FStarC_Options.pop ())
  else ()
let extract_let_rec_annotation (env : FStarC_TypeChecker_Env.env)
  (lb : FStarC_Syntax_Syntax.letbinding) :
  (FStarC_Syntax_Syntax.univ_names * FStarC_Syntax_Syntax.typ *
    FStarC_Syntax_Syntax.term * Prims.bool)=
  let uu___ = lb in
  match uu___ with
  | { FStarC_Syntax_Syntax.lbname = lbname;
      FStarC_Syntax_Syntax.lbunivs = univ_vars;
      FStarC_Syntax_Syntax.lbtyp = t; FStarC_Syntax_Syntax.lbeff = uu___1;
      FStarC_Syntax_Syntax.lbdef = e; FStarC_Syntax_Syntax.lbattrs = uu___2;
      FStarC_Syntax_Syntax.lbpos = uu___3;_} ->
      let rng = FStarC_Syntax_Syntax.range_of_lbname lbname in
      let t1 = FStarC_Syntax_Subst.compress t in
      let uu___4 = FStarC_Syntax_Subst.univ_var_opening univ_vars in
      (match uu___4 with
       | (u_subst, univ_vars1) ->
           let e1 = FStarC_Syntax_Subst.subst u_subst e in
           let t2 = FStarC_Syntax_Subst.subst u_subst t1 in
           ((let uu___6 = FStarC_Effect.op_Bang dbg_Dec in
             if uu___6
             then
               let uu___7 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e1 in
               let uu___8 =
                 FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t2 in
               FStarC_Format.print2
                 "extract_let_rec_annotation lbdef=%s; lbtyp=%s\n" uu___7
                 uu___8
             else ());
            (let env1 = FStarC_TypeChecker_Env.push_univ_vars env univ_vars1 in
             let un_arrow t3 =
               let uu___6 =
                 let uu___7 = FStarC_Syntax_Subst.compress t3 in
                 uu___7.FStarC_Syntax_Syntax.n in
               match uu___6 with
               | FStarC_Syntax_Syntax.Tm_arrow uu___7 ->
                   FStarC_Syntax_Util.arrow_formals_comp_strict t3
               | uu___7 ->
                   FStarC_Errors.raise_error
                     FStarC_Class_HasRange.hasRange_range rng
                     FStarC_Errors_Codes.Fatal_LetRecArgumentMismatch ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic
                        [FStarC_Errors_Msg.text
                           "Recursive functions must be introduced at arrow types."]) in
             let reconcile_let_rec_ascription_and_body_type tarr lbtyp_opt
               n_opt =
               let get_decreases c =
                 FStarC_Util.prefix_until
                   (fun uu___6 ->
                      match uu___6 with
                      | FStarC_Syntax_Syntax.DECREASES uu___7 -> true
                      | uu___7 -> false) (FStarC_Syntax_Util.comp_flags c) in
               let fallback uu___6 =
                 let uu___7 = FStarC_Syntax_Util.arrow_formals_comp tarr in
                 match uu___7 with
                 | (bs, c) ->
                     let uu___8 = get_decreases c in
                     (match uu___8 with
                      | FStar_Pervasives_Native.Some
                          (pfx, FStarC_Syntax_Syntax.DECREASES d, sfx) ->
                          let c1 =
                            FStarC_TypeChecker_Env.comp_set_flags env1 c
                              (FStarC_List.op_At pfx sfx) in
                          let uu___9 = FStarC_Syntax_Util.arrow bs c1 in
                          (uu___9, tarr, true)
                      | uu___9 -> (tarr, tarr, true)) in
               match lbtyp_opt with
               | FStar_Pervasives_Native.None -> fallback ()
               | FStar_Pervasives_Native.Some annot ->
                   let uu___6 =
                     match n_opt with
                     | FStar_Pervasives_Native.Some n ->
                         FStarC_TypeChecker_Normalize.get_n_binders env1 n
                           tarr
                     | FStar_Pervasives_Native.None -> un_arrow tarr in
                   (match uu___6 with
                    | (bs, c) ->
                        let n_bs = FStarC_List.length bs in
                        let uu___7 =
                          FStarC_TypeChecker_Normalize.get_n_binders env1
                            n_bs annot in
                        (match uu___7 with
                         | (bs', c') ->
                             (if (FStarC_List.length bs') <> n_bs
                              then
                                FStarC_Errors.raise_error
                                  FStarC_Class_HasRange.hasRange_range rng
                                  FStarC_Errors_Codes.Fatal_LetRecArgumentMismatch
                                  ()
                                  (Obj.magic
                                     FStarC_Errors_Msg.is_error_message_list_doc)
                                  (Obj.magic
                                     [FStarC_Errors_Msg.text
                                        "Arity mismatch on let rec annotation";
                                     FStarC_Errors_Msg.text "(explain)"])
                              else ();
                              (let move_decreases d flags flags' =
                                 let d' =
                                   let s =
                                     FStarC_Syntax_Util.rename_binders bs bs' in
                                   FStarC_Syntax_Subst.subst_decreasing_order
                                     s d in
                                 let c1 =
                                   let uu___9 =
                                     FStarC_TypeChecker_Env.push_binders env1
                                       bs in
                                   FStarC_TypeChecker_Env.comp_set_flags
                                     uu___9 c flags in
                                 let tarr1 = FStarC_Syntax_Util.arrow bs c1 in
                                 let c'1 =
                                   let uu___9 =
                                     FStarC_TypeChecker_Env.push_binders env1
                                       bs' in
                                   FStarC_TypeChecker_Env.comp_set_flags
                                     uu___9 c'
                                     ((FStarC_Syntax_Syntax.DECREASES d') ::
                                     flags') in
                                 let tannot =
                                   FStarC_Syntax_Util.arrow bs' c'1 in
                                 (tarr1, tannot, true) in
                               let uu___9 =
                                 let uu___10 = get_decreases c in
                                 let uu___11 = get_decreases c' in
                                 (uu___10, uu___11) in
                               match uu___9 with
                               | (FStar_Pervasives_Native.None, uu___10) ->
                                   (tarr, annot, false)
                               | (FStar_Pervasives_Native.Some
                                  (pfx, FStarC_Syntax_Syntax.DECREASES d,
                                   sfx),
                                  FStar_Pervasives_Native.Some
                                  (pfx', FStarC_Syntax_Syntax.DECREASES d',
                                   sfx')) ->
                                   (FStarC_Errors.log_issue
                                      FStarC_Class_HasRange.hasRange_range
                                      rng
                                      FStarC_Errors_Codes.Warning_DeprecatedGeneric
                                      ()
                                      (Obj.magic
                                         FStarC_Errors_Msg.is_error_message_list_doc)
                                      (Obj.magic
                                         [FStarC_Errors_Msg.text
                                            "This definitions has multiple decreases clauses.";
                                         FStarC_Errors_Msg.text
                                           "The decreases clause on the declaration is ignored, please remove it."]);
                                    move_decreases d
                                      (FStarC_List.op_At pfx sfx)
                                      (FStarC_List.op_At pfx' sfx'))
                               | (FStar_Pervasives_Native.Some
                                  (pfx, FStarC_Syntax_Syntax.DECREASES d,
                                   sfx),
                                  FStar_Pervasives_Native.None) ->
                                   move_decreases d
                                     (FStarC_List.op_At pfx sfx)
                                     (FStarC_Syntax_Util.comp_flags c')
                               | uu___10 ->
                                   FStarC_Effect.failwith "Impossible")))) in
             let extract_annot_from_body lbtyp_opt =
               let rec aux_lbdef e2 =
                 let e3 = FStarC_Syntax_Subst.compress e2 in
                 match e3.FStarC_Syntax_Syntax.n with
                 | FStarC_Syntax_Syntax.Tm_meta
                     { FStarC_Syntax_Syntax.tm2 = e';
                       FStarC_Syntax_Syntax.meta = m;_}
                     ->
                     let uu___6 = aux_lbdef e' in
                     (match uu___6 with
                      | (t3, e'1, recheck) ->
                          (t3,
                            {
                              FStarC_Syntax_Syntax.n =
                                (FStarC_Syntax_Syntax.Tm_meta
                                   {
                                     FStarC_Syntax_Syntax.tm2 = e'1;
                                     FStarC_Syntax_Syntax.meta = m
                                   });
                              FStarC_Syntax_Syntax.pos =
                                (e3.FStarC_Syntax_Syntax.pos);
                              FStarC_Syntax_Syntax.hash_code =
                                (e3.FStarC_Syntax_Syntax.hash_code)
                            }, recheck))
                 | FStarC_Syntax_Syntax.Tm_ascribed
                     { FStarC_Syntax_Syntax.tm = e';
                       FStarC_Syntax_Syntax.asc =
                         (FStar_Pervasives.Inr c, tac_opt, use_eq);
                       FStarC_Syntax_Syntax.eff_opt = lopt;_}
                     ->
                     let uu___6 = FStarC_Syntax_Util.is_total_comp c in
                     if uu___6
                     then
                       let uu___7 =
                         reconcile_let_rec_ascription_and_body_type
                           (FStarC_Syntax_Util.comp_result c) lbtyp_opt
                           FStar_Pervasives_Native.None in
                       (match uu___7 with
                        | (t3, lbtyp, recheck) ->
                            let e4 =
                              let uu___8 =
                                let uu___9 =
                                  let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        FStarC_Syntax_Syntax.mk_Total t3 in
                                      FStar_Pervasives.Inr uu___12 in
                                    (uu___11, tac_opt, use_eq) in
                                  {
                                    FStarC_Syntax_Syntax.tm = e';
                                    FStarC_Syntax_Syntax.asc = uu___10;
                                    FStarC_Syntax_Syntax.eff_opt = lopt
                                  } in
                                FStarC_Syntax_Syntax.Tm_ascribed uu___9 in
                              {
                                FStarC_Syntax_Syntax.n = uu___8;
                                FStarC_Syntax_Syntax.pos =
                                  (e3.FStarC_Syntax_Syntax.pos);
                                FStarC_Syntax_Syntax.hash_code =
                                  (e3.FStarC_Syntax_Syntax.hash_code)
                              } in
                            (lbtyp, e4, recheck))
                     else
                       (let uu___7 =
                          let uu___8 =
                            let uu___9 =
                              let uu___10 =
                                let uu___11 =
                                  FStarC_Class_PP.pp
                                    FStarC_Syntax_Print.pretty_comp c in
                                FStar_Pprint.op_Hat_Slash_Hat uu___11
                                  (FStarC_Errors_Msg.text "instead") in
                              FStar_Pprint.op_Hat_Slash_Hat
                                (FStarC_Errors_Msg.text
                                   "Got a computation type") uu___10 in
                            [uu___9] in
                          (FStarC_Errors_Msg.text
                             "Expected a 'let rec' to be annotated with a value type")
                            :: uu___8 in
                        FStarC_Errors.raise_error
                          FStarC_Class_HasRange.hasRange_range rng
                          FStarC_Errors_Codes.Fatal_UnexpectedComputationTypeForLetRec
                          ()
                          (Obj.magic
                             FStarC_Errors_Msg.is_error_message_list_doc)
                          (Obj.magic uu___7))
                 | FStarC_Syntax_Syntax.Tm_ascribed
                     { FStarC_Syntax_Syntax.tm = e';
                       FStarC_Syntax_Syntax.asc =
                         (FStar_Pervasives.Inl t3, tac_opt, use_eq);
                       FStarC_Syntax_Syntax.eff_opt = lopt;_}
                     ->
                     let uu___6 =
                       reconcile_let_rec_ascription_and_body_type t3
                         lbtyp_opt FStar_Pervasives_Native.None in
                     (match uu___6 with
                      | (t4, lbtyp, recheck) ->
                          let e4 =
                            {
                              FStarC_Syntax_Syntax.n =
                                (FStarC_Syntax_Syntax.Tm_ascribed
                                   {
                                     FStarC_Syntax_Syntax.tm = e';
                                     FStarC_Syntax_Syntax.asc =
                                       ((FStar_Pervasives.Inl t4), tac_opt,
                                         use_eq);
                                     FStarC_Syntax_Syntax.eff_opt = lopt
                                   });
                              FStarC_Syntax_Syntax.pos =
                                (e3.FStarC_Syntax_Syntax.pos);
                              FStarC_Syntax_Syntax.hash_code =
                                (e3.FStarC_Syntax_Syntax.hash_code)
                            } in
                          (lbtyp, e4, recheck))
                 | FStarC_Syntax_Syntax.Tm_abs uu___6 ->
                     let uu___7 =
                       FStarC_Syntax_Util.abs_formals_maybe_unascribe_body
                         false e3 in
                     (match uu___7 with
                      | (bs, body, rcopt) ->
                          let mk_comp t3 = FStarC_Syntax_Syntax.mk_Total t3 in
                          let mk_arrow c = FStarC_Syntax_Util.arrow bs c in
                          let rec aux_abs_body body1 =
                            let body2 = FStarC_Syntax_Subst.compress body1 in
                            match body2.FStarC_Syntax_Syntax.n with
                            | FStarC_Syntax_Syntax.Tm_meta
                                { FStarC_Syntax_Syntax.tm2 = body3;
                                  FStarC_Syntax_Syntax.meta = m;_}
                                ->
                                let uu___8 = aux_abs_body body3 in
                                (match uu___8 with
                                 | (t3, body', recheck) ->
                                     let body4 =
                                       {
                                         FStarC_Syntax_Syntax.n =
                                           (FStarC_Syntax_Syntax.Tm_meta
                                              {
                                                FStarC_Syntax_Syntax.tm2 =
                                                  body';
                                                FStarC_Syntax_Syntax.meta = m
                                              });
                                         FStarC_Syntax_Syntax.pos =
                                           (body3.FStarC_Syntax_Syntax.pos);
                                         FStarC_Syntax_Syntax.hash_code =
                                           (body3.FStarC_Syntax_Syntax.hash_code)
                                       } in
                                     (t3, body4, recheck))
                            | FStarC_Syntax_Syntax.Tm_ascribed
                                { FStarC_Syntax_Syntax.tm = uu___8;
                                  FStarC_Syntax_Syntax.asc =
                                    (FStar_Pervasives.Inl t3, uu___9, use_eq);
                                  FStarC_Syntax_Syntax.eff_opt = uu___10;_}
                                ->
                                (if use_eq
                                 then
                                   (let uu___12 =
                                      let uu___13 =
                                        let uu___14 =
                                          let uu___15 =
                                            let uu___16 =
                                              FStarC_Class_PP.pp
                                                FStarC_Syntax_Print.pretty_term
                                                t3 in
                                            FStar_Pprint.parens uu___16 in
                                          FStar_Pprint.op_Hat_Slash_Hat
                                            uu___15
                                            (FStarC_Errors_Msg.text
                                               "is not yet supported.") in
                                        FStar_Pprint.op_Hat_Slash_Hat
                                          (FStarC_Errors_Msg.text
                                             "Equality ascription in this case")
                                          uu___14 in
                                      [uu___13;
                                      FStarC_Errors_Msg.text
                                        "Please use subtyping instead"] in
                                    FStarC_Errors.raise_error
                                      (FStarC_Syntax_Syntax.has_range_syntax
                                         ()) t3
                                      FStarC_Errors_Codes.Fatal_NotSupported
                                      ()
                                      (Obj.magic
                                         FStarC_Errors_Msg.is_error_message_list_doc)
                                      (Obj.magic uu___12))
                                 else ();
                                 (match lbtyp_opt with
                                  | FStar_Pervasives_Native.Some lbtyp ->
                                      (lbtyp, body2, false)
                                  | FStar_Pervasives_Native.None ->
                                      let t4 =
                                        let uu___12 = mk_comp t3 in
                                        mk_arrow uu___12 in
                                      (t4, body2, true)))
                            | FStarC_Syntax_Syntax.Tm_ascribed
                                { FStarC_Syntax_Syntax.tm = body';
                                  FStarC_Syntax_Syntax.asc =
                                    (FStar_Pervasives.Inr c, tac_opt, use_eq);
                                  FStarC_Syntax_Syntax.eff_opt = lopt;_}
                                ->
                                let tarr = mk_arrow c in
                                let n_bs = FStarC_List.length bs in
                                let uu___8 =
                                  reconcile_let_rec_ascription_and_body_type
                                    tarr lbtyp_opt
                                    (FStar_Pervasives_Native.Some n_bs) in
                                (match uu___8 with
                                 | (tarr1, lbtyp, recheck) ->
                                     let uu___9 =
                                       FStarC_TypeChecker_Normalize.get_n_binders
                                         env1 n_bs tarr1 in
                                     (match uu___9 with
                                      | (bs', c1) ->
                                          if (FStarC_List.length bs') <> n_bs
                                          then
                                            FStarC_Effect.failwith
                                              "Impossible"
                                          else
                                            (let subst =
                                               FStarC_Syntax_Util.rename_binders
                                                 bs' bs in
                                             let c2 =
                                               FStarC_Syntax_Subst.subst_comp
                                                 subst c1 in
                                             let body3 =
                                               {
                                                 FStarC_Syntax_Syntax.n =
                                                   (FStarC_Syntax_Syntax.Tm_ascribed
                                                      {
                                                        FStarC_Syntax_Syntax.tm
                                                          = body';
                                                        FStarC_Syntax_Syntax.asc
                                                          =
                                                          ((FStar_Pervasives.Inr
                                                              c2), tac_opt,
                                                            use_eq);
                                                        FStarC_Syntax_Syntax.eff_opt
                                                          = lopt
                                                      });
                                                 FStarC_Syntax_Syntax.pos =
                                                   (body2.FStarC_Syntax_Syntax.pos);
                                                 FStarC_Syntax_Syntax.hash_code
                                                   =
                                                   (body2.FStarC_Syntax_Syntax.hash_code)
                                               } in
                                             (lbtyp, body3, recheck))))
                            | uu___8 ->
                                (match lbtyp_opt with
                                 | FStar_Pervasives_Native.Some lbtyp ->
                                     (lbtyp, body2, false)
                                 | FStar_Pervasives_Native.None ->
                                     let tarr =
                                       let uu___9 =
                                         mk_comp FStarC_Syntax_Syntax.tun in
                                       mk_arrow uu___9 in
                                     (tarr, body2, true)) in
                          let uu___8 = aux_abs_body body in
                          (match uu___8 with
                           | (lbtyp, body1, recheck) ->
                               let uu___9 =
                                 FStarC_Syntax_Util.abs bs body1 rcopt in
                               (lbtyp, uu___9, recheck)))
                 | uu___6 ->
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           let uu___10 =
                             let uu___11 =
                               FStarC_Class_PP.pp
                                 FStarC_Syntax_Print.pretty_term e3 in
                             FStar_Pprint.op_Hat_Slash_Hat uu___11
                               (FStarC_Errors_Msg.text "instead") in
                           FStar_Pprint.op_Hat_Slash_Hat
                             (FStarC_Errors_Msg.text "Got") uu___10 in
                         [uu___9] in
                       (FStarC_Errors_Msg.text
                          "The definition of a 'let rec' must be a function literal")
                         :: uu___8 in
                     FStarC_Errors.raise_error
                       (FStarC_Syntax_Syntax.has_range_syntax ()) e3
                       FStarC_Errors_Codes.Fatal_UnexpectedComputationTypeForLetRec
                       ()
                       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                       (Obj.magic uu___7) in
               aux_lbdef e1 in
             match t2.FStarC_Syntax_Syntax.n with
             | FStarC_Syntax_Syntax.Tm_unknown ->
                 let uu___6 =
                   extract_annot_from_body FStar_Pervasives_Native.None in
                 (match uu___6 with
                  | (lbtyp, e2, uu___7) -> (univ_vars1, lbtyp, e2, true))
             | uu___6 ->
                 let uu___7 = FStarC_Syntax_Util.arrow_formals_comp t2 in
                 (match uu___7 with
                  | (uu___8, c) ->
                      let uu___9 =
                        let uu___10 =
                          let uu___11 =
                            FStarC_TypeChecker_Env.lookup_effect_quals env1
                              (FStarC_Syntax_Util.comp_effect_name c) in
                          FStarC_List.contains
                            FStarC_Syntax_Syntax.TotalEffect uu___11 in
                        Prims.not uu___10 in
                      if uu___9
                      then (univ_vars1, t2, e1, false)
                      else
                        (let uu___10 =
                           extract_annot_from_body
                             (FStar_Pervasives_Native.Some t2) in
                         match uu___10 with
                         | (lbtyp, e2, check_lbtyp) ->
                             (univ_vars1, lbtyp, e2, check_lbtyp))))))
let rec decorated_pattern_as_term (pat : FStarC_Syntax_Syntax.pat) :
  (FStarC_Syntax_Syntax.bv Prims.list * FStarC_Syntax_Syntax.term)=
  let mk f = FStarC_Syntax_Syntax.mk f pat.FStarC_Syntax_Syntax.p in
  let pat_as_arg uu___ =
    match uu___ with
    | (p, i) ->
        let uu___1 = decorated_pattern_as_term p in
        (match uu___1 with
         | (vars, te) ->
             (vars, (te, (FStarC_Syntax_Syntax.as_aqual_implicit i)))) in
  match pat.FStarC_Syntax_Syntax.v with
  | FStarC_Syntax_Syntax.Pat_constant c ->
      let uu___ = mk (FStarC_Syntax_Syntax.Tm_constant c) in ([], uu___)
  | FStarC_Syntax_Syntax.Pat_var x ->
      let uu___ = mk (FStarC_Syntax_Syntax.Tm_name x) in ([x], uu___)
  | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, pats) ->
      let uu___ =
        let uu___1 = FStarC_List.map pat_as_arg pats in
        FStarC_List.unzip uu___1 in
      (match uu___ with
       | (vars, args) ->
           let vars1 = FStarC_List.flatten vars in
           let head = FStarC_Syntax_Syntax.fv_to_tm fv in
           let head1 =
             match us_opt with
             | FStar_Pervasives_Native.None -> head
             | FStar_Pervasives_Native.Some us ->
                 FStarC_Syntax_Syntax.mk_Tm_uinst head us in
           let uu___1 =
             FStarC_Syntax_Syntax.mk_Tm_app head1 args
               pat.FStarC_Syntax_Syntax.p in
           (vars1, uu___1))
  | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
      (match eopt with
       | FStar_Pervasives_Native.None ->
           FStarC_Effect.failwith
             "TcUtil::decorated_pattern_as_term: dot pattern not resolved"
       | FStar_Pervasives_Native.Some e -> ([], e))
let comp_univ_opt
  (c : FStarC_Syntax_Syntax.comp' FStarC_Syntax_Syntax.syntax) :
  FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option=
  match c.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Total uu___ -> FStar_Pervasives_Native.None
  | FStarC_Syntax_Syntax.GTotal uu___ -> FStar_Pervasives_Native.None
  | FStarC_Syntax_Syntax.Comp c1 ->
      (match c1.FStarC_Syntax_Syntax.comp_univs with
       | [] -> FStar_Pervasives_Native.None
       | hd::uu___ -> FStar_Pervasives_Native.Some hd)
let lcomp_univ_opt (lc : FStarC_TypeChecker_Common.lcomp) :
  (FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option *
    FStarC_TypeChecker_Common.guard_t)=
  let uu___ = FStarC_TypeChecker_Common.lcomp_comp lc in
  match uu___ with | (c, g) -> let uu___1 = comp_univ_opt c in (uu___1, g)
let mk_comp_l (mname : FStarC_Ident.lident)
  (u_result : FStarC_Syntax_Syntax.universe)
  (result : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  (pre : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  (post : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  (flags : FStarC_Syntax_Syntax.cflag Prims.list) :
  FStarC_Syntax_Syntax.comp=
  FStarC_Syntax_Syntax.mk_Comp
    {
      FStarC_Syntax_Syntax.comp_univs = [u_result];
      FStarC_Syntax_Syntax.effect_name = mname;
      FStarC_Syntax_Syntax.result_typ = result;
      FStarC_Syntax_Syntax.comp_pre = pre;
      FStarC_Syntax_Syntax.comp_post = post;
      FStarC_Syntax_Syntax.flags = flags
    }
let mk_comp (md : FStarC_Syntax_Syntax.eff_decl) :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
      FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
        FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax ->
          FStarC_Syntax_Syntax.cflag Prims.list -> FStarC_Syntax_Syntax.comp=
  mk_comp_l md.FStarC_Syntax_Syntax.mname
let close_formula (env : FStarC_TypeChecker_Env.env)
  (bvs : FStarC_Syntax_Syntax.bv Prims.list)
  (phi : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  FStarC_List.fold_right
    (fun x phi1 ->
       let uu___ =
         env.FStarC_TypeChecker_Env.universe_of env
           x.FStarC_Syntax_Syntax.sort in
       FStarC_Syntax_Util.mk_forall uu___ x phi1) bvs phi
let close_post (env : FStarC_TypeChecker_Env.env)
  (bvs : FStarC_Syntax_Syntax.bv Prims.list) (t : FStarC_Syntax_Syntax.typ)
  (post : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let uu___ = FStarC_Syntax_Util.is_trivial_post post in
  if uu___
  then post
  else
    (let x = FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None t in
     let uu___1 =
       let uu___2 =
         let uu___3 = FStarC_Syntax_Syntax.bv_to_name x in
         FStarC_Syntax_Util.apply_post post uu___3 in
       FStarC_List.fold_right
         (fun y phi ->
            let uu___3 =
              env.FStarC_TypeChecker_Env.universe_of env
                y.FStarC_Syntax_Syntax.sort in
            FStarC_Syntax_Util.mk_exists uu___3 y phi) bvs uu___2 in
     FStarC_Syntax_Util.abs [FStarC_Syntax_Syntax.mk_binder x] uu___1
       (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.post_rc))
let label (reason : FStar_Pprint.document Prims.list)
  (r : FStarC_Range_Type.t) (f : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.typ=
  FStarC_Syntax_Syntax.mk
    (FStarC_Syntax_Syntax.Tm_meta
       {
         FStarC_Syntax_Syntax.tm2 = f;
         FStarC_Syntax_Syntax.meta =
           (FStarC_Syntax_Syntax.Meta_labeled (reason, r, false))
       }) f.FStarC_Syntax_Syntax.pos
let label_opt (env : FStarC_TypeChecker_Env.env)
  (reason :
    (unit -> FStar_Pprint.document Prims.list) FStar_Pervasives_Native.option)
  (r : FStarC_Range_Type.t) (f : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.typ=
  match reason with
  | FStar_Pervasives_Native.None -> f
  | FStar_Pervasives_Native.Some reason1 ->
      let uu___ =
        let uu___1 = FStarC_TypeChecker_Env.should_verify env in
        Prims.not uu___1 in
      if uu___ then f else (let uu___1 = reason1 () in label uu___1 r f)
let label_guard (r : FStarC_Range_Type.t)
  (reason : FStar_Pprint.document Prims.list)
  (g : FStarC_TypeChecker_Env.guard_t) : FStarC_TypeChecker_Common.guard_t=
  match g.FStarC_TypeChecker_Common.guard_f with
  | FStarC_TypeChecker_Common.Trivial -> g
  | FStarC_TypeChecker_Common.NonTrivial f ->
      let uu___ =
        let uu___1 = label reason r f in
        FStarC_TypeChecker_Common.NonTrivial uu___1 in
      {
        FStarC_TypeChecker_Common.guard_f = uu___;
        FStarC_TypeChecker_Common.deferred_to_tac =
          (g.FStarC_TypeChecker_Common.deferred_to_tac);
        FStarC_TypeChecker_Common.deferred =
          (g.FStarC_TypeChecker_Common.deferred);
        FStarC_TypeChecker_Common.univ_ineqs =
          (g.FStarC_TypeChecker_Common.univ_ineqs);
        FStarC_TypeChecker_Common.implicits =
          (g.FStarC_TypeChecker_Common.implicits)
      }
let lift_comp (env : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp_typ) (m : FStarC_Ident.lident) :
  (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Env.guard_t)=
  (let uu___1 =
     let uu___2 =
       let uu___3 =
         FStarC_TypeChecker_Env.is_erasable_effect env
           c.FStarC_Syntax_Syntax.effect_name in
       if uu___3
       then
         let uu___4 = FStarC_TypeChecker_Env.is_erasable_effect env m in
         Prims.not uu___4
       else false in
     if uu___2
     then
       let uu___3 =
         FStarC_TypeChecker_Normalize.non_info_norm env
           c.FStarC_Syntax_Syntax.result_typ in
       Prims.not uu___3
     else false in
   if uu___1
   then
     let uu___2 =
       let uu___3 =
         let uu___4 =
           let uu___5 =
             FStarC_Class_PP.pp FStarC_Ident.pretty_lident
               c.FStarC_Syntax_Syntax.effect_name in
           let uu___6 =
             let uu___7 =
               let uu___8 = FStarC_Class_PP.pp FStarC_Ident.pretty_lident m in
               let uu___9 =
                 let uu___10 =
                   let uu___11 =
                     FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term
                       c.FStarC_Syntax_Syntax.result_typ in
                   FStar_Pprint.op_Hat_Slash_Hat uu___11
                     (FStarC_Errors_Msg.text "is informative") in
                 FStar_Pprint.op_Hat_Slash_Hat
                   (FStarC_Errors_Msg.text "since its type") uu___10 in
               FStar_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
             FStar_Pprint.op_Hat_Slash_Hat (FStarC_Errors_Msg.text "~>")
               uu___7 in
           FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
         FStar_Pprint.op_Hat_Slash_Hat
           (FStarC_Errors_Msg.text "Cannot lift erasable expression from")
           uu___4 in
       [uu___3] in
     FStarC_Errors.raise_error FStarC_TypeChecker_Env.hasRange_env env
       FStarC_Errors_Codes.Error_TypeError ()
       (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
       (Obj.magic uu___2)
   else ());
  (let uu___1 =
     FStarC_Syntax_Syntax.mk_Comp
       {
         FStarC_Syntax_Syntax.comp_univs =
           (c.FStarC_Syntax_Syntax.comp_univs);
         FStarC_Syntax_Syntax.effect_name = m;
         FStarC_Syntax_Syntax.result_typ =
           (c.FStarC_Syntax_Syntax.result_typ);
         FStarC_Syntax_Syntax.comp_pre = (c.FStarC_Syntax_Syntax.comp_pre);
         FStarC_Syntax_Syntax.comp_post = (c.FStarC_Syntax_Syntax.comp_post);
         FStarC_Syntax_Syntax.flags = []
       } in
   (uu___1, FStarC_TypeChecker_Env.trivial_guard))
let join_effects (env : FStarC_TypeChecker_Env.env)
  (l1_in : FStarC_Ident.lident) (l2_in : FStarC_Ident.lident) :
  FStarC_Ident.lident=
  let uu___ =
    let uu___1 = FStarC_TypeChecker_Env.norm_eff_name env l1_in in
    let uu___2 = FStarC_TypeChecker_Env.norm_eff_name env l2_in in
    (uu___1, uu___2) in
  match uu___ with
  | (l1, l2) ->
      let uu___1 = FStarC_TypeChecker_Env.join_opt env l1 l2 in
      (match uu___1 with
       | FStar_Pervasives_Native.Some m -> m
       | FStar_Pervasives_Native.None ->
           let uu___2 =
             let uu___3 =
               let uu___4 =
                 let uu___5 =
                   FStarC_Class_PP.pp FStarC_Ident.pretty_lident l1_in in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       FStarC_Class_PP.pp FStarC_Ident.pretty_lident l2_in in
                     FStar_Pprint.op_Hat_Slash_Hat uu___8
                       (FStarC_Errors_Msg.text "cannot be composed") in
                   FStar_Pprint.op_Hat_Slash_Hat
                     (FStarC_Errors_Msg.text "and") uu___7 in
                 FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
               FStar_Pprint.op_Hat_Slash_Hat
                 (FStarC_Errors_Msg.text "Effects") uu___4 in
             [uu___3] in
           FStarC_Errors.raise_error FStarC_TypeChecker_Env.hasRange_env env
             FStarC_Errors_Codes.Fatal_EffectsCannotBeComposed ()
             (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
             (Obj.magic uu___2))
let join_lcomp (env : FStarC_TypeChecker_Env.env)
  (c1 : FStarC_TypeChecker_Common.lcomp)
  (c2 : FStarC_TypeChecker_Common.lcomp) : FStarC_Ident.lident=
  let uu___ =
    let uu___1 = FStarC_TypeChecker_Common.is_total_lcomp c1 in
    if uu___1 then FStarC_TypeChecker_Common.is_total_lcomp c2 else false in
  if uu___
  then FStarC_Parser_Const.effect_Tot_lid
  else
    join_effects env c1.FStarC_TypeChecker_Common.eff_name
      c2.FStarC_TypeChecker_Common.eff_name
let maybe_push (env : FStarC_TypeChecker_Env.env)
  (b : FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option) :
  FStarC_TypeChecker_Env.env=
  match b with
  | FStar_Pervasives_Native.None -> env
  | FStar_Pervasives_Native.Some bv -> FStarC_TypeChecker_Env.push_bv env bv
let lift_comps_sep_guards (env : FStarC_TypeChecker_Env.env)
  (c1 : FStarC_Syntax_Syntax.comp) (c2 : FStarC_Syntax_Syntax.comp)
  (b : FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  (for_bind : Prims.bool) :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.comp *
    FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Env.guard_t *
    FStarC_TypeChecker_Env.guard_t)=
  let c11 = FStarC_TypeChecker_Env.unfold_effect_abbrev env c1 in
  let env2 = maybe_push env b in
  let c21 = FStarC_TypeChecker_Env.unfold_effect_abbrev env2 c2 in
  let uu___ =
    FStarC_TypeChecker_Env.join_opt env c11.FStarC_Syntax_Syntax.effect_name
      c21.FStarC_Syntax_Syntax.effect_name in
  match uu___ with
  | FStar_Pervasives_Native.Some m ->
      let uu___1 = lift_comp env c11 m in
      (match uu___1 with
       | (c12, g1) ->
           let uu___2 = lift_comp env2 c21 m in
           (match uu___2 with | (c22, g2) -> (m, c12, c22, g1, g2)))
  | FStar_Pervasives_Native.None ->
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                c11.FStarC_Syntax_Syntax.effect_name in
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                    c21.FStarC_Syntax_Syntax.effect_name in
                FStar_Pprint.op_Hat_Slash_Hat uu___7
                  (FStarC_Errors_Msg.text "cannot be composed") in
              FStar_Pprint.op_Hat_Slash_Hat (FStarC_Errors_Msg.text "and")
                uu___6 in
            FStar_Pprint.op_Hat_Slash_Hat uu___4 uu___5 in
          FStar_Pprint.op_Hat_Slash_Hat (FStarC_Errors_Msg.text "Effects")
            uu___3 in
        [uu___2] in
      FStarC_Errors.raise_error FStarC_TypeChecker_Env.hasRange_env env
        FStarC_Errors_Codes.Fatal_EffectsCannotBeComposed ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
        (Obj.magic uu___1)
let lift_comps (env : FStarC_TypeChecker_Env.env)
  (c1 : FStarC_Syntax_Syntax.comp) (c2 : FStarC_Syntax_Syntax.comp)
  (b : FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  (for_bind : Prims.bool) :
  (FStarC_Ident.lident * FStarC_Syntax_Syntax.comp *
    FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Env.guard_t)=
  let uu___ = lift_comps_sep_guards env c1 c2 b for_bind in
  match uu___ with
  | (l, c11, c21, g1, g2) ->
      let uu___1 = FStarC_TypeChecker_Env.conj_guard g1 g2 in
      (l, c11, c21, uu___1)
let is_pure_effect (env : FStarC_TypeChecker_Env.env)
  (l : FStarC_Ident.lident) : Prims.bool=
  let l1 = FStarC_TypeChecker_Env.norm_eff_name env l in
  FStarC_Ident.lid_equals l1 FStarC_Parser_Const.effect_PURE_lid
let is_ghost_effect (env : FStarC_TypeChecker_Env.env)
  (l : FStarC_Ident.lident) : Prims.bool=
  let l1 = FStarC_TypeChecker_Env.norm_eff_name env l in
  FStarC_Ident.lid_equals l1 FStarC_Parser_Const.effect_GHOST_lid
let is_pure_or_ghost_effect (env : FStarC_TypeChecker_Env.env)
  (l : FStarC_Ident.lident) : Prims.bool=
  let l1 = FStarC_TypeChecker_Env.norm_eff_name env l in
  (FStarC_Ident.lid_equals l1 FStarC_Parser_Const.effect_PURE_lid) ||
    (FStarC_Ident.lid_equals l1 FStarC_Parser_Const.effect_GHOST_lid)
let close_wp_comp (env : FStarC_TypeChecker_Env.env)
  (bvs : FStarC_Syntax_Syntax.bv Prims.list) (c : FStarC_Syntax_Syntax.comp)
  : FStarC_Syntax_Syntax.comp=
  (let uu___1 = FStarC_TypeChecker_Env.push_bvs env bvs in
   FStarC_Defensive.def_check_scoped FStarC_TypeChecker_Env.hasBinders_env
     FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp
     c.FStarC_Syntax_Syntax.pos "close_wp_comp" uu___1 c);
  (let uu___1 = FStarC_Syntax_Util.is_ml_comp c in
   if uu___1
   then c
   else
     (let env_bvs = FStarC_TypeChecker_Env.push_bvs env bvs in
      match c.FStarC_Syntax_Syntax.n with
      | FStarC_Syntax_Syntax.Total uu___2 -> c
      | FStarC_Syntax_Syntax.GTotal uu___2 -> c
      | FStarC_Syntax_Syntax.Comp ct ->
          let uu___2 =
            let uu___3 =
              close_formula env_bvs bvs ct.FStarC_Syntax_Syntax.comp_pre in
            let uu___4 =
              close_post env_bvs bvs ct.FStarC_Syntax_Syntax.result_typ
                ct.FStarC_Syntax_Syntax.comp_post in
            let uu___5 =
              FStarC_List.filter
                (fun uu___6 ->
                   match uu___6 with
                   | FStarC_Syntax_Syntax.MLEFFECT -> true
                   | uu___7 -> false) ct.FStarC_Syntax_Syntax.flags in
            {
              FStarC_Syntax_Syntax.comp_univs =
                (ct.FStarC_Syntax_Syntax.comp_univs);
              FStarC_Syntax_Syntax.effect_name =
                (ct.FStarC_Syntax_Syntax.effect_name);
              FStarC_Syntax_Syntax.result_typ =
                (ct.FStarC_Syntax_Syntax.result_typ);
              FStarC_Syntax_Syntax.comp_pre = uu___3;
              FStarC_Syntax_Syntax.comp_post = uu___4;
              FStarC_Syntax_Syntax.flags = uu___5
            } in
          FStarC_Syntax_Syntax.mk_Comp uu___2))
let close_wp_lcomp (env : FStarC_TypeChecker_Env.env)
  (bvs : FStarC_Syntax_Syntax.bv Prims.list)
  (lc : FStarC_TypeChecker_Common.lcomp) : FStarC_TypeChecker_Common.lcomp=
  let bs = FStarC_List.map FStarC_Syntax_Syntax.mk_binder bvs in
  FStarC_TypeChecker_Common.apply_lcomp (close_wp_comp env bvs)
    (fun g ->
       let uu___ = FStarC_TypeChecker_Env.close_guard env bs g in
       close_guard_implicits env false bs uu___) lc
let close_layered_lcomp_with_combinator (env : FStarC_TypeChecker_Env.env)
  (bvs : FStarC_Syntax_Syntax.bv Prims.list)
  (lc : FStarC_TypeChecker_Common.lcomp) : FStarC_TypeChecker_Common.lcomp=
  close_wp_lcomp env bvs lc
let close_layered_lcomp_with_substitutions (env : FStarC_TypeChecker_Env.env)
  (bvs : FStarC_Syntax_Syntax.bv Prims.list)
  (tms : FStarC_Syntax_Syntax.term Prims.list)
  (lc : FStarC_TypeChecker_Common.lcomp) : FStarC_TypeChecker_Common.lcomp=
  let bs = FStarC_List.map FStarC_Syntax_Syntax.mk_binder bvs in
  let substs =
    FStarC_List.map2 (fun bv tm -> FStarC_Syntax_Syntax.NT (bv, tm)) bvs tms in
  FStarC_TypeChecker_Common.apply_lcomp
    (FStarC_Syntax_Subst.subst_comp substs)
    (fun g ->
       let uu___ = FStarC_TypeChecker_Env.close_guard env bs g in
       close_guard_implicits env false bs uu___) lc
let should_not_inline_lc (lc : FStarC_TypeChecker_Common.lcomp) : Prims.bool=
  false
let should_return (env : FStarC_TypeChecker_Env.env)
  (eopt : FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  (lc : FStarC_TypeChecker_Common.lcomp) : Prims.bool=
  let lc_is_unit_or_effectful =
    let c =
      let uu___ =
        FStarC_Syntax_Util.arrow_formals_comp
          lc.FStarC_TypeChecker_Common.res_typ in
      FStar_Pervasives_Native.snd uu___ in
    let uu___ = FStarC_Syntax_Util.is_pure_or_ghost_comp c in
    if uu___
    then
      let uu___1 =
        FStarC_TypeChecker_Normalize.unfold_whnf env
          (FStarC_Syntax_Util.comp_result c) in
      FStarC_Syntax_Util.is_unit uu___1
    else true in
  match eopt with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some e ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_TypeChecker_Common.is_pure_or_ghost_lcomp lc in
          if uu___2 then Prims.not lc_is_unit_or_effectful else false in
        if uu___1
        then
          let uu___2 = FStarC_Syntax_Util.head_and_args_full e in
          match uu___2 with
          | (head, uu___3) ->
              let uu___4 =
                let uu___5 = FStarC_Syntax_Util.un_uinst head in
                uu___5.FStarC_Syntax_Syntax.n in
              (match uu___4 with
               | FStarC_Syntax_Syntax.Tm_fvar fv ->
                   let uu___5 =
                     FStarC_TypeChecker_Env.is_irreducible env
                       (FStarC_Syntax_Syntax.lid_of_fv fv) in
                   Prims.not uu___5
               | uu___5 -> true)
        else false in
      if uu___
      then let uu___1 = should_not_inline_lc lc in Prims.not uu___1
      else false
let discard_specs : FStarC_TypeChecker_Env.env -> Prims.bool=
  FStarC_TypeChecker_Env.discard_specs
let mk_bind (env : FStarC_TypeChecker_Env.env)
  (c1 : FStarC_Syntax_Syntax.comp)
  (b : FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option)
  (c2 : FStarC_Syntax_Syntax.comp)
  (flags : FStarC_Syntax_Syntax.cflag Prims.list) (r1 : FStarC_Range_Type.t)
  : (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Env.guard_t)=
  let env2 = maybe_push env b in
  let uu___ = discard_specs env in
  if uu___
  then
    let uu___1 = lift_comps env c1 c2 b true in
    match uu___1 with
    | (m, _c1, c21, g_lift) ->
        let ct2 = FStarC_TypeChecker_Env.comp_to_comp_typ env2 c21 in
        let u2 =
          match ct2.FStarC_Syntax_Syntax.comp_univs with
          | u::uu___2 -> u
          | [] ->
              env.FStarC_TypeChecker_Env.universe_of env2
                ct2.FStarC_Syntax_Syntax.result_typ in
        let uu___2 =
          FStarC_Syntax_Syntax.mk_triv_comp [u2] m
            ct2.FStarC_Syntax_Syntax.result_typ flags in
        (uu___2, g_lift)
  else
    (FStarC_Defensive.def_check_scoped FStarC_TypeChecker_Env.hasBinders_env
       FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp r1
       "mk_bind.in.c1" env c1;
     FStarC_Defensive.def_check_scoped FStarC_TypeChecker_Env.hasBinders_env
       FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp r1
       "mk_bind.in.c2" env2 c2;
     (let uu___3 = lift_comps env c1 c2 b true in
      match uu___3 with
      | (m, c11, c21, g_lift) ->
          let ct1 = FStarC_TypeChecker_Env.comp_to_comp_typ env c11 in
          let ct2 = FStarC_TypeChecker_Env.comp_to_comp_typ env2 c21 in
          let u1 =
            match ct1.FStarC_Syntax_Syntax.comp_univs with
            | u::uu___4 -> u
            | [] ->
                env.FStarC_TypeChecker_Env.universe_of env
                  ct1.FStarC_Syntax_Syntax.result_typ in
          let u2 =
            match ct2.FStarC_Syntax_Syntax.comp_univs with
            | u::uu___4 -> u
            | [] ->
                env.FStarC_TypeChecker_Env.universe_of env2
                  ct2.FStarC_Syntax_Syntax.result_typ in
          let x =
            match b with
            | FStar_Pervasives_Native.Some x1 ->
                {
                  FStarC_Syntax_Syntax.ppname =
                    (x1.FStarC_Syntax_Syntax.ppname);
                  FStarC_Syntax_Syntax.index =
                    (x1.FStarC_Syntax_Syntax.index);
                  FStarC_Syntax_Syntax.sort =
                    (ct1.FStarC_Syntax_Syntax.result_typ)
                }
            | FStar_Pervasives_Native.None ->
                FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                  ct1.FStarC_Syntax_Syntax.result_typ in
          let post1_x =
            let t1 =
              FStarC_TypeChecker_Normalize.normalize_refinement
                FStarC_TypeChecker_Normalize.whnf_steps env
                ct1.FStarC_Syntax_Syntax.result_typ in
            let uu___4 =
              let uu___5 = FStarC_Syntax_Syntax.bv_to_name x in
              FStarC_TypeChecker_Env.type_hypothesis env t1 uu___5 in
            let uu___5 =
              let uu___6 = FStarC_Syntax_Syntax.bv_to_name x in
              FStarC_Syntax_Util.apply_post
                ct1.FStarC_Syntax_Syntax.comp_post uu___6 in
            FStarC_Syntax_Util.mk_conj_simp uu___4 uu___5 in
          let one_point = FStarC_TypeChecker_Common.one_point_defn x post1_x in
          let quantify phi =
            let uu___4 = FStarC_Syntax_Util.is_t_true phi in
            if uu___4
            then phi
            else
              (match one_point with
               | FStar_Pervasives_Native.Some (v, rest) ->
                   let uu___5 = FStarC_Syntax_Util.mk_imp_simp rest phi in
                   FStarC_Syntax_Subst.subst [FStarC_Syntax_Syntax.NT (x, v)]
                     uu___5
               | FStar_Pervasives_Native.None ->
                   let body = FStarC_Syntax_Util.mk_imp_simp post1_x phi in
                   let uu___5 =
                     let uu___6 = FStarC_Syntax_Free.names body in
                     FStarC_Class_Setlike.mem
                       (FStarC_FlatSet.setlike_flat_set
                          FStarC_Syntax_Syntax.ord_bv) x uu___6 in
                   if uu___5
                   then FStarC_Syntax_Util.mk_forall u1 x body
                   else body) in
          let compose phi =
            match one_point with
            | FStar_Pervasives_Native.Some (v, rest) ->
                let uu___4 = FStarC_Syntax_Util.mk_conj_simp rest phi in
                FStarC_Syntax_Subst.subst [FStarC_Syntax_Syntax.NT (x, v)]
                  uu___4
            | FStar_Pervasives_Native.None ->
                let body = FStarC_Syntax_Util.mk_conj_simp post1_x phi in
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Free.names body in
                  FStarC_Class_Setlike.mem
                    (FStarC_FlatSet.setlike_flat_set
                       FStarC_Syntax_Syntax.ord_bv) x uu___5 in
                if uu___4
                then FStarC_Syntax_Util.mk_exists u1 x body
                else body in
          let pre =
            let uu___4 = quantify ct2.FStarC_Syntax_Syntax.comp_pre in
            FStarC_Syntax_Util.mk_conj_simp ct1.FStarC_Syntax_Syntax.comp_pre
              uu___4 in
          let post =
            let y =
              FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                ct2.FStarC_Syntax_Syntax.result_typ in
            let body =
              let uu___4 =
                let uu___5 = FStarC_Syntax_Syntax.bv_to_name y in
                FStarC_Syntax_Util.apply_post
                  ct2.FStarC_Syntax_Syntax.comp_post uu___5 in
              compose uu___4 in
            let uu___4 = FStarC_Syntax_Util.is_t_true body in
            if uu___4
            then
              FStarC_Syntax_Syntax.trivial_post
                ct2.FStarC_Syntax_Syntax.result_typ
            else
              FStarC_Syntax_Util.abs [FStarC_Syntax_Syntax.mk_binder y] body
                (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.post_rc) in
          let res =
            mk_comp_l m u2 ct2.FStarC_Syntax_Syntax.result_typ pre post flags in
          (FStarC_Defensive.def_check_scoped
             FStarC_TypeChecker_Env.hasBinders_env
             FStarC_Class_Binders.hasNames_comp
             FStarC_Syntax_Print.pretty_comp r1 "mk_bind.out" env res;
           (res, g_lift))))
let strengthen_comp (env : FStarC_TypeChecker_Env.env)
  (reason :
    (unit -> FStar_Pprint.document Prims.list) FStar_Pervasives_Native.option)
  (c : FStarC_Syntax_Syntax.comp) (f : FStarC_Syntax_Syntax.formula)
  (flags : FStarC_Syntax_Syntax.cflag Prims.list) :
  (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Env.guard_t)=
  if env.FStarC_TypeChecker_Env.phase1
  then (c, FStarC_TypeChecker_Env.trivial_guard)
  else
    (let r = FStarC_TypeChecker_Env.get_range env in
     let f1 = label_opt env reason r f in
     let assert_c =
       let uu___ =
         FStarC_Syntax_Syntax.trivial_post FStarC_Syntax_Syntax.t_unit in
       mk_comp_l FStarC_Parser_Const.effect_PURE_lid
         FStarC_Syntax_Syntax.U_zero FStarC_Syntax_Syntax.t_unit f1 uu___ [] in
     mk_bind env assert_c FStar_Pervasives_Native.None c flags r)
let return_value (env : FStarC_TypeChecker_Env.env)
  (eff_lid : FStarC_Ident.lident)
  (u_t_opt : FStarC_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  (t : FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax)
  (v : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Env.guard_t)=
  let u =
    match u_t_opt with
    | FStar_Pervasives_Native.None ->
        env.FStarC_TypeChecker_Env.universe_of env t
    | FStar_Pervasives_Native.Some u1 -> u1 in
  let x = FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None t in
  let post =
    let uu___ =
      let uu___1 = FStarC_Syntax_Syntax.bv_to_name x in
      FStarC_Syntax_Util.mk_eq2 u t uu___1 v in
    FStarC_Syntax_Util.abs [FStarC_Syntax_Syntax.mk_binder x] uu___
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.post_rc) in
  let uu___ =
    let uu___1 = FStarC_TypeChecker_Env.norm_eff_name env eff_lid in
    mk_comp_l uu___1 u t FStarC_Syntax_Syntax.trivial_pre post [] in
  (uu___, FStarC_TypeChecker_Env.trivial_guard)
let weaken_flags (flags : FStarC_Syntax_Syntax.cflag Prims.list) :
  FStarC_Syntax_Syntax.cflag Prims.list=
  FStarC_List.filter
    (fun uu___ ->
       match uu___ with
       | FStarC_Syntax_Syntax.MLEFFECT -> true
       | uu___1 -> false) flags
let weaken_comp (env : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) (formula : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Env.guard_t)=
  let uu___ = FStarC_Syntax_Util.is_ml_comp c in
  if uu___
  then (c, FStarC_TypeChecker_Env.trivial_guard)
  else
    (let r = FStarC_TypeChecker_Env.get_range env in
     let assume_c =
       let uu___1 =
         let uu___2 =
           let uu___3 =
             FStarC_Syntax_Syntax.null_binder FStarC_Syntax_Syntax.t_unit in
           [uu___3] in
         FStarC_Syntax_Util.abs uu___2 formula
           (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.post_rc) in
       mk_comp_l FStarC_Parser_Const.effect_PURE_lid
         FStarC_Syntax_Syntax.U_zero FStarC_Syntax_Syntax.t_unit
         FStarC_Syntax_Syntax.trivial_pre uu___1 [] in
     let uu___1 = weaken_flags (FStarC_Syntax_Util.comp_flags c) in
     mk_bind env assume_c FStar_Pervasives_Native.None c uu___1 r)
let weaken_precondition (env : FStarC_TypeChecker_Env.env)
  (lc : FStarC_TypeChecker_Common.lcomp)
  (f : FStarC_TypeChecker_Common.guard_formula) :
  FStarC_TypeChecker_Common.lcomp=
  let weaken uu___ =
    let uu___1 = FStarC_TypeChecker_Common.lcomp_comp lc in
    match uu___1 with
    | (c, g_c) ->
        (match f with
         | FStarC_TypeChecker_Common.Trivial -> (c, g_c)
         | FStarC_TypeChecker_Common.NonTrivial f1 ->
             let uu___2 = weaken_comp env c f1 in
             (match uu___2 with
              | (c1, g_w) ->
                  let uu___3 = FStarC_TypeChecker_Env.conj_guard g_c g_w in
                  (c1, uu___3))) in
  let uu___ = weaken_flags lc.FStarC_TypeChecker_Common.cflags in
  FStarC_TypeChecker_Common.mk_lcomp lc.FStarC_TypeChecker_Common.eff_name
    lc.FStarC_TypeChecker_Common.res_typ uu___ weaken
let strengthen_precondition
  (reason :
    (unit -> FStar_Pprint.document Prims.list) FStar_Pervasives_Native.option)
  (env : FStarC_TypeChecker_Env.env)
  (e_for_debugging_only : FStarC_Syntax_Syntax.term)
  (lc : FStarC_TypeChecker_Common.lcomp)
  (g0 : FStarC_TypeChecker_Env.guard_t) :
  (FStarC_TypeChecker_Common.lcomp * FStarC_TypeChecker_Common.guard_t)=
  if FStarC_TypeChecker_Env.is_trivial_guard_formula g0
  then (lc, g0)
  else
    (let flags = [] in
     let strengthen uu___ =
       let uu___1 = FStarC_TypeChecker_Common.lcomp_comp lc in
       match uu___1 with
       | (c, g_c) ->
           let uu___2 = FStarC_Options.admit_smt_queries () in
           if uu___2
           then (c, g_c)
           else
             (let g01 = FStarC_TypeChecker_Rel.simplify_guard env g0 in
              match FStarC_TypeChecker_Env.guard_form g01 with
              | FStarC_TypeChecker_Common.Trivial -> (c, g_c)
              | FStarC_TypeChecker_Common.NonTrivial f ->
                  ((let uu___4 = FStarC_Debug.extreme () in
                    if uu___4
                    then
                      let uu___5 =
                        FStarC_TypeChecker_Normalize.term_to_string env
                          e_for_debugging_only in
                      let uu___6 =
                        FStarC_TypeChecker_Normalize.term_to_string env f in
                      FStarC_Format.print2
                        "-------------Strengthening pre-condition of term %s with guard %s\n"
                        uu___5 uu___6
                    else ());
                   (let uu___4 = strengthen_comp env reason c f flags in
                    match uu___4 with
                    | (c1, g_s) ->
                        let uu___5 =
                          FStarC_TypeChecker_Env.conj_guard g_c g_s in
                        (c1, uu___5)))) in
     let uu___ =
       let uu___1 =
         FStarC_TypeChecker_Env.norm_eff_name env
           lc.FStarC_TypeChecker_Common.eff_name in
       FStarC_TypeChecker_Common.mk_lcomp uu___1
         lc.FStarC_TypeChecker_Common.res_typ flags strengthen in
     (uu___,
       {
         FStarC_TypeChecker_Common.guard_f =
           FStarC_TypeChecker_Common.Trivial;
         FStarC_TypeChecker_Common.deferred_to_tac =
           (g0.FStarC_TypeChecker_Common.deferred_to_tac);
         FStarC_TypeChecker_Common.deferred =
           (g0.FStarC_TypeChecker_Common.deferred);
         FStarC_TypeChecker_Common.univ_ineqs =
           (g0.FStarC_TypeChecker_Common.univ_ineqs);
         FStarC_TypeChecker_Common.implicits =
           (g0.FStarC_TypeChecker_Common.implicits)
       }))
let lcomp_has_trivial_postcondition (lc : FStarC_TypeChecker_Common.lcomp) :
  Prims.bool= FStarC_TypeChecker_Common.is_tot_or_gtot_lcomp lc
let maybe_capture_unit_refinement (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) (x : FStarC_Syntax_Syntax.bv)
  (c : FStarC_Syntax_Syntax.comp) :
  (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Env.guard_t * Prims.bool)=
  let t1 =
    FStarC_TypeChecker_Normalize.normalize_refinement
      FStarC_TypeChecker_Normalize.whnf_steps env t in
  match t1.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_refine
      { FStarC_Syntax_Syntax.b2 = b; FStarC_Syntax_Syntax.phi = phi;_} ->
      let is_unit =
        match (b.FStarC_Syntax_Syntax.sort).FStarC_Syntax_Syntax.n with
        | FStarC_Syntax_Syntax.Tm_fvar fv ->
            FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.unit_lid
        | uu___ -> false in
      if is_unit
      then
        let uu___ = FStarC_Syntax_Subst.open_term_bv b phi in
        (match uu___ with
         | (b1, phi1) ->
             let phi2 =
               FStarC_Syntax_Subst.subst
                 [FStarC_Syntax_Syntax.NT
                    (b1, FStarC_Syntax_Syntax.unit_const)] phi1 in
             let c1 =
               FStarC_Syntax_Subst.subst_comp
                 [FStarC_Syntax_Syntax.NT
                    (x, FStarC_Syntax_Syntax.unit_const)] c in
             let uu___1 = weaken_comp env c1 phi2 in
             (match uu___1 with | (c2, g) -> (c2, g, true)))
      else (c, FStarC_TypeChecker_Env.trivial_guard, false)
  | FStarC_Syntax_Syntax.Tm_fvar fv when
      FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.unit_lid ->
      let uu___ =
        FStarC_Syntax_Subst.subst_comp
          [FStarC_Syntax_Syntax.NT (x, FStarC_Syntax_Syntax.unit_const)] c in
      (uu___, FStarC_TypeChecker_Env.trivial_guard, true)
  | uu___ -> (c, FStarC_TypeChecker_Env.trivial_guard, false)
let optimize_bind_vc (uu___ : unit) : Prims.bool=
  FStarC_Options_Ext.enabled "optimize_let_vc"
let bind (r1 : FStarC_Range_Type.t) (is_let_binding : Prims.bool)
  (env : FStarC_TypeChecker_Env.env)
  (e1opt : FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  (lc1 : FStarC_TypeChecker_Common.lcomp) (binder_lc2 : lcomp_with_binder) :
  FStarC_TypeChecker_Common.lcomp=
  let uu___ = binder_lc2 in
  match uu___ with
  | (b, lc2) ->
      let debug f =
        let uu___1 =
          let uu___2 = FStarC_Debug.extreme () in
          if uu___2 then true else FStarC_Effect.op_Bang dbg_bind in
        if uu___1 then f () else () in
      let uu___1 =
        FStarC_TypeChecker_Normalize.ghost_to_pure_lcomp2 env (lc1, lc2) in
      (match uu___1 with
       | (lc11, lc21) ->
           let joined_eff = join_lcomp env lc11 lc21 in
           let bind_flags =
             let uu___2 =
               let uu___3 = FStarC_TypeChecker_Common.is_total_lcomp lc11 in
               if uu___3
               then FStarC_TypeChecker_Common.is_total_lcomp lc21
               else false in
             if uu___2 then [FStarC_Syntax_Syntax.TOTAL] else [] in
           let bind_it uu___2 =
             let uu___3 = FStarC_TypeChecker_Common.lcomp_comp lc11 in
             match uu___3 with
             | (c1, g_c1) ->
                 let uu___4 = FStarC_TypeChecker_Common.lcomp_comp lc21 in
                 (match uu___4 with
                  | (c2, g_c2) ->
                      let trivial_guard =
                        let uu___5 =
                          match b with
                          | FStar_Pervasives_Native.Some x ->
                              let b1 = FStarC_Syntax_Syntax.mk_binder x in
                              if FStarC_Syntax_Syntax.is_null_binder b1
                              then g_c2
                              else
                                FStarC_TypeChecker_Env.close_guard env 
                                  [b1] g_c2
                          | FStar_Pervasives_Native.None -> g_c2 in
                        FStarC_TypeChecker_Env.conj_guard g_c1 uu___5 in
                      (debug
                         (fun uu___6 ->
                            let uu___7 =
                              FStarC_Class_Show.show
                                FStarC_Class_Show.showable_bool
                                is_let_binding in
                            let uu___8 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_comp c1 in
                            let uu___9 =
                              match b with
                              | FStar_Pervasives_Native.None -> "none"
                              | FStar_Pervasives_Native.Some x ->
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_bv x in
                            let uu___10 =
                              FStarC_Class_Show.show
                                FStarC_Syntax_Print.showable_comp c2 in
                            let uu___11 =
                              match e1opt with
                              | FStar_Pervasives_Native.None -> "none"
                              | FStar_Pervasives_Native.Some e1 ->
                                  FStarC_Class_Show.show
                                    FStarC_Syntax_Print.showable_term e1 in
                            FStarC_Format.print5
                              "(1) bind (is_let_binding=%s): \n\tc1=%s\n\tx=%s\n\tc2=%s\n\te1=%s\n(1. end bind)\n"
                              uu___7 uu___8 uu___9 uu___10 uu___11);
                       (let aux uu___6 =
                          let uu___7 =
                            let uu___8 = FStarC_Syntax_Util.is_ml_comp c1 in
                            if uu___8
                            then FStarC_Syntax_Util.is_ml_comp c2
                            else false in
                          if uu___7
                          then FStar_Pervasives.Inl (c2, "both ml")
                          else FStar_Pervasives.Inr "both are not ML" in
                        let try_simplify uu___6 =
                          let aux_with_trivial_guard uu___7 =
                            let uu___8 = aux () in
                            match uu___8 with
                            | FStar_Pervasives.Inl (c, reason) ->
                                FStar_Pervasives.Inl
                                  (c, trivial_guard, reason)
                            | FStar_Pervasives.Inr reason ->
                                FStar_Pervasives.Inr reason in
                          let has_evident_type uu___7 =
                            match e1opt with
                            | FStar_Pervasives_Native.None -> false
                            | FStar_Pervasives_Native.Some e ->
                                let uu___8 =
                                  FStarC_Syntax_Util.head_and_args_full e in
                                (match uu___8 with
                                 | (hd, uu___9) ->
                                     let uu___10 =
                                       let uu___11 =
                                         FStarC_Syntax_Util.un_uinst hd in
                                       uu___11.FStarC_Syntax_Syntax.n in
                                     (match uu___10 with
                                      | FStarC_Syntax_Syntax.Tm_fvar fv ->
                                          FStarC_TypeChecker_Env.is_datacon
                                            env
                                            (FStarC_Syntax_Syntax.lid_of_fv
                                               fv)
                                      | FStarC_Syntax_Syntax.Tm_constant
                                          uu___11 -> true
                                      | uu___11 -> false)) in
                          let drops_typing_info uu___7 =
                            match b with
                            | FStar_Pervasives_Native.Some x when
                                let uu___8 =
                                  let uu___9 =
                                    let uu___10 = discard_specs env in
                                    Prims.not uu___10 in
                                  if uu___9
                                  then
                                    (if is_let_binding
                                     then true
                                     else
                                       (let uu___10 = has_evident_type () in
                                        Prims.not uu___10))
                                  else false in
                                if uu___8
                                then
                                  let uu___9 =
                                    let uu___10 =
                                      FStarC_Syntax_Free.names_comp c2 in
                                    FStarC_Class_Setlike.mem
                                      (FStarC_FlatSet.setlike_flat_set
                                         FStarC_Syntax_Syntax.ord_bv) x
                                      uu___10 in
                                  Prims.not uu___9
                                else false ->
                                let t =
                                  FStarC_TypeChecker_Normalize.normalize_refinement
                                    FStarC_TypeChecker_Normalize.whnf_steps
                                    env (FStarC_Syntax_Util.comp_result c1) in
                                let is_unit_refinement =
                                  match t.FStarC_Syntax_Syntax.n with
                                  | FStarC_Syntax_Syntax.Tm_refine
                                      { FStarC_Syntax_Syntax.b2 = b1;
                                        FStarC_Syntax_Syntax.phi = uu___8;_}
                                      ->
                                      (match (b1.FStarC_Syntax_Syntax.sort).FStarC_Syntax_Syntax.n
                                       with
                                       | FStarC_Syntax_Syntax.Tm_fvar fv ->
                                           FStarC_Syntax_Syntax.fv_eq_lid fv
                                             FStarC_Parser_Const.unit_lid
                                       | uu___9 -> false)
                                  | uu___8 -> false in
                                if Prims.not is_unit_refinement
                                then
                                  let uu___8 =
                                    let uu___9 =
                                      let uu___10 =
                                        FStarC_Syntax_Syntax.bv_to_name x in
                                      FStarC_TypeChecker_Env.type_hypothesis
                                        env t uu___10 in
                                    FStarC_Syntax_Util.is_t_true uu___9 in
                                  Prims.not uu___8
                                else false
                            | uu___8 -> false in
                          let uu___7 = drops_typing_info () in
                          if uu___7
                          then
                            FStar_Pervasives.Inr
                              "binder is unused but its type carries information"
                          else
                            (let uu___8 = FStarC_Syntax_Util.is_total_comp c1 in
                             if uu___8
                             then
                               let maybe_close_with_unit_refinement x c =
                                 let x1 =
                                   {
                                     FStarC_Syntax_Syntax.ppname =
                                       (x.FStarC_Syntax_Syntax.ppname);
                                     FStarC_Syntax_Syntax.index =
                                       (x.FStarC_Syntax_Syntax.index);
                                     FStarC_Syntax_Syntax.sort =
                                       (FStarC_Syntax_Util.comp_result c1)
                                   } in
                                 maybe_capture_unit_refinement env
                                   x1.FStarC_Syntax_Syntax.sort x1 c in
                               let close_with_type_of_x x c =
                                 let uu___9 =
                                   maybe_close_with_unit_refinement x c in
                                 match uu___9 with
                                 | (c3, g, closed) ->
                                     if closed
                                     then (c3, g)
                                     else
                                       (let uu___10 =
                                          close_wp_comp env [x] c3 in
                                        let uu___11 =
                                          FStarC_TypeChecker_Env.close_guard
                                            env
                                            [FStarC_Syntax_Syntax.mk_binder x]
                                            g in
                                        (uu___10, uu___11)) in
                               let is_layered = false in
                               match (e1opt, b) with
                               | (FStar_Pervasives_Native.Some e,
                                  FStar_Pervasives_Native.Some x) when
                                   let uu___9 =
                                     let uu___10 =
                                       let uu___11 = optimize_bind_vc () in
                                       Prims.not uu___11 in
                                     if uu___10
                                     then true
                                     else Prims.not is_let_binding in
                                   (if uu___9 then true else is_layered) ->
                                   let uu___9 =
                                     let uu___10 =
                                       FStarC_Syntax_Subst.subst_comp
                                         [FStarC_Syntax_Syntax.NT (x, e)] c2 in
                                     maybe_close_with_unit_refinement x
                                       uu___10 in
                                   (match uu___9 with
                                    | (c21, g_close, uu___10) ->
                                        let uu___11 =
                                          let uu___12 =
                                            let uu___13 =
                                              let uu___14 =
                                                let uu___15 =
                                                  FStarC_TypeChecker_Env.map_guard
                                                    g_c2
                                                    (FStarC_Syntax_Subst.subst
                                                       [FStarC_Syntax_Syntax.NT
                                                          (x, e)]) in
                                                [uu___15; g_close] in
                                              g_c1 :: uu___14 in
                                            FStarC_TypeChecker_Env.conj_guards
                                              uu___13 in
                                          (c21, uu___12, "c1 Tot") in
                                        FStar_Pervasives.Inl uu___11)
                               | (FStar_Pervasives_Native.Some e,
                                  FStar_Pervasives_Native.Some x) ->
                                   let default_with_eqn uu___9 =
                                     let uu___10 =
                                       let uu___11 =
                                         FStarC_TypeChecker_Env.push_binders
                                           env
                                           [FStarC_Syntax_Syntax.mk_binder x] in
                                       let uu___12 =
                                         let uu___13 =
                                           env.FStarC_TypeChecker_Env.universe_of
                                             env x.FStarC_Syntax_Syntax.sort in
                                         let uu___14 =
                                           FStarC_Syntax_Syntax.bv_to_name x in
                                         FStarC_Syntax_Util.mk_eq2 uu___13
                                           x.FStarC_Syntax_Syntax.sort e
                                           uu___14 in
                                       weaken_comp uu___11 c2 uu___12 in
                                     match uu___10 with
                                     | (c21, g_c2') ->
                                         let uu___11 =
                                           close_with_type_of_x x c21 in
                                         (match uu___11 with
                                          | (c22, g_close) ->
                                              let uu___12 =
                                                let uu___13 =
                                                  let uu___14 =
                                                    let uu___15 =
                                                      let uu___16 =
                                                        FStarC_TypeChecker_Env.close_guard
                                                          env
                                                          [FStarC_Syntax_Syntax.mk_binder
                                                             x] g_c2' in
                                                      [uu___16; g_close] in
                                                    trivial_guard :: uu___15 in
                                                  FStarC_TypeChecker_Env.conj_guards
                                                    uu___14 in
                                                (c22, uu___13,
                                                  "c1 Tot with eq") in
                                              FStar_Pervasives.Inl uu___12) in
                                   let uu___9 =
                                     FStarC_Syntax_Util.is_tot_or_gtot_comp
                                       c2 in
                                   (if uu___9
                                    then
                                      (if is_let_binding
                                       then
                                         let uu___10 =
                                           let uu___11 =
                                             let uu___12 =
                                               FStarC_Syntax_Free.names_comp
                                                 c2 in
                                             FStarC_Class_Setlike.mem
                                               (FStarC_FlatSet.setlike_flat_set
                                                  FStarC_Syntax_Syntax.ord_bv)
                                               x uu___12 in
                                           Prims.not uu___11 in
                                         (if uu___10
                                          then
                                            let uu___11 =
                                              maybe_close_with_unit_refinement
                                                x c2 in
                                            match uu___11 with
                                            | (c21, g_close, uu___12) ->
                                                let uu___13 =
                                                  let uu___14 =
                                                    FStarC_TypeChecker_Env.conj_guards
                                                      [trivial_guard;
                                                      g_close] in
                                                  (c21, uu___14,
                                                    "both Tot/GTot") in
                                                FStar_Pervasives.Inl uu___13
                                          else default_with_eqn ())
                                       else
                                         (let uu___10 =
                                            let uu___11 =
                                              FStarC_Syntax_Subst.subst_comp
                                                [FStarC_Syntax_Syntax.NT
                                                   (x, e)] c2 in
                                            (uu___11, trivial_guard,
                                              "both Tot/GTot") in
                                          FStar_Pervasives.Inl uu___10))
                                    else default_with_eqn ())
                               | (uu___9, FStar_Pervasives_Native.Some x) ->
                                   let uu___10 = close_with_type_of_x x c2 in
                                   (match uu___10 with
                                    | (c21, g_close) ->
                                        let uu___11 =
                                          let uu___12 =
                                            FStarC_TypeChecker_Env.conj_guards
                                              [trivial_guard; g_close] in
                                          (c21, uu___12, "c1 Tot only close") in
                                        FStar_Pervasives.Inl uu___11)
                               | (uu___9, uu___10) ->
                                   aux_with_trivial_guard ()
                             else
                               (let uu___9 =
                                  let uu___10 =
                                    FStarC_Syntax_Util.is_tot_or_gtot_comp c1 in
                                  if uu___10
                                  then
                                    FStarC_Syntax_Util.is_tot_or_gtot_comp c2
                                  else false in
                                if uu___9
                                then
                                  let uu___10 =
                                    let uu___11 =
                                      FStarC_Syntax_Syntax.mk_GTotal
                                        (FStarC_Syntax_Util.comp_result c2) in
                                    (uu___11, trivial_guard, "both GTot") in
                                  FStar_Pervasives.Inl uu___10
                                else aux_with_trivial_guard ())) in
                        let uu___6 = try_simplify () in
                        match uu___6 with
                        | FStar_Pervasives.Inl (c, g, reason) ->
                            (debug
                               (fun uu___8 ->
                                  let uu___9 =
                                    FStarC_Class_Show.show
                                      FStarC_Syntax_Print.showable_comp c in
                                  FStarC_Format.print2
                                    "(2) bind: Simplified (because %s) to\n\t%s\n"
                                    reason uu___9);
                             (c, g))
                        | FStar_Pervasives.Inr reason ->
                            (debug
                               (fun uu___8 ->
                                  FStarC_Format.print1
                                    "(2) bind: Not simplified because %s\n"
                                    reason);
                             (let mk_bind1 c11 b1 c21 g =
                                let uu___8 =
                                  mk_bind env c11 b1 c21 bind_flags r1 in
                                match uu___8 with
                                | (c, g_bind) ->
                                    let uu___9 =
                                      FStarC_TypeChecker_Env.conj_guard g
                                        g_bind in
                                    (c, uu___9) in
                              let uu___8 =
                                let t = FStarC_Syntax_Util.comp_result c1 in
                                let uu___9 = comp_univ_opt c1 in
                                match uu___9 with
                                | FStar_Pervasives_Native.None ->
                                    let uu___10 =
                                      env.FStarC_TypeChecker_Env.universe_of
                                        env t in
                                    (uu___10, t)
                                | FStar_Pervasives_Native.Some u -> (u, t) in
                              match uu___8 with
                              | (u_res_t1, res_t1) ->
                                  let uu___9 =
                                    if
                                      match b with
                                      | FStar_Pervasives_Native.Some v ->
                                          true
                                      | uu___10 -> false
                                    then should_return env e1opt lc11
                                    else false in
                                  if uu___9
                                  then
                                    let e1 = FStarC_Option.must e1opt in
                                    let x = FStarC_Option.must b in
                                    (debug
                                       (fun uu___11 ->
                                          let uu___12 =
                                            FStarC_TypeChecker_Normalize.term_to_string
                                              env e1 in
                                          let uu___13 =
                                            FStarC_Class_Show.show
                                              FStarC_Syntax_Print.showable_bv
                                              x in
                                          FStarC_Format.print2
                                            "(3) bind (case b): Adding equality %s = %s\n"
                                            uu___12 uu___13);
                                     (let c21 =
                                        let uu___11 =
                                          let uu___12 =
                                            let uu___13 = optimize_bind_vc () in
                                            Prims.not uu___13 in
                                          if uu___12
                                          then true
                                          else Prims.not is_let_binding in
                                        if uu___11
                                        then
                                          FStarC_Syntax_Subst.subst_comp
                                            [FStarC_Syntax_Syntax.NT (x, e1)]
                                            c2
                                        else c2 in
                                      let x_eq_e =
                                        let uu___11 =
                                          FStarC_Syntax_Syntax.bv_to_name x in
                                        FStarC_Syntax_Util.mk_eq2 u_res_t1
                                          res_t1 e1 uu___11 in
                                      let uu___11 =
                                        let uu___12 =
                                          FStarC_TypeChecker_Env.push_binders
                                            env
                                            [FStarC_Syntax_Syntax.mk_binder x] in
                                        weaken_comp uu___12 c21 x_eq_e in
                                      match uu___11 with
                                      | (c22, g_w) ->
                                          let g =
                                            let uu___12 =
                                              let uu___13 =
                                                let uu___14 =
                                                  FStarC_TypeChecker_Env.close_guard
                                                    env
                                                    [FStarC_Syntax_Syntax.mk_binder
                                                       x] g_w in
                                                let uu___15 =
                                                  let uu___16 =
                                                    let uu___17 =
                                                      FStarC_TypeChecker_Common.weaken_guard_formula
                                                        g_c2 x_eq_e in
                                                    FStarC_TypeChecker_Env.close_guard
                                                      env
                                                      [FStarC_Syntax_Syntax.mk_binder
                                                         x] uu___17 in
                                                  [uu___16] in
                                                uu___14 :: uu___15 in
                                              g_c1 :: uu___13 in
                                            FStarC_TypeChecker_Env.conj_guards
                                              uu___12 in
                                          mk_bind1 c1 b c22 g))
                                  else mk_bind1 c1 b c2 trivial_guard))))) in
           FStarC_TypeChecker_Common.mk_lcomp joined_eff
             lc21.FStarC_TypeChecker_Common.res_typ bind_flags bind_it)
let weaken_guard (g1 : FStarC_TypeChecker_Common.guard_formula)
  (g2 : FStarC_TypeChecker_Common.guard_formula) :
  FStarC_TypeChecker_Common.guard_formula=
  match (g1, g2) with
  | (FStarC_TypeChecker_Common.NonTrivial f1,
     FStarC_TypeChecker_Common.NonTrivial f2) ->
      let g = FStarC_Syntax_Util.mk_imp f1 f2 in
      FStarC_TypeChecker_Common.NonTrivial g
  | uu___ -> g2
let assume_result_eq_pure_term_in_m (env : FStarC_TypeChecker_Env.env)
  (m_opt : FStarC_Ident.lident FStar_Pervasives_Native.option)
  (e : FStarC_Syntax_Syntax.term) (lc : FStarC_TypeChecker_Common.lcomp) :
  FStarC_TypeChecker_Common.lcomp=
  let m =
    let uu___ =
      if
        match m_opt with
        | FStar_Pervasives_Native.None -> true
        | uu___1 -> false
      then true
      else is_ghost_effect env lc.FStarC_TypeChecker_Common.eff_name in
    if uu___
    then FStarC_Parser_Const.effect_PURE_lid
    else FStarC_Option.must m_opt in
  let flags = lc.FStarC_TypeChecker_Common.cflags in
  let refine uu___ =
    let uu___1 = FStarC_TypeChecker_Common.lcomp_comp lc in
    match uu___1 with
    | (c, g_c) ->
        let u_t =
          let uu___2 = comp_univ_opt c in
          match uu___2 with
          | FStar_Pervasives_Native.Some u_t1 -> u_t1
          | FStar_Pervasives_Native.None ->
              env.FStarC_TypeChecker_Env.universe_of env
                (FStarC_Syntax_Util.comp_result c) in
        let uu___2 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
        if uu___2
        then
          let uu___3 =
            return_value env m (FStar_Pervasives_Native.Some u_t)
              (FStarC_Syntax_Util.comp_result c) e in
          (match uu___3 with
           | (retc, g_retc) ->
               let g_c1 = FStarC_TypeChecker_Env.conj_guard g_c g_retc in
               let uu___4 =
                 let uu___5 = FStarC_Syntax_Util.is_pure_comp c in
                 Prims.not uu___5 in
               if uu___4
               then
                 let retc1 = FStarC_TypeChecker_Env.comp_to_comp_typ env retc in
                 let retc2 =
                   {
                     FStarC_Syntax_Syntax.comp_univs =
                       (retc1.FStarC_Syntax_Syntax.comp_univs);
                     FStarC_Syntax_Syntax.effect_name =
                       FStarC_Parser_Const.effect_GHOST_lid;
                     FStarC_Syntax_Syntax.result_typ =
                       (retc1.FStarC_Syntax_Syntax.result_typ);
                     FStarC_Syntax_Syntax.comp_pre =
                       (retc1.FStarC_Syntax_Syntax.comp_pre);
                     FStarC_Syntax_Syntax.comp_post =
                       (retc1.FStarC_Syntax_Syntax.comp_post);
                     FStarC_Syntax_Syntax.flags = flags
                   } in
                 let uu___5 = FStarC_Syntax_Syntax.mk_Comp retc2 in
                 (uu___5, g_c1)
               else
                 (let uu___5 =
                    FStarC_TypeChecker_Env.comp_set_flags env retc flags in
                  (uu___5, g_c1)))
        else
          (let c1 = FStarC_TypeChecker_Env.unfold_effect_abbrev env c in
           let t = c1.FStarC_Syntax_Syntax.result_typ in
           let c2 = FStarC_Syntax_Syntax.mk_Comp c1 in
           let x =
             FStarC_Syntax_Syntax.new_bv
               (FStar_Pervasives_Native.Some (t.FStarC_Syntax_Syntax.pos)) t in
           let xexp = FStarC_Syntax_Syntax.bv_to_name x in
           let env_x = FStarC_TypeChecker_Env.push_bv env x in
           let uu___3 =
             return_value env_x m (FStar_Pervasives_Native.Some u_t) t xexp in
           match uu___3 with
           | (ret, g_ret) ->
               let ret1 =
                 let uu___4 =
                   FStarC_TypeChecker_Env.comp_set_flags env_x ret [] in
                 FStarC_TypeChecker_Common.lcomp_of_comp uu___4 in
               let eq = FStarC_Syntax_Util.mk_eq2 u_t t xexp e in
               let eq_ret =
                 weaken_precondition env_x ret1
                   (FStarC_TypeChecker_Common.NonTrivial eq) in
               let uu___4 =
                 let uu___5 =
                   let uu___6 = FStarC_TypeChecker_Common.lcomp_of_comp c2 in
                   bind e.FStarC_Syntax_Syntax.pos false env
                     FStar_Pervasives_Native.None uu___6
                     ((FStar_Pervasives_Native.Some x), eq_ret) in
                 FStarC_TypeChecker_Common.lcomp_comp uu___5 in
               (match uu___4 with
                | (bind_c, g_bind) ->
                    let uu___5 =
                      FStarC_TypeChecker_Env.comp_set_flags env bind_c flags in
                    let uu___6 =
                      FStarC_TypeChecker_Env.conj_guards [g_c; g_ret; g_bind] in
                    (uu___5, uu___6))) in
  let uu___ = should_not_inline_lc lc in
  if uu___
  then
    let uu___1 =
      let uu___2 =
        let uu___3 = FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term e in
        FStar_Pprint.op_Hat_Hat
          (FStarC_Errors_Msg.text
             "assume_result_eq_pure_term cannot inline an non-inlineable lc : ")
          uu___3 in
      [uu___2] in
    FStarC_Errors.raise_error (FStarC_Syntax_Syntax.has_range_syntax ()) e
      FStarC_Errors_Codes.Fatal_UnexpectedTerm ()
      (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
      (Obj.magic uu___1)
  else
    (let uu___1 = refine () in
     match uu___1 with
     | (c, g) -> FStarC_TypeChecker_Common.lcomp_of_comp_guard c g)
let maybe_assume_result_eq_pure_term_in_m (env : FStarC_TypeChecker_Env.env)
  (m_opt : FStarC_Ident.lident FStar_Pervasives_Native.option)
  (e : FStarC_Syntax_Syntax.term) (lc : FStarC_TypeChecker_Common.lcomp) :
  FStarC_TypeChecker_Common.lcomp=
  let should_return1 =
    let uu___ =
      if Prims.not env.FStarC_TypeChecker_Env.phase1
      then should_return env (FStar_Pervasives_Native.Some e) lc
      else false in
    if uu___
    then
      let uu___1 = FStarC_TypeChecker_Common.is_lcomp_partial_return lc in
      Prims.not uu___1
    else false in
  if Prims.not should_return1
  then lc
  else assume_result_eq_pure_term_in_m env m_opt e lc
let maybe_assume_result_eq_pure_term (env : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (lc : FStarC_TypeChecker_Common.lcomp) :
  FStarC_TypeChecker_Common.lcomp=
  maybe_assume_result_eq_pure_term_in_m env FStar_Pervasives_Native.None e lc
let maybe_return_e2_and_bind (r : FStarC_Range_Type.t)
  (is_let_binding : Prims.bool) (env : FStarC_TypeChecker_Env.env)
  (e1opt : FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option)
  (lc1 : FStarC_TypeChecker_Common.lcomp) (e2 : FStarC_Syntax_Syntax.term)
  (xlc2 :
    (FStarC_Syntax_Syntax.bv FStar_Pervasives_Native.option *
      FStarC_TypeChecker_Common.lcomp))
  : FStarC_TypeChecker_Common.lcomp=
  let uu___ = xlc2 in
  match uu___ with
  | (x, lc2) ->
      let env_x =
        match x with
        | FStar_Pervasives_Native.None -> env
        | FStar_Pervasives_Native.Some x1 ->
            FStarC_TypeChecker_Env.push_bv env x1 in
      let uu___1 =
        FStarC_TypeChecker_Normalize.ghost_to_pure_lcomp2 env (lc1, lc2) in
      (match uu___1 with
       | (lc11, lc21) ->
           let lc22 =
             let eff1 =
               FStarC_TypeChecker_Env.norm_eff_name env
                 lc11.FStarC_TypeChecker_Common.eff_name in
             let eff2 =
               FStarC_TypeChecker_Env.norm_eff_name env
                 lc21.FStarC_TypeChecker_Common.eff_name in
             let uu___2 =
               if
                 FStarC_Ident.lid_equals eff2
                   FStarC_Parser_Const.effect_PURE_lid
               then
                 let uu___3 = FStarC_TypeChecker_Env.join_opt env eff1 eff2 in
                 match uu___3 with
                 | FStar_Pervasives_Native.None -> true
                 | uu___4 -> false
               else false in
             if uu___2
             then
               assume_result_eq_pure_term_in_m env_x
                 (FStar_Pervasives_Native.Some eff1) e2 lc21
             else
               (let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = is_pure_or_ghost_effect env eff1 in
                      Prims.not uu___6 in
                    if uu___5 then true else should_not_inline_lc lc11 in
                  if uu___4 then is_pure_or_ghost_effect env eff2 else false in
                if uu___3
                then
                  maybe_assume_result_eq_pure_term_in_m env_x
                    (FStar_Pervasives_Native.Some eff1) e2 lc21
                else lc21) in
           bind r is_let_binding env e1opt lc11 (x, lc22))
let fvar_env (env : FStarC_TypeChecker_Env.env) (lid : FStarC_Ident.lident) :
  FStarC_Syntax_Syntax.term=
  FStarC_Syntax_Syntax.fvar
    (FStarC_Ident.set_lid_range lid (FStarC_TypeChecker_Env.get_range env))
    FStar_Pervasives_Native.None
let comp_false (env : FStarC_TypeChecker_Env.env)
  (u : FStarC_Syntax_Syntax.universe) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.comp=
  let uu___ = fvar_env env FStarC_Parser_Const.false_lid in
  let uu___1 = FStarC_Syntax_Syntax.trivial_post t in
  mk_comp_l FStarC_Parser_Const.effect_PURE_lid u t uu___ uu___1 []
let mk_conjunction (env : 'uuuuu) (u_a : FStarC_Syntax_Syntax.universe)
  (a : FStarC_Syntax_Syntax.term) (p : FStarC_Syntax_Syntax.typ)
  (ct1 : FStarC_Syntax_Syntax.comp_typ) (ct2 : FStarC_Syntax_Syntax.comp_typ)
  (r : FStarC_Range_Type.t) :
  (FStarC_Syntax_Syntax.comp * FStarC_TypeChecker_Env.guard_t)=
  let np = FStarC_Syntax_Util.mk_neg p in
  let pre =
    let uu___ =
      FStarC_Syntax_Util.mk_imp_simp p ct1.FStarC_Syntax_Syntax.comp_pre in
    let uu___1 =
      FStarC_Syntax_Util.mk_imp_simp np ct2.FStarC_Syntax_Syntax.comp_pre in
    FStarC_Syntax_Util.mk_conj_simp uu___ uu___1 in
  let post =
    let uu___ =
      let uu___1 =
        FStarC_Syntax_Util.is_trivial_post ct1.FStarC_Syntax_Syntax.comp_post in
      if uu___1
      then
        FStarC_Syntax_Util.is_trivial_post ct2.FStarC_Syntax_Syntax.comp_post
      else false in
    if uu___
    then FStarC_Syntax_Syntax.trivial_post a
    else
      (let x = FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None a in
       let uu___1 =
         let uu___2 =
           let uu___3 =
             let uu___4 = FStarC_Syntax_Syntax.bv_to_name x in
             FStarC_Syntax_Util.apply_post ct1.FStarC_Syntax_Syntax.comp_post
               uu___4 in
           FStarC_Syntax_Util.mk_imp_simp p uu___3 in
         let uu___3 =
           let uu___4 =
             let uu___5 = FStarC_Syntax_Syntax.bv_to_name x in
             FStarC_Syntax_Util.apply_post ct2.FStarC_Syntax_Syntax.comp_post
               uu___5 in
           FStarC_Syntax_Util.mk_imp_simp np uu___4 in
         FStarC_Syntax_Util.mk_conj_simp uu___2 uu___3 in
       FStarC_Syntax_Util.abs [FStarC_Syntax_Syntax.mk_binder x] uu___1
         (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.post_rc)) in
  let uu___ =
    mk_comp_l ct1.FStarC_Syntax_Syntax.effect_name u_a a pre post [] in
  (uu___, FStarC_TypeChecker_Env.trivial_guard)
let get_neg_branch_conds
  (branch_conds : FStarC_Syntax_Syntax.formula Prims.list) :
  (FStarC_Syntax_Syntax.formula Prims.list * FStarC_Syntax_Syntax.formula)=
  let uu___ =
    let uu___1 =
      let uu___2 =
        FStarC_List.fold_left
          (fun uu___3 g ->
             match uu___3 with
             | (conds, acc) ->
                 let cond =
                   let uu___4 =
                     let uu___5 = FStarC_Syntax_Util.b2t g in
                     FStarC_Syntax_Util.mk_neg uu___5 in
                   FStarC_Syntax_Util.mk_conj acc uu___4 in
                 ((FStarC_List.op_At conds [cond]), cond))
          ([FStarC_Syntax_Util.t_true], FStarC_Syntax_Util.t_true)
          branch_conds in
      FStar_Pervasives_Native.fst uu___2 in
    FStarC_List.splitAt ((FStarC_List.length uu___1) - Prims.int_one) uu___1 in
  match uu___ with | (l1, l2) -> (l1, (FStarC_List.hd l2))
let bind_cases (env0 : FStarC_TypeChecker_Env.env)
  (res_t : FStarC_Syntax_Syntax.typ)
  (lcases :
    (FStarC_Syntax_Syntax.formula * FStarC_Ident.lident *
      FStarC_Syntax_Syntax.cflag Prims.list *
      (Prims.bool -> FStarC_TypeChecker_Common.lcomp)) Prims.list)
  (scrutinee : FStarC_Syntax_Syntax.bv) : FStarC_TypeChecker_Common.lcomp=
  let env =
    FStarC_TypeChecker_Env.push_binders env0
      [FStarC_Syntax_Syntax.mk_binder scrutinee] in
  let eff =
    FStarC_List.fold_left
      (fun eff1 uu___ ->
         match uu___ with
         | (uu___1, eff_label, uu___2, uu___3) ->
             join_effects env eff1 eff_label)
      FStarC_Parser_Const.effect_PURE_lid lcases in
  let bind_cases_flags = [] in
  let bind_cases1 uu___ =
    let u_res_t = env.FStarC_TypeChecker_Env.universe_of env res_t in
    let maybe_return eff_label_then cthen =
      let uu___1 =
        let uu___2 = is_pure_or_ghost_effect env eff in Prims.not uu___2 in
      if uu___1 then cthen true else cthen false in
    let uu___1 =
      let uu___2 =
        FStarC_List.map
          (fun uu___3 -> match uu___3 with | (g, uu___4, uu___5, uu___6) -> g)
          lcases in
      get_neg_branch_conds uu___2 in
    match uu___1 with
    | (neg_branch_conds, exhaustiveness_branch_cond) ->
        let uu___2 =
          match lcases with
          | [] ->
              let uu___3 = comp_false env u_res_t res_t in
              (uu___3, FStarC_TypeChecker_Env.trivial_guard)
          | uu___3 ->
              let uu___4 =
                let uu___5 =
                  match FStarC_List.splitAt
                          ((FStarC_List.length lcases) - Prims.int_one)
                          neg_branch_conds
                  with
                  | (l1, l2) -> (l1, (FStarC_List.hd l2)) in
                match uu___5 with
                | (neg_branch_conds1, neg_last) ->
                    let uu___6 =
                      match FStarC_List.splitAt
                              ((FStarC_List.length lcases) - Prims.int_one)
                              lcases
                      with
                      | (l1, l2) -> (l1, (FStarC_List.hd l2)) in
                    (match uu___6 with
                     | (lcases1, (g_last, eff_last, uu___7, c_last)) ->
                         let uu___8 =
                           let lc = maybe_return eff_last c_last in
                           let uu___9 =
                             FStarC_TypeChecker_Common.lcomp_comp lc in
                           match uu___9 with
                           | (c, g) ->
                               let uu___10 =
                                 let uu___11 =
                                   let uu___12 =
                                     FStarC_Syntax_Util.b2t g_last in
                                   FStarC_Syntax_Util.mk_conj uu___12
                                     neg_last in
                                 FStarC_TypeChecker_Common.weaken_guard_formula
                                   g uu___11 in
                               (c, uu___10) in
                         (match uu___8 with
                          | (c, g) -> (lcases1, neg_branch_conds1, c, g))) in
              (match uu___4 with
               | (lcases1, neg_branch_conds1, comp, g_comp) ->
                   FStarC_List.fold_right2
                     (fun uu___5 neg_cond uu___6 ->
                        match (uu___5, uu___6) with
                        | ((g, eff_label, uu___7, cthen), (celse, g_comp1))
                            ->
                            let uu___8 =
                              let uu___9 = maybe_return eff_label cthen in
                              FStarC_TypeChecker_Common.lcomp_comp uu___9 in
                            (match uu___8 with
                             | (cthen1, g_then) ->
                                 let uu___9 =
                                   lift_comps_sep_guards env cthen1 celse
                                     FStar_Pervasives_Native.None false in
                                 (match uu___9 with
                                  | (m, cthen2, celse1, g_lift_then,
                                     g_lift_else) ->
                                      let ct_then =
                                        FStarC_TypeChecker_Env.comp_to_comp_typ
                                          env cthen2 in
                                      let ct_else =
                                        FStarC_TypeChecker_Env.comp_to_comp_typ
                                          env celse1 in
                                      let uu___10 =
                                        let uu___11 =
                                          FStarC_Syntax_Util.b2t g in
                                        mk_conjunction env u_res_t res_t
                                          uu___11 ct_then ct_else
                                          (FStarC_TypeChecker_Env.get_range
                                             env) in
                                      (match uu___10 with
                                       | (c, g_conjunction) ->
                                           let uu___11 =
                                             let g1 =
                                               FStarC_Syntax_Util.b2t g in
                                             let uu___12 =
                                               let uu___13 =
                                                 FStarC_TypeChecker_Env.conj_guard
                                                   g_then g_lift_then in
                                               let uu___14 =
                                                 FStarC_Syntax_Util.mk_conj
                                                   neg_cond g1 in
                                               FStarC_TypeChecker_Common.weaken_guard_formula
                                                 uu___13 uu___14 in
                                             let uu___13 =
                                               let uu___14 =
                                                 let uu___15 =
                                                   FStarC_Syntax_Util.mk_neg
                                                     g1 in
                                                 FStarC_Syntax_Util.mk_conj
                                                   neg_cond uu___15 in
                                               FStarC_TypeChecker_Common.weaken_guard_formula
                                                 g_lift_else uu___14 in
                                             (uu___12, uu___13) in
                                           (match uu___11 with
                                            | (g_then1, g_else) ->
                                                let uu___12 =
                                                  FStarC_TypeChecker_Env.conj_guards
                                                    [g_comp1;
                                                    g_then1;
                                                    g_else;
                                                    g_conjunction] in
                                                (c, uu___12)))))) lcases1
                     neg_branch_conds1 (comp, g_comp)) in
        (match uu___2 with
         | (comp, g_comp) ->
             let uu___3 =
               let uu___4 =
                 let check =
                   FStarC_Syntax_Util.mk_imp exhaustiveness_branch_cond
                     FStarC_Syntax_Util.t_false in
                 let check1 =
                   label FStarC_TypeChecker_Err.exhaustiveness_check
                     (FStarC_TypeChecker_Env.get_range env) check in
                 strengthen_comp env FStar_Pervasives_Native.None comp check1
                   bind_cases_flags in
               match uu___4 with
               | (c, g) ->
                   let uu___5 = FStarC_TypeChecker_Env.conj_guard g_comp g in
                   (c, uu___5) in
             (match uu___3 with | (comp1, g_comp1) -> (comp1, g_comp1))) in
  FStarC_TypeChecker_Common.mk_lcomp eff res_t bind_cases_flags bind_cases1
let check_comp (env : FStarC_TypeChecker_Env.env) (use_eq : Prims.bool)
  (e : FStarC_Syntax_Syntax.term) (c : FStarC_Syntax_Syntax.comp)
  (c' : FStarC_Syntax_Syntax.comp) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.comp *
    FStarC_TypeChecker_Common.guard_t)=
  FStarC_Defensive.def_check_scoped FStarC_TypeChecker_Env.hasBinders_env
    FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp
    c.FStarC_Syntax_Syntax.pos "check_comp.c" env c;
  FStarC_Defensive.def_check_scoped FStarC_TypeChecker_Env.hasBinders_env
    FStarC_Class_Binders.hasNames_comp FStarC_Syntax_Print.pretty_comp
    c'.FStarC_Syntax_Syntax.pos "check_comp.c'" env c';
  (let uu___3 = FStarC_Debug.extreme () in
   if uu___3
   then
     let uu___4 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
     let uu___5 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c in
     let uu___6 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c' in
     FStarC_Format.print4
       "Checking comp relation:\n%s has type %s\n\t %s \n%s\n" uu___4 uu___5
       (if use_eq then "$:" else "<:") uu___6
   else ());
  (let spec_has_uvars c1 =
     let uu___3 =
       let uu___4 =
         let uu___5 =
           FStarC_Syntax_Free.uvars (FStarC_Syntax_Util.comp_pre c1) in
         FStarC_Class_Setlike.is_empty
           (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Free.ord_ctx_uvar)
           uu___5 in
       Prims.not uu___4 in
     if uu___3
     then true
     else
       (let uu___4 =
          let uu___5 =
            let uu___6 = FStarC_Syntax_Util.comp_post c1 in
            FStarC_Syntax_Free.uvars uu___6 in
          FStarC_Class_Setlike.is_empty
            (FStarC_FlatSet.setlike_flat_set FStarC_Syntax_Free.ord_ctx_uvar)
            uu___5 in
        Prims.not uu___4) in
   let eq_result_and_subsume uu___3 =
     let uu___4 =
       FStarC_TypeChecker_Rel.try_teq true env
         (FStarC_Syntax_Util.comp_result c)
         (FStarC_Syntax_Util.comp_result c') in
     match uu___4 with
     | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
     | FStar_Pervasives_Native.Some g_eq ->
         let uu___5 = FStarC_TypeChecker_Rel.sub_comp env c c' in
         (match uu___5 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some g ->
              let uu___6 =
                FStarC_Class_Monoid.op_Plus_Plus
                  FStarC_TypeChecker_Common.monoid_guard_t g_eq g in
              FStar_Pervasives_Native.Some uu___6) in
   let g =
     if use_eq
     then
       let uu___3 =
         let uu___4 = spec_has_uvars c in
         if uu___4 then true else spec_has_uvars c' in
       (if uu___3
        then
          let uu___4 = FStarC_TypeChecker_Rel.eq_comp env c c' in
          match uu___4 with
          | FStar_Pervasives_Native.Some g1 ->
              FStar_Pervasives_Native.Some g1
          | FStar_Pervasives_Native.None -> eq_result_and_subsume ()
        else eq_result_and_subsume ())
     else FStarC_TypeChecker_Rel.sub_comp env c c' in
   match g with
   | FStar_Pervasives_Native.None ->
       if use_eq
       then
         FStarC_TypeChecker_Err.computed_computation_type_does_not_match_annotation_eq
           env (FStarC_TypeChecker_Env.get_range env) e c c'
       else
         FStarC_TypeChecker_Err.computed_computation_type_does_not_match_annotation
           env (FStarC_TypeChecker_Env.get_range env) e c c'
   | FStar_Pervasives_Native.Some g1 -> (e, c', g1))
let universe_of_comp (env : FStarC_TypeChecker_Env.env)
  (u_res : FStarC_Syntax_Syntax.universe) (c : FStarC_Syntax_Syntax.comp) :
  FStarC_Syntax_Syntax.universe=
  let c_lid =
    FStarC_TypeChecker_Env.norm_eff_name env
      (FStarC_Syntax_Util.comp_effect_name c) in
  if FStarC_Syntax_Util.is_pure_or_ghost_effect c_lid
  then u_res
  else
    (let uu___ =
       let uu___1 = FStarC_TypeChecker_Env.lookup_effect_quals env c_lid in
       FStarC_List.existsb (fun q -> q = FStarC_Syntax_Syntax.TotalEffect)
         uu___1 in
     if uu___ then u_res else FStarC_Syntax_Syntax.U_zero)
let check_trivial_precondition_wp (env : FStarC_TypeChecker_Env.env)
  (c : FStarC_Syntax_Syntax.comp) :
  (FStarC_Syntax_Syntax.comp_typ * FStarC_Syntax_Syntax.formula *
    FStarC_TypeChecker_Common.guard_t)=
  let ct = FStarC_TypeChecker_Env.unfold_effect_abbrev env c in
  let vc = ct.FStarC_Syntax_Syntax.comp_pre in
  (ct, vc,
    (FStarC_TypeChecker_Env.guard_of_guard_formula
       (FStarC_TypeChecker_Common.NonTrivial vc)))
let maybe_lift (env : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (c1 : FStarC_Ident.lident)
  (c2 : FStarC_Ident.lident) (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.term=
  let norm_eff l =
    let l1 = FStarC_TypeChecker_Env.norm_eff_name env l in
    if FStarC_Ident.lid_equals l1 FStarC_Parser_Const.effect_Tot_lid
    then FStarC_Parser_Const.effect_PURE_lid
    else
      if FStarC_Ident.lid_equals l1 FStarC_Parser_Const.effect_GTot_lid
      then FStarC_Parser_Const.effect_GHOST_lid
      else l1 in
  let m1 = norm_eff c1 in
  let m2 = norm_eff c2 in
  if
    ((FStarC_Ident.lid_equals m1 m2) ||
       ((FStarC_Syntax_Util.is_pure_effect c1) &&
          (FStarC_Syntax_Util.is_ghost_effect c2)))
      ||
      ((FStarC_Syntax_Util.is_pure_effect c2) &&
         (FStarC_Syntax_Util.is_ghost_effect c1))
  then e
  else
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_meta
         {
           FStarC_Syntax_Syntax.tm2 = e;
           FStarC_Syntax_Syntax.meta =
             (FStarC_Syntax_Syntax.Meta_monadic_lift (m1, m2, t))
         }) e.FStarC_Syntax_Syntax.pos
let maybe_monadic (env : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (c : FStarC_Ident.lident)
  (t : FStarC_Syntax_Syntax.typ) : FStarC_Syntax_Syntax.term=
  let m = FStarC_TypeChecker_Env.norm_eff_name env c in
  let uu___ =
    let uu___1 =
      let uu___2 = is_pure_or_ghost_effect env m in
      if uu___2
      then true
      else FStarC_Ident.lid_equals m FStarC_Parser_Const.effect_Tot_lid in
    if uu___1
    then true
    else FStarC_Ident.lid_equals m FStarC_Parser_Const.effect_GTot_lid in
  if uu___
  then e
  else
    FStarC_Syntax_Syntax.mk
      (FStarC_Syntax_Syntax.Tm_meta
         {
           FStarC_Syntax_Syntax.tm2 = e;
           FStarC_Syntax_Syntax.meta =
             (FStarC_Syntax_Syntax.Meta_monadic (m, t))
         }) e.FStarC_Syntax_Syntax.pos
let coerce_with (env : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (lc : FStarC_TypeChecker_Common.lcomp)
  (f : FStarC_Ident.lident) (us : FStarC_Syntax_Syntax.universes)
  (eargs : FStarC_Syntax_Syntax.args) (comp2 : FStarC_Syntax_Syntax.comp) :
  (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.lcomp)=
  let uu___ = FStarC_TypeChecker_Env.try_lookup_lid env f in
  match uu___ with
  | FStar_Pervasives_Native.Some uu___1 ->
      ((let uu___3 = FStarC_Effect.op_Bang dbg_Coercions in
        if uu___3
        then
          FStarC_Format.print1 "Coercing with %s!\n"
            (FStarC_Ident.string_of_lid f)
        else ());
       (let lc2 = FStarC_TypeChecker_Common.lcomp_of_comp comp2 in
        let lc_res =
          bind e.FStarC_Syntax_Syntax.pos false env
            (FStar_Pervasives_Native.Some e) lc
            (FStar_Pervasives_Native.None, lc2) in
        let coercion =
          FStarC_Syntax_Syntax.fvar
            (FStarC_Ident.set_lid_range f e.FStarC_Syntax_Syntax.pos)
            FStar_Pervasives_Native.None in
        let coercion1 = FStarC_Syntax_Syntax.mk_Tm_uinst coercion us in
        let e1 =
          let uu___3 = FStarC_TypeChecker_Common.is_pure_or_ghost_lcomp lc in
          if uu___3
          then
            FStarC_Syntax_Syntax.mk_Tm_app coercion1
              (FStarC_List.op_At eargs [FStarC_Syntax_Syntax.as_arg e])
              e.FStarC_Syntax_Syntax.pos
          else
            (let x =
               FStarC_Syntax_Syntax.new_bv
                 (FStar_Pervasives_Native.Some (e.FStarC_Syntax_Syntax.pos))
                 lc.FStarC_TypeChecker_Common.res_typ in
             let e2 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     let uu___7 = FStarC_Syntax_Syntax.bv_to_name x in
                     FStarC_Syntax_Syntax.as_arg uu___7 in
                   [uu___6] in
                 FStarC_List.op_At eargs uu___5 in
               FStarC_Syntax_Syntax.mk_Tm_app coercion1 uu___4
                 e.FStarC_Syntax_Syntax.pos in
             let e3 =
               maybe_lift env e lc.FStarC_TypeChecker_Common.eff_name
                 lc_res.FStarC_TypeChecker_Common.eff_name
                 lc.FStarC_TypeChecker_Common.res_typ in
             let e21 =
               maybe_lift (FStarC_TypeChecker_Env.push_bv env x) e2
                 lc2.FStarC_TypeChecker_Common.eff_name
                 lc_res.FStarC_TypeChecker_Common.eff_name
                 lc2.FStarC_TypeChecker_Common.res_typ in
             let lb =
               FStarC_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl x) []
                 lc.FStarC_TypeChecker_Common.res_typ
                 lc_res.FStarC_TypeChecker_Common.eff_name e3 []
                 e3.FStarC_Syntax_Syntax.pos in
             let e4 =
               let uu___4 =
                 let uu___5 =
                   let uu___6 =
                     FStarC_Syntax_Subst.close
                       [FStarC_Syntax_Syntax.mk_binder x] e21 in
                   {
                     FStarC_Syntax_Syntax.lbs = (false, [lb]);
                     FStarC_Syntax_Syntax.body1 = uu___6
                   } in
                 FStarC_Syntax_Syntax.Tm_let uu___5 in
               FStarC_Syntax_Syntax.mk uu___4 e3.FStarC_Syntax_Syntax.pos in
             maybe_monadic env e4 lc_res.FStarC_TypeChecker_Common.eff_name
               lc_res.FStarC_TypeChecker_Common.res_typ) in
        (e1, lc_res)))
  | FStar_Pervasives_Native.None ->
      (FStarC_Errors.log_issue (FStarC_Syntax_Syntax.has_range_syntax ()) e
         FStarC_Errors_Codes.Warning_CoercionNotFound ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic
            (FStarC_Format.fmt1
               "Coercion %s was not found in the environment, not coercing."
               (FStarC_Ident.string_of_lid f)));
       (e, lc))
type isErased =
  | Yes of FStarC_Syntax_Syntax.term 
  | Maybe 
  | No 
let uu___is_Yes (projectee : isErased) : Prims.bool=
  match projectee with | Yes _0 -> true | uu___ -> false
let __proj__Yes__item___0 (projectee : isErased) : FStarC_Syntax_Syntax.term=
  match projectee with | Yes _0 -> _0
let uu___is_Maybe (projectee : isErased) : Prims.bool=
  match projectee with | Maybe -> true | uu___ -> false
let uu___is_No (projectee : isErased) : Prims.bool=
  match projectee with | No -> true | uu___ -> false
let rec check_erased (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.term) : isErased=
  let norm' =
    FStarC_TypeChecker_Normalize.normalize
      [FStarC_TypeChecker_Env.Beta;
      FStarC_TypeChecker_Env.Eager_unfolding;
      FStarC_TypeChecker_Env.UnfoldUntil FStarC_Syntax_Syntax.delta_constant;
      FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta;
      FStarC_TypeChecker_Env.Primops;
      FStarC_TypeChecker_Env.Unascribe;
      FStarC_TypeChecker_Env.Unmeta;
      FStarC_TypeChecker_Env.Unrefine;
      FStarC_TypeChecker_Env.Weak;
      FStarC_TypeChecker_Env.HNF;
      FStarC_TypeChecker_Env.Iota] in
  let t1 = norm' env t in
  let uu___ = FStarC_Syntax_Util.head_and_args_full t1 in
  match uu___ with
  | (h, args) ->
      let h1 = FStarC_Syntax_Util.un_uinst h in
      let r =
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Syntax_Subst.compress h1 in
            uu___3.FStarC_Syntax_Syntax.n in
          (uu___2, args) in
        match uu___1 with
        | (FStarC_Syntax_Syntax.Tm_fvar fv, (a, uu___2)::[]) when
            FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.erased_lid
            -> Yes a
        | (FStarC_Syntax_Syntax.Tm_uvar uu___2, uu___3) -> Maybe
        | (FStarC_Syntax_Syntax.Tm_unknown, uu___2) -> Maybe
        | (FStarC_Syntax_Syntax.Tm_match
           { FStarC_Syntax_Syntax.scrutinee = uu___2;
             FStarC_Syntax_Syntax.ret_opt = uu___3;
             FStarC_Syntax_Syntax.brs = branches;
             FStarC_Syntax_Syntax.rc_opt1 = uu___4;_},
           uu___5) ->
            FStarC_List.fold_left
              (fun acc br ->
                 match acc with
                 | Yes uu___6 -> Maybe
                 | Maybe -> Maybe
                 | No ->
                     let uu___6 = FStarC_Syntax_Subst.open_branch br in
                     (match uu___6 with
                      | (uu___7, uu___8, br_body) ->
                          let uu___9 =
                            let uu___10 =
                              let uu___11 =
                                let uu___12 =
                                  FStarC_Syntax_Free.names br_body in
                                FStarC_Class_Setlike.elems
                                  (FStarC_FlatSet.setlike_flat_set
                                     FStarC_Syntax_Syntax.ord_bv) uu___12 in
                              FStarC_TypeChecker_Env.push_bvs env uu___11 in
                            check_erased uu___10 br_body in
                          (match uu___9 with | No -> No | uu___10 -> Maybe)))
              No branches
        | uu___2 -> No in
      r
let rec first_opt :
  'a 'b .
    ('a -> 'b FStar_Pervasives_Native.option) ->
      'a Prims.list -> 'b FStar_Pervasives_Native.option
  =
  fun f xs ->
    match xs with
    | [] -> FStar_Pervasives_Native.None
    | x::xs1 ->
        let uu___ = f x in
        FStarC_Option.catch uu___ (fun uu___1 -> first_opt f xs1)
let op_let_Question (uu___ : unit) :
  'uuuuu FStar_Pervasives_Native.option ->
    ('uuuuu -> 'uuuuu1 FStar_Pervasives_Native.option) ->
      'uuuuu1 FStar_Pervasives_Native.option=
  FStarC_Option.bind
let bool_guard (b : Prims.bool) : unit FStar_Pervasives_Native.option=
  if b then FStar_Pervasives_Native.Some () else FStar_Pervasives_Native.None
let find_coercion (env : FStarC_TypeChecker_Env.env)
  (checked : FStarC_TypeChecker_Common.lcomp)
  (exp_t : FStarC_Syntax_Syntax.typ) (e : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.lcomp *
    FStarC_TypeChecker_Env.guard_t) FStar_Pervasives_Native.option=
  FStarC_Errors.with_ctx "find_coercion"
    (fun uu___ ->
       let rec is_type retry t =
         let uu___1 =
           let uu___2 = FStarC_Syntax_Subst.compress t in
           uu___2.FStarC_Syntax_Syntax.n in
         match uu___1 with
         | FStarC_Syntax_Syntax.Tm_type uu___2 -> true
         | uu___2 when retry ->
             let t1 = FStarC_TypeChecker_Normalize.unfold_whnf env t in
             let t2 = FStarC_Syntax_Util.unrefine t1 in is_type false t2
         | uu___2 -> false in
       let is_type1 = is_type true in
       let rec head_of t =
         let uu___1 =
           let uu___2 = FStarC_Syntax_Subst.compress t in
           uu___2.FStarC_Syntax_Syntax.n in
         match uu___1 with
         | FStarC_Syntax_Syntax.Tm_match
             { FStarC_Syntax_Syntax.scrutinee = t1;
               FStarC_Syntax_Syntax.ret_opt = uu___2;
               FStarC_Syntax_Syntax.brs = uu___3;
               FStarC_Syntax_Syntax.rc_opt1 = uu___4;_}
             -> head_of t1
         | FStarC_Syntax_Syntax.Tm_ascribed
             { FStarC_Syntax_Syntax.tm = t1;
               FStarC_Syntax_Syntax.asc = uu___2;
               FStarC_Syntax_Syntax.eff_opt = uu___3;_}
             -> head_of t1
         | FStarC_Syntax_Syntax.Tm_meta
             { FStarC_Syntax_Syntax.tm2 = t1;
               FStarC_Syntax_Syntax.meta = uu___2;_}
             -> head_of t1
         | FStarC_Syntax_Syntax.Tm_app uu___2 ->
             let uu___3 = FStarC_Syntax_Util.head_and_args_full t in
             (match uu___3 with | (t1, uu___4) -> head_of t1)
         | FStarC_Syntax_Syntax.Tm_abs uu___2 ->
             let uu___3 = FStarC_Syntax_Util.abs_formals_ln t in
             (match uu___3 with | (uu___4, t1, uu___5) -> head_of t1)
         | FStarC_Syntax_Syntax.Tm_refine
             { FStarC_Syntax_Syntax.b2 = b;
               FStarC_Syntax_Syntax.phi = uu___2;_}
             -> head_of b.FStarC_Syntax_Syntax.sort
         | uu___2 -> t in
       let is_prop t =
         let uu___1 =
           let uu___2 =
             let uu___3 = head_of t in FStarC_Syntax_Subst.compress uu___3 in
           uu___2.FStarC_Syntax_Syntax.n in
         match uu___1 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.prop_lid
         | uu___2 -> false in
       let is_bool t =
         let uu___1 =
           let uu___2 =
             let uu___3 = head_of t in FStarC_Syntax_Subst.compress uu___3 in
           uu___2.FStarC_Syntax_Syntax.n in
         match uu___1 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.bool_lid
         | uu___2 -> false in
       let is_head_defined t =
         let h = head_of t in
         let h1 = FStarC_Syntax_Subst.compress h in
         ((match h1.FStarC_Syntax_Syntax.n with
           | FStarC_Syntax_Syntax.Tm_fvar _0 -> true
           | uu___1 -> false) ||
            (match h1.FStarC_Syntax_Syntax.n with
             | FStarC_Syntax_Syntax.Tm_uinst _0 -> true
             | uu___1 -> false))
           ||
           (match h1.FStarC_Syntax_Syntax.n with
            | FStarC_Syntax_Syntax.Tm_type _0 -> true
            | uu___1 -> false) in
       let head_unfold env1 t =
         FStarC_TypeChecker_Normalize.unfold_whnf'
           [FStarC_TypeChecker_Env.Unascribe;
           FStarC_TypeChecker_Env.Unmeta;
           FStarC_TypeChecker_Env.Unrefine] env1 t in
       let uu___1 =
         let uu___2 =
           let uu___3 = is_head_defined exp_t in
           if uu___3
           then is_head_defined checked.FStarC_TypeChecker_Common.res_typ
           else false in
         bool_guard uu___2 in
       op_let_Question () uu___1
         (fun uu___2 ->
            let computed_t =
              head_unfold env checked.FStarC_TypeChecker_Common.res_typ in
            let uu___3 = FStarC_Syntax_Util.head_and_args_full computed_t in
            match uu___3 with
            | (head, args) ->
                let exp_t1 = head_unfold env exp_t in
                let uu___4 =
                  let uu___5 =
                    let uu___6 = FStarC_Syntax_Util.un_uinst head in
                    uu___6.FStarC_Syntax_Syntax.n in
                  (uu___5, args) in
                (match uu___4 with
                 | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.bool_lid
                     then is_prop exp_t1
                     else false ->
                     let lc2 =
                       let uu___5 =
                         FStarC_Syntax_Syntax.mk_Total
                           FStarC_Syntax_Syntax.t_prop in
                       FStarC_TypeChecker_Common.lcomp_of_comp uu___5 in
                     let lc_res =
                       bind e.FStarC_Syntax_Syntax.pos false env
                         (FStar_Pervasives_Native.Some e) checked
                         (FStar_Pervasives_Native.None, lc2) in
                     let uu___5 =
                       let uu___6 = FStarC_Syntax_Util.mk_b2t e in
                       (uu___6, lc_res, FStarC_TypeChecker_Env.trivial_guard) in
                     FStar_Pervasives_Native.Some uu___5
                 | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.prop_lid
                     then is_type1 exp_t1
                     else false ->
                     let lc2 =
                       let uu___5 =
                         FStarC_Syntax_Syntax.mk_Total
                           FStarC_Syntax_Util.ktype0 in
                       FStarC_TypeChecker_Common.lcomp_of_comp uu___5 in
                     let lc_res =
                       bind e.FStarC_Syntax_Syntax.pos false env
                         (FStar_Pervasives_Native.Some e) checked
                         (FStar_Pervasives_Native.None, lc2) in
                     let uu___5 =
                       let uu___6 = FStarC_Syntax_Util.mk_squash e in
                       (uu___6, lc_res, FStarC_TypeChecker_Env.trivial_guard) in
                     FStar_Pervasives_Native.Some uu___5
                 | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.bool_lid
                     then is_type1 exp_t1
                     else false ->
                     let lc2 =
                       let uu___5 =
                         FStarC_Syntax_Syntax.mk_Total
                           FStarC_Syntax_Util.ktype0 in
                       FStarC_TypeChecker_Common.lcomp_of_comp uu___5 in
                     let lc_res =
                       bind e.FStarC_Syntax_Syntax.pos false env
                         (FStar_Pervasives_Native.Some e) checked
                         (FStar_Pervasives_Native.None, lc2) in
                     let uu___5 =
                       let uu___6 =
                         let uu___7 = FStarC_Syntax_Util.mk_b2t e in
                         FStarC_Syntax_Util.mk_squash uu___7 in
                       (uu___6, lc_res, FStarC_TypeChecker_Env.trivial_guard) in
                     FStar_Pervasives_Native.Some uu___5
                 | (FStarC_Syntax_Syntax.Tm_fvar fv, []) when
                     if
                       FStarC_Syntax_Syntax.fv_eq_lid fv
                         FStarC_Parser_Const.prop_lid
                     then is_bool exp_t1
                     else false ->
                     let lc2 =
                       let uu___5 =
                         FStarC_Syntax_Syntax.mk_GTotal
                           FStarC_Syntax_Util.t_bool in
                       FStarC_TypeChecker_Common.lcomp_of_comp uu___5 in
                     let lc_res =
                       bind e.FStarC_Syntax_Syntax.pos false env
                         (FStar_Pervasives_Native.Some e) checked
                         (FStar_Pervasives_Native.None, lc2) in
                     let uu___5 =
                       let uu___6 = FStarC_Syntax_Util.mk_t2b e in
                       (uu___6, lc_res, FStarC_TypeChecker_Env.trivial_guard) in
                     FStar_Pervasives_Native.Some uu___5
                 | uu___5 ->
                     let head_lid_of t =
                       let uu___6 =
                         let uu___7 =
                           let uu___8 = head_of t in
                           FStarC_Syntax_Subst.compress uu___8 in
                         uu___7.FStarC_Syntax_Syntax.n in
                       match uu___6 with
                       | FStarC_Syntax_Syntax.Tm_fvar fv ->
                           FStar_Pervasives_Native.Some
                             (FStarC_Syntax_Syntax.lid_of_fv fv)
                       | FStarC_Syntax_Syntax.Tm_uinst
                           ({
                              FStarC_Syntax_Syntax.n =
                                FStarC_Syntax_Syntax.Tm_fvar fv;
                              FStarC_Syntax_Syntax.pos = uu___7;
                              FStarC_Syntax_Syntax.hash_code = uu___8;_},
                            uu___9)
                           ->
                           FStar_Pervasives_Native.Some
                             (FStarC_Syntax_Syntax.lid_of_fv fv)
                       | uu___7 -> FStar_Pervasives_Native.None in
                     let uu___6 = head_lid_of exp_t1 in
                     op_let_Question () uu___6
                       (fun exp_head_lid ->
                          let uu___7 = head_lid_of computed_t in
                          op_let_Question () uu___7
                            (fun computed_head_lid ->
                               let candidates =
                                 FStarC_TypeChecker_Env.lookup_attr env
                                   (FStarC_Ident.string_of_lid
                                      FStarC_Parser_Const.coercion_lid) in
                               first_opt
                                 (fun se ->
                                    op_let_Question ()
                                      (match se.FStarC_Syntax_Syntax.sigel
                                       with
                                       | FStarC_Syntax_Syntax.Sig_let
                                           {
                                             FStarC_Syntax_Syntax.lbs1 =
                                               (uu___8, lb::[]);
                                             FStarC_Syntax_Syntax.lids1 =
                                               uu___9;_}
                                           ->
                                           FStar_Pervasives_Native.Some
                                             ((FStarC_Syntax_Syntax.lid_of_fv
                                                 (match lb.FStarC_Syntax_Syntax.lbname
                                                  with
                                                  | FStar_Pervasives.Inr v ->
                                                      v)),
                                               (lb.FStarC_Syntax_Syntax.lbunivs),
                                               (lb.FStarC_Syntax_Syntax.lbtyp))
                                       | FStarC_Syntax_Syntax.Sig_declare_typ
                                           { FStarC_Syntax_Syntax.lid2 = lid;
                                             FStarC_Syntax_Syntax.us2 = us;
                                             FStarC_Syntax_Syntax.t2 = t;_}
                                           ->
                                           FStar_Pervasives_Native.Some
                                             (lid, us, t)
                                       | uu___8 ->
                                           FStar_Pervasives_Native.None)
                                      (fun uu___8 ->
                                         match uu___8 with
                                         | (f_name, f_us, f_typ) ->
                                             let uu___9 =
                                               FStarC_Syntax_Subst.open_univ_vars
                                                 f_us f_typ in
                                             (match uu___9 with
                                              | (uu___10, f_typ1) ->
                                                  let uu___11 =
                                                    FStarC_TypeChecker_Overload.coercion_source_and_target
                                                      env f_typ1 in
                                                  op_let_Question () uu___11
                                                    (fun uu___12 ->
                                                       match uu___12 with
                                                       | (src_fv, tgt_fv) ->
                                                           let uu___13 =
                                                             bool_guard
                                                               (FStarC_Ident.lid_equals
                                                                  computed_head_lid
                                                                  (FStarC_Syntax_Syntax.lid_of_fv
                                                                    src_fv)) in
                                                           op_let_Question ()
                                                             uu___13
                                                             (fun uu___14 ->
                                                                let uu___15 =
                                                                  bool_guard
                                                                    (
                                                                    FStarC_Ident.lid_equals
                                                                    exp_head_lid
                                                                    (FStarC_Syntax_Syntax.lid_of_fv
                                                                    tgt_fv)) in
                                                                op_let_Question
                                                                  () uu___15
                                                                  (fun
                                                                    uu___16
                                                                    ->
                                                                    let f_tm
                                                                    =
                                                                    FStarC_Syntax_Syntax.fvar
                                                                    f_name
                                                                    FStar_Pervasives_Native.None in
                                                                    let tt =
                                                                    FStarC_Syntax_Util.mk_app
                                                                    f_tm
                                                                    [
                                                                    FStarC_Syntax_Syntax.as_arg
                                                                    e] in
                                                                    let uu___17
                                                                    =
                                                                    env.FStarC_TypeChecker_Env.tc_term
                                                                    {
                                                                    FStarC_TypeChecker_Env.solver
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.solver);
                                                                    FStarC_TypeChecker_Env.range
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.range);
                                                                    FStarC_TypeChecker_Env.curmodule
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.curmodule);
                                                                    FStarC_TypeChecker_Env.gamma
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.gamma);
                                                                    FStarC_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.gamma_sig);
                                                                    FStarC_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.gamma_cache);
                                                                    FStarC_TypeChecker_Env.modules
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.modules);
                                                                    FStarC_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    (exp_t1,
                                                                    false));
                                                                    FStarC_TypeChecker_Env.sigtab
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.sigtab);
                                                                    FStarC_TypeChecker_Env.attrtab
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.attrtab);
                                                                    FStarC_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.instantiate_imp);
                                                                    FStarC_TypeChecker_Env.effects
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.effects);
                                                                    FStarC_TypeChecker_Env.generalize
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.generalize);
                                                                    FStarC_TypeChecker_Env.letrecs
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.letrecs);
                                                                    FStarC_TypeChecker_Env.top_level
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.top_level);
                                                                    FStarC_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.check_uvars);
                                                                    FStarC_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.use_eq_strict);
                                                                    FStarC_TypeChecker_Env.is_iface
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.is_iface);
                                                                    FStarC_TypeChecker_Env.admit
                                                                    = true;
                                                                    FStarC_TypeChecker_Env.phase1
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.phase1);
                                                                    FStarC_TypeChecker_Env.failhard
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.failhard);
                                                                    FStarC_TypeChecker_Env.flychecking
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.flychecking);
                                                                    FStarC_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.uvar_subtyping);
                                                                    FStarC_TypeChecker_Env.intactics
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.intactics);
                                                                    FStarC_TypeChecker_Env.nocoerce
                                                                    = true;
                                                                    FStarC_TypeChecker_Env.tc_term
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.tc_term);
                                                                    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                                    FStarC_TypeChecker_Env.universe_of
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.universe_of);
                                                                    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                                    FStarC_TypeChecker_Env.teq_nosmt_force
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.teq_nosmt_force);
                                                                    FStarC_TypeChecker_Env.subtype_nosmt_force
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
                                                                    FStarC_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStarC_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.normalized_eff_names);
                                                                    FStarC_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.fv_delta_depths);
                                                                    FStarC_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.proof_ns);
                                                                    FStarC_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.synth_hook);
                                                                    FStarC_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStarC_TypeChecker_Env.splice
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.splice);
                                                                    FStarC_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.mpreprocess);
                                                                    FStarC_TypeChecker_Env.postprocess
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.postprocess);
                                                                    FStarC_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.identifier_info);
                                                                    FStarC_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.tc_hooks);
                                                                    FStarC_TypeChecker_Env.dsenv
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.dsenv);
                                                                    FStarC_TypeChecker_Env.nbe
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.nbe);
                                                                    FStarC_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.strict_args_tab);
                                                                    FStarC_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.erasable_types_tab);
                                                                    FStarC_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
                                                                    FStarC_TypeChecker_Env.unif_allow_ref_guards
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
                                                                    FStarC_TypeChecker_Env.erase_erasable_args
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.erase_erasable_args);
                                                                    FStarC_TypeChecker_Env.core_check
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.core_check);
                                                                    FStarC_TypeChecker_Env.missing_decl
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.missing_decl);
                                                                    FStarC_TypeChecker_Env.iface_todo
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.iface_todo);
                                                                    FStarC_TypeChecker_Env.iface_hidden
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.iface_hidden);
                                                                    FStarC_TypeChecker_Env.iface_lids
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.iface_lids);
                                                                    FStarC_TypeChecker_Env.iface_val_lids
                                                                    =
                                                                    (env.FStarC_TypeChecker_Env.iface_val_lids)
                                                                    } tt in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___17))))))
                                 candidates)))))
let maybe_coerce_lc (env : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (lc : FStarC_TypeChecker_Common.lcomp)
  (exp_t : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.lcomp *
    FStarC_TypeChecker_Common.guard_t)=
  let head_types_equal t0 t1 =
    let uu___ =
      let uu___1 =
        let uu___2 =
          let uu___3 = FStarC_Syntax_Util.unrefine t0 in
          FStarC_Syntax_Util.un_uinst uu___3 in
        uu___2.FStarC_Syntax_Syntax.n in
      let uu___2 =
        let uu___3 =
          let uu___4 = FStarC_Syntax_Util.unrefine t1 in
          FStarC_Syntax_Util.un_uinst uu___4 in
        uu___3.FStarC_Syntax_Syntax.n in
      (uu___1, uu___2) in
    match uu___ with
    | (FStarC_Syntax_Syntax.Tm_fvar fv0, FStarC_Syntax_Syntax.Tm_fvar fv1) ->
        FStarC_Syntax_Syntax.fv_eq fv0 fv1
    | uu___1 -> false in
  let should_coerce =
    if
      env.FStarC_TypeChecker_Env.phase1 &&
        (Prims.not env.FStarC_TypeChecker_Env.nocoerce)
    then
      let uu___ = head_types_equal lc.FStarC_TypeChecker_Common.res_typ exp_t in
      Prims.not uu___
    else false in
  if Prims.not should_coerce
  then
    ((let uu___1 = FStarC_Effect.op_Bang dbg_Coercions in
      if uu___1
      then
        let uu___2 =
          FStarC_Class_Show.show FStarC_Range_Ops.showable_range
            e.FStarC_Syntax_Syntax.pos in
        let uu___3 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
        let uu___4 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
            lc.FStarC_TypeChecker_Common.res_typ in
        let uu___5 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term exp_t in
        FStarC_Format.print4
          "(%s) NOT Trying to coerce %s from type (%s) to type (%s)\n" uu___2
          uu___3 uu___4 uu___5
      else ());
     (e, lc, FStarC_TypeChecker_Env.trivial_guard))
  else
    ((let uu___1 = FStarC_Effect.op_Bang dbg_Coercions in
      if uu___1
      then
        let uu___2 =
          FStarC_Class_Show.show FStarC_Range_Ops.showable_range
            e.FStarC_Syntax_Syntax.pos in
        let uu___3 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
        let uu___4 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
            lc.FStarC_TypeChecker_Common.res_typ in
        let uu___5 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term exp_t in
        FStarC_Format.print4
          "(%s) Trying to coerce %s from type (%s) to type (%s)\n" uu___2
          uu___3 uu___4 uu___5
      else ());
     (let uu___1 = find_coercion env lc exp_t e in
      match uu___1 with
      | FStar_Pervasives_Native.Some (coerced, lc1, g) ->
          ((let uu___3 = FStarC_Effect.op_Bang dbg_Coercions in
            if uu___3
            then
              let uu___4 =
                FStarC_Range_Ops.string_of_range e.FStarC_Syntax_Syntax.pos in
              let uu___5 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
              let uu___6 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
                  coerced in
              FStarC_Format.print3 "(%s) COERCING %s to %s\n" uu___4 uu___5
                uu___6
            else ());
           (coerced, lc1, g))
      | FStar_Pervasives_Native.None ->
          ((let uu___3 = FStarC_Effect.op_Bang dbg_Coercions in
            if uu___3
            then
              let uu___4 =
                FStarC_Range_Ops.string_of_range e.FStarC_Syntax_Syntax.pos in
              FStarC_Format.print1 "(%s) No user coercion found\n" uu___4
            else ());
           (let strip_hide_or_reveal e1 hide_or_reveal =
              let uu___3 = FStarC_Syntax_Util.leftmost_head_and_args e1 in
              match uu___3 with
              | (hd, args) ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStarC_Syntax_Subst.compress hd in
                      uu___6.FStarC_Syntax_Syntax.n in
                    (uu___5, args) in
                  (match uu___4 with
                   | (FStarC_Syntax_Syntax.Tm_uinst (hd1, uu___5),
                      (uu___6, aq_t)::(e2, aq_e)::[]) when
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             FStarC_Syntax_Util.is_fvar hide_or_reveal hd1 in
                           if uu___9
                           then
                             match aq_t with
                             | FStar_Pervasives_Native.Some v -> true
                             | uu___10 -> false
                           else false in
                         if uu___8
                         then
                           (match aq_t with
                            | FStar_Pervasives_Native.Some v -> v).FStarC_Syntax_Syntax.aqual_implicit
                         else false in
                       if uu___7
                       then
                         (aq_e = FStar_Pervasives_Native.None) ||
                           (Prims.not
                              (match aq_e with
                               | FStar_Pervasives_Native.Some v -> v).FStarC_Syntax_Syntax.aqual_implicit)
                       else false -> FStar_Pervasives_Native.Some e2
                   | uu___5 -> FStar_Pervasives_Native.None) in
            let uu___3 =
              let uu___4 =
                check_erased env lc.FStarC_TypeChecker_Common.res_typ in
              let uu___5 = check_erased env exp_t in (uu___4, uu___5) in
            match uu___3 with
            | (No, Yes ty) ->
                let u = env.FStarC_TypeChecker_Env.universe_of env ty in
                let uu___4 =
                  FStarC_TypeChecker_Rel.get_subtyping_predicate env
                    lc.FStarC_TypeChecker_Common.res_typ ty in
                (match uu___4 with
                 | FStar_Pervasives_Native.None ->
                     (e, lc, FStarC_TypeChecker_Env.trivial_guard)
                 | FStar_Pervasives_Native.Some g ->
                     let g1 = FStarC_TypeChecker_Env.apply_guard g e in
                     let uu___5 =
                       let uu___6 = FStarC_Syntax_Syntax.mk_Total exp_t in
                       coerce_with env e lc FStarC_Parser_Const.hide 
                         [u] [FStarC_Syntax_Syntax.iarg ty] uu___6 in
                     (match uu___5 with
                      | (e_hide, lc1) ->
                          let e_hide1 =
                            let uu___6 =
                              strip_hide_or_reveal e
                                FStarC_Parser_Const.reveal in
                            FStarC_Option.dflt e_hide uu___6 in
                          (e_hide1, lc1, g1)))
            | (Yes ty, No) ->
                let u = env.FStarC_TypeChecker_Env.universe_of env ty in
                let uu___4 =
                  let uu___5 = FStarC_Syntax_Syntax.mk_GTotal ty in
                  coerce_with env e lc FStarC_Parser_Const.reveal [u]
                    [FStarC_Syntax_Syntax.iarg ty] uu___5 in
                (match uu___4 with
                 | (e_reveal, lc1) ->
                     let e_reveal1 =
                       let uu___5 =
                         strip_hide_or_reveal e FStarC_Parser_Const.hide in
                       FStarC_Option.dflt e_reveal uu___5 in
                     (e_reveal1, lc1, FStarC_TypeChecker_Env.trivial_guard))
            | uu___4 -> (e, lc, FStarC_TypeChecker_Env.trivial_guard)))))
let weaken_result_typ (env : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (lc : FStarC_TypeChecker_Common.lcomp)
  (t : FStarC_Syntax_Syntax.typ) (use_eq : Prims.bool) :
  (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.lcomp *
    FStarC_TypeChecker_Common.guard_t)=
  (let uu___1 = FStarC_Debug.high () in
   if uu___1
   then
     let uu___2 =
       FStarC_Class_Show.show FStarC_Class_Show.showable_bool use_eq in
     let uu___3 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
     let uu___4 = FStarC_TypeChecker_Common.lcomp_to_string lc in
     let uu___5 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
     FStarC_Format.print4
       "weaken_result_typ use_eq=%s e=(%s) lc=(%s) t=(%s)\n" uu___2 uu___3
       uu___4 uu___5
   else ());
  (let use_eq1 =
     if use_eq || env.FStarC_TypeChecker_Env.use_eq_strict
     then true
     else
       (let uu___1 =
          FStarC_TypeChecker_Env.effect_decl_opt env
            lc.FStarC_TypeChecker_Common.eff_name in
        match uu___1 with
        | FStar_Pervasives_Native.Some (ed, qualifiers) ->
            FStarC_List.contains FStarC_Syntax_Syntax.Reifiable qualifiers
        | uu___2 -> false) in
   let gopt =
     if use_eq1
     then
       let uu___1 =
         FStarC_TypeChecker_Rel.try_teq true env
           lc.FStarC_TypeChecker_Common.res_typ t in
       (uu___1, false)
     else
       (let uu___1 =
          FStarC_TypeChecker_Rel.get_subtyping_predicate env
            lc.FStarC_TypeChecker_Common.res_typ t in
        (uu___1, true)) in
   match gopt with
   | (FStar_Pervasives_Native.None, uu___1) ->
       if env.FStarC_TypeChecker_Env.failhard
       then
         FStarC_TypeChecker_Err.raise_basic_type_error env
           e.FStarC_Syntax_Syntax.pos (FStar_Pervasives_Native.Some e) t
           lc.FStarC_TypeChecker_Common.res_typ
       else
         (FStarC_TypeChecker_Rel.subtype_fail env e
            lc.FStarC_TypeChecker_Common.res_typ t;
          (e,
            {
              FStarC_TypeChecker_Common.eff_name =
                (lc.FStarC_TypeChecker_Common.eff_name);
              FStarC_TypeChecker_Common.res_typ = t;
              FStarC_TypeChecker_Common.cflags =
                (lc.FStarC_TypeChecker_Common.cflags);
              FStarC_TypeChecker_Common.comp_thunk =
                (lc.FStarC_TypeChecker_Common.comp_thunk)
            }, FStarC_TypeChecker_Env.trivial_guard))
   | (FStar_Pervasives_Native.Some g, apply_guard) ->
       (match FStarC_TypeChecker_Env.guard_form g with
        | FStarC_TypeChecker_Common.Trivial ->
            let strengthen_trivial uu___1 =
              let uu___2 = FStarC_TypeChecker_Common.lcomp_comp lc in
              match uu___2 with
              | (c, g_c) ->
                  let res_t = FStarC_Syntax_Util.comp_result c in
                  let set_result_typ c1 =
                    FStarC_Syntax_Util.set_result_typ c1 t in
                  let uu___3 =
                    let uu___4 =
                      FStarC_TypeChecker_TermEqAndSimplify.eq_tm env t res_t in
                    uu___4 = FStarC_TypeChecker_TermEqAndSimplify.Equal in
                  if uu___3
                  then
                    ((let uu___5 = FStarC_Debug.extreme () in
                      if uu___5
                      then
                        let uu___6 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_term res_t in
                        let uu___7 =
                          FStarC_Class_Show.show
                            FStarC_Syntax_Print.showable_term t in
                        FStarC_Format.print2
                          "weaken_result_type::strengthen_trivial: res_t:%s is same as t:%s\n"
                          uu___6 uu___7
                      else ());
                     (let uu___5 = set_result_typ c in (uu___5, g_c)))
                  else
                    (let is_res_t_refinement =
                       let res_t1 =
                         FStarC_TypeChecker_Normalize.normalize_refinement
                           FStarC_TypeChecker_Normalize.whnf_steps env res_t in
                       match res_t1.FStarC_Syntax_Syntax.n with
                       | FStarC_Syntax_Syntax.Tm_refine uu___4 -> true
                       | uu___4 -> false in
                     if is_res_t_refinement
                     then
                       let x =
                         FStarC_Syntax_Syntax.new_bv
                           (FStar_Pervasives_Native.Some
                              (res_t.FStarC_Syntax_Syntax.pos)) res_t in
                       let uu___4 =
                         let uu___5 =
                           FStarC_TypeChecker_Env.norm_eff_name env
                             (FStarC_Syntax_Util.comp_effect_name c) in
                         let uu___6 = comp_univ_opt c in
                         let uu___7 = FStarC_Syntax_Syntax.bv_to_name x in
                         return_value env uu___5 uu___6 res_t uu___7 in
                       match uu___4 with
                       | (cret, gret) ->
                           let lc1 =
                             let uu___5 =
                               FStarC_TypeChecker_Common.lcomp_of_comp c in
                             let uu___6 =
                               let uu___7 =
                                 FStarC_TypeChecker_Common.lcomp_of_comp cret in
                               ((FStar_Pervasives_Native.Some x), uu___7) in
                             bind e.FStarC_Syntax_Syntax.pos false env
                               (FStar_Pervasives_Native.Some e) uu___5 uu___6 in
                           ((let uu___6 = FStarC_Debug.extreme () in
                             if uu___6
                             then
                               let uu___7 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term e in
                               let uu___8 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_comp c in
                               let uu___9 =
                                 FStarC_Class_Show.show
                                   FStarC_Syntax_Print.showable_term t in
                               let uu___10 =
                                 FStarC_TypeChecker_Common.lcomp_to_string
                                   lc1 in
                               FStarC_Format.print4
                                 "weaken_result_type::strengthen_trivial: inserting a return for e: %s, c: %s, t: %s, and then post return lc: %s\n"
                                 uu___7 uu___8 uu___9 uu___10
                             else ());
                            (let uu___6 =
                               FStarC_TypeChecker_Common.lcomp_comp lc1 in
                             match uu___6 with
                             | (c1, g_lc) ->
                                 let uu___7 = set_result_typ c1 in
                                 let uu___8 =
                                   FStarC_TypeChecker_Env.conj_guards
                                     [g_c; gret; g_lc] in
                                 (uu___7, uu___8)))
                     else
                       ((let uu___5 = FStarC_Debug.extreme () in
                         if uu___5
                         then
                           let uu___6 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_term res_t in
                           let uu___7 =
                             FStarC_Class_Show.show
                               FStarC_Syntax_Print.showable_comp c in
                           FStarC_Format.print2
                             "weaken_result_type::strengthen_trivial: res_t:%s is not a refinement, leaving c:%s as is\n"
                             uu___6 uu___7
                         else ());
                        (let uu___5 = set_result_typ c in (uu___5, g_c)))) in
            let lc1 =
              FStarC_TypeChecker_Common.mk_lcomp
                lc.FStarC_TypeChecker_Common.eff_name t
                lc.FStarC_TypeChecker_Common.cflags strengthen_trivial in
            (e, lc1, g)
        | FStarC_TypeChecker_Common.NonTrivial f ->
            let g1 =
              {
                FStarC_TypeChecker_Common.guard_f =
                  FStarC_TypeChecker_Common.Trivial;
                FStarC_TypeChecker_Common.deferred_to_tac =
                  (g.FStarC_TypeChecker_Common.deferred_to_tac);
                FStarC_TypeChecker_Common.deferred =
                  (g.FStarC_TypeChecker_Common.deferred);
                FStarC_TypeChecker_Common.univ_ineqs =
                  (g.FStarC_TypeChecker_Common.univ_ineqs);
                FStarC_TypeChecker_Common.implicits =
                  (g.FStarC_TypeChecker_Common.implicits)
              } in
            let strengthen uu___1 =
              let f1 =
                FStarC_TypeChecker_Normalize.normalize
                  [FStarC_TypeChecker_Env.Beta;
                  FStarC_TypeChecker_Env.Eager_unfolding;
                  FStarC_TypeChecker_Env.Simplify;
                  FStarC_TypeChecker_Env.Primops] env f in
              let uu___2 =
                let uu___3 = FStarC_Syntax_Subst.compress f1 in
                uu___3.FStarC_Syntax_Syntax.n in
              match uu___2 with
              | FStarC_Syntax_Syntax.Tm_abs uu___3 when
                  let uu___4 = FStarC_Syntax_Util.abs_formals_ln f1 in
                  match uu___4 with
                  | (uu___5,
                     {
                       FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar
                         fv;
                       FStarC_Syntax_Syntax.pos = uu___6;
                       FStarC_Syntax_Syntax.hash_code = uu___7;_},
                     uu___8) ->
                      FStarC_Syntax_Syntax.fv_eq_lid fv
                        FStarC_Parser_Const.true_lid
                  | uu___5 -> false ->
                  let lc1 =
                    {
                      FStarC_TypeChecker_Common.eff_name =
                        (lc.FStarC_TypeChecker_Common.eff_name);
                      FStarC_TypeChecker_Common.res_typ = t;
                      FStarC_TypeChecker_Common.cflags =
                        (lc.FStarC_TypeChecker_Common.cflags);
                      FStarC_TypeChecker_Common.comp_thunk =
                        (lc.FStarC_TypeChecker_Common.comp_thunk)
                    } in
                  FStarC_TypeChecker_Common.lcomp_comp lc1
              | uu___3 ->
                  let uu___4 = FStarC_TypeChecker_Common.lcomp_comp lc in
                  (match uu___4 with
                   | (c, g_c) ->
                       ((let uu___6 = FStarC_Debug.extreme () in
                         if uu___6
                         then
                           let uu___7 =
                             FStarC_TypeChecker_Normalize.term_to_string env
                               lc.FStarC_TypeChecker_Common.res_typ in
                           let uu___8 =
                             FStarC_TypeChecker_Normalize.term_to_string env
                               t in
                           let uu___9 =
                             FStarC_TypeChecker_Normalize.comp_to_string env
                               c in
                           let uu___10 =
                             FStarC_TypeChecker_Normalize.term_to_string env
                               f1 in
                           FStarC_Format.print4
                             "Weakened from %s to %s\nStrengthening %s with guard %s\n"
                             uu___7 uu___8 uu___9 uu___10
                         else ());
                        (let u_t_opt = comp_univ_opt c in
                         let x =
                           FStarC_Syntax_Syntax.new_bv
                             (FStar_Pervasives_Native.Some
                                (t.FStarC_Syntax_Syntax.pos)) t in
                         let xexp = FStarC_Syntax_Syntax.bv_to_name x in
                         let uu___6 =
                           let uu___7 =
                             FStarC_TypeChecker_Env.norm_eff_name env
                               (FStarC_Syntax_Util.comp_effect_name c) in
                           return_value env uu___7 u_t_opt t xexp in
                         match uu___6 with
                         | (cret, gret) ->
                             let guard =
                               if apply_guard
                               then
                                 FStarC_Syntax_Syntax.mk_Tm_app f1
                                   [FStarC_Syntax_Syntax.as_arg xexp]
                                   f1.FStarC_Syntax_Syntax.pos
                               else f1 in
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 =
                                   FStarC_TypeChecker_Env.push_bvs env [x] in
                                 FStarC_TypeChecker_Env.set_range uu___9
                                   e.FStarC_Syntax_Syntax.pos in
                               let uu___9 =
                                 FStarC_TypeChecker_Common.lcomp_of_comp cret in
                               strengthen_precondition
                                 (FStar_Pervasives_Native.Some
                                    (FStarC_TypeChecker_Err.subtyping_failed
                                       env
                                       lc.FStarC_TypeChecker_Common.res_typ t))
                                 uu___8 e uu___9
                                 (FStarC_TypeChecker_Env.guard_of_guard_formula
                                    (FStarC_TypeChecker_Common.NonTrivial
                                       guard)) in
                             (match uu___7 with
                              | (eq_ret, _trivial_so_ok_to_discard) ->
                                  let x1 =
                                    {
                                      FStarC_Syntax_Syntax.ppname =
                                        (x.FStarC_Syntax_Syntax.ppname);
                                      FStarC_Syntax_Syntax.index =
                                        (x.FStarC_Syntax_Syntax.index);
                                      FStarC_Syntax_Syntax.sort =
                                        (lc.FStarC_TypeChecker_Common.res_typ)
                                    } in
                                  let c1 =
                                    let uu___8 =
                                      FStarC_TypeChecker_Common.lcomp_of_comp
                                        c in
                                    bind e.FStarC_Syntax_Syntax.pos false env
                                      (FStar_Pervasives_Native.Some e) uu___8
                                      ((FStar_Pervasives_Native.Some x1),
                                        eq_ret) in
                                  let uu___8 =
                                    FStarC_TypeChecker_Common.lcomp_comp c1 in
                                  (match uu___8 with
                                   | (c2, g_lc) ->
                                       ((let uu___10 =
                                           FStarC_Debug.extreme () in
                                         if uu___10
                                         then
                                           let uu___11 =
                                             FStarC_TypeChecker_Normalize.comp_to_string
                                               env c2 in
                                           FStarC_Format.print1
                                             "Strengthened to %s\n" uu___11
                                         else ());
                                        (let uu___10 =
                                           FStarC_TypeChecker_Env.conj_guards
                                             [g_c; gret; g_lc] in
                                         (c2, uu___10)))))))) in
            let flags = [] in
            let lc1 =
              let uu___1 =
                FStarC_TypeChecker_Env.norm_eff_name env
                  lc.FStarC_TypeChecker_Common.eff_name in
              FStarC_TypeChecker_Common.mk_lcomp uu___1 t flags strengthen in
            let g2 =
              {
                FStarC_TypeChecker_Common.guard_f =
                  FStarC_TypeChecker_Common.Trivial;
                FStarC_TypeChecker_Common.deferred_to_tac =
                  (g1.FStarC_TypeChecker_Common.deferred_to_tac);
                FStarC_TypeChecker_Common.deferred =
                  (g1.FStarC_TypeChecker_Common.deferred);
                FStarC_TypeChecker_Common.univ_ineqs =
                  (g1.FStarC_TypeChecker_Common.univ_ineqs);
                FStarC_TypeChecker_Common.implicits =
                  (g1.FStarC_TypeChecker_Common.implicits)
              } in
            (e, lc1, g2)))
let pure_or_ghost_pre_and_post (env : FStarC_TypeChecker_Env.env)
  (comp : FStarC_Syntax_Syntax.comp) :
  (FStarC_Syntax_Syntax.typ FStar_Pervasives_Native.option *
    FStarC_Syntax_Syntax.typ)=
  let mk_post_type res_t ens =
    let x = FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None res_t in
    let uu___ =
      let uu___1 = FStarC_Syntax_Syntax.bv_to_name x in
      FStarC_Syntax_Util.apply_post ens uu___1 in
    FStarC_Syntax_Util.refine x uu___ in
  let norm t =
    FStarC_TypeChecker_Normalize.normalize
      [FStarC_TypeChecker_Env.Beta; FStarC_TypeChecker_Env.Eager_unfolding]
      env t in
  let uu___ = FStarC_Syntax_Util.is_tot_or_gtot_comp comp in
  if uu___
  then (FStar_Pervasives_Native.None, (FStarC_Syntax_Util.comp_result comp))
  else
    (let ct = FStarC_TypeChecker_Env.unfold_effect_abbrev env comp in
     let req = ct.FStarC_Syntax_Syntax.comp_pre in
     let uu___1 =
       let uu___2 = norm req in FStar_Pervasives_Native.Some uu___2 in
     let uu___2 =
       let uu___3 =
         mk_post_type ct.FStarC_Syntax_Syntax.result_typ
           ct.FStarC_Syntax_Syntax.comp_post in
       norm uu___3 in
     (uu___1, uu___2))
let norm_reify (env : FStarC_TypeChecker_Env.env)
  (steps : FStarC_TypeChecker_Env.steps) (t : FStarC_Syntax_Syntax.term) :
  FStarC_Syntax_Syntax.term=
  FStarC_Defensive.def_check_scoped FStarC_TypeChecker_Env.hasBinders_env
    FStarC_Class_Binders.hasNames_term FStarC_Syntax_Print.pretty_term
    t.FStarC_Syntax_Syntax.pos "norm_reify" env t;
  (let t' =
     FStarC_TypeChecker_Normalize.normalize
       (FStarC_List.op_At
          [FStarC_TypeChecker_Env.Beta;
          FStarC_TypeChecker_Env.Reify;
          FStarC_TypeChecker_Env.Eager_unfolding;
          FStarC_TypeChecker_Env.AllowUnboundUniverses;
          FStarC_TypeChecker_Env.Exclude FStarC_TypeChecker_Env.Zeta] steps)
       env t in
   (let uu___2 = FStarC_Effect.op_Bang dbg_SMTEncodingReify in
    if uu___2
    then
      let uu___3 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
      let uu___4 =
        FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t' in
      FStarC_Format.print2 "Reified body %s \nto %s\n" uu___3 uu___4
    else ());
   t')
let remove_reify (t : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.term=
  let uu___ =
    let uu___1 =
      let uu___2 = FStarC_Syntax_Subst.compress t in
      uu___2.FStarC_Syntax_Syntax.n in
    match uu___1 with
    | FStarC_Syntax_Syntax.Tm_app uu___2 -> false
    | uu___2 -> true in
  if uu___
  then t
  else
    (let uu___1 = FStarC_Syntax_Util.head_and_args_full t in
     match uu___1 with
     | (head, args) ->
         let uu___2 =
           let uu___3 =
             let uu___4 = FStarC_Syntax_Subst.compress head in
             uu___4.FStarC_Syntax_Syntax.n in
           match uu___3 with
           | FStarC_Syntax_Syntax.Tm_constant (FStarC_Const.Const_reify
               uu___4) -> true
           | uu___4 -> false in
         if uu___2
         then
           (match args with
            | x::[] -> FStar_Pervasives_Native.fst x
            | uu___3 ->
                FStarC_Effect.failwith
                  "Impossible : Reify applied to multiple arguments after normalization.")
         else t)
let maybe_implicit_with_meta_or_attr (aq : FStarC_Syntax_Syntax.bqual)
  (attrs : FStarC_Syntax_Syntax.attribute Prims.list) : Prims.bool=
  match (aq, attrs) with
  | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta uu___), uu___1)
      -> true
  | (FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit uu___),
     uu___1::uu___2) -> true
  | uu___ -> false
let instantiate_one_binder (env : FStarC_TypeChecker_Env.env_t)
  (r : FStarC_Range_Type.t) (b : FStarC_Syntax_Syntax.binder) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.typ *
    FStarC_Syntax_Syntax.aqual * FStarC_TypeChecker_Common.guard_t)=
  (let uu___1 = FStarC_Debug.high () in
   if uu___1
   then
     let uu___2 =
       FStarC_Class_Show.show FStarC_Syntax_Print.showable_binder b in
     FStarC_Format.print1
       "instantiate_one_binder: Instantiating implicit binder \226\128\152%s\226\128\153\n"
       uu___2
   else ());
  (let op_Plus_Plus = FStarC_TypeChecker_Env.conj_guard in
   let uu___1 = b in
   match uu___1 with
   | { FStarC_Syntax_Syntax.binder_bv = x;
       FStarC_Syntax_Syntax.binder_qual = uu___2;
       FStarC_Syntax_Syntax.binder_positivity = uu___3;
       FStarC_Syntax_Syntax.binder_attrs = uu___4;_} ->
       let uu___5 = FStarC_TypeChecker_Env.uvar_meta_for_binder b in
       (match uu___5 with
        | (ctx_uvar_meta, should_unrefine) ->
            let t = x.FStarC_Syntax_Syntax.sort in
            let uu___6 =
              let msg =
                let is_typeclass =
                  match ctx_uvar_meta with
                  | FStar_Pervasives_Native.Some
                      (FStarC_Syntax_Syntax.Ctx_uvar_meta_tac tau) ->
                      FStarC_Syntax_Util.is_fvar
                        FStarC_Parser_Const.tcresolve_lid tau
                  | uu___7 -> false in
                let name =
                  let uu___7 =
                    let uu___8 =
                      FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv
                        x in
                    Prims.strcat uu___8 "\226\128\153" in
                  Prims.strcat "\226\128\152" uu___7 in
                if is_typeclass
                then "Typeclass constraint argument"
                else
                  if
                    (match ctx_uvar_meta with
                     | FStar_Pervasives_Native.Some v -> true
                     | uu___7 -> false)
                  then Prims.strcat "Instantiating meta argument " name
                  else Prims.strcat "Instantiating implicit argument " name in
              FStarC_TypeChecker_Env.new_implicit_var_aux msg r env t
                FStarC_Syntax_Syntax.Strict ctx_uvar_meta should_unrefine in
            (match uu___6 with
             | (varg, uu___7, implicits) ->
                 let aq = FStarC_Syntax_Util.aqual_of_binder b in
                 let arg = (varg, aq) in
                 let r1 = (varg, t, aq, implicits) in
                 ((let uu___9 = FStarC_Debug.high () in
                   if uu___9
                   then
                     let uu___10 =
                       FStarC_Class_Show.show
                         (FStarC_Class_Show.show_tuple2
                            FStarC_Syntax_Print.showable_term
                            FStarC_Syntax_Print.showable_term)
                         ((match r1 with | (_1, _2, _3, _4) -> _1),
                           (match r1 with | (_1, _2, _3, _4) -> _2)) in
                     FStarC_Format.print1
                       "instantiate_one_binder: result = %s\n" uu___10
                   else ());
                  r1))))
let maybe_instantiate (env : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (t : FStarC_Syntax_Syntax.typ) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.typ *
    FStarC_TypeChecker_Common.guard_t)=
  let torig = FStarC_Syntax_Subst.compress t in
  if Prims.not env.FStarC_TypeChecker_Env.instantiate_imp
  then
    (e, torig,
      (FStarC_Class_Monoid.mzero FStarC_TypeChecker_Common.monoid_guard_t))
  else
    ((let uu___1 = FStarC_Debug.high () in
      if uu___1
      then
        let uu___2 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term e in
        let uu___3 =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
        let uu___4 =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_option
               (FStarC_Class_Show.show_tuple2
                  FStarC_Syntax_Print.showable_term
                  FStarC_Class_Show.showable_bool))
            (FStarC_TypeChecker_Env.expected_typ env) in
        FStarC_Format.print3
          "maybe_instantiate: starting check for (%s) of type (%s), expected type is %s\n"
          uu___2 uu___3 uu___4
      else ());
     (let unfolded_arrow_formals env1 t1 =
        let rec aux env2 bs t2 =
          let t3 = FStarC_TypeChecker_Normalize.unfold_whnf env2 t2 in
          let uu___1 = FStarC_Syntax_Util.arrow_formals t3 in
          match uu___1 with
          | (bs', t4) ->
              (match bs' with
               | [] -> bs
               | bs'1 ->
                   let uu___2 = FStarC_TypeChecker_Env.push_binders env2 bs'1 in
                   aux uu___2 (FStarC_List.op_At bs bs'1) t4) in
        aux env1 [] t1 in
      let number_of_implicits t1 =
        let formals = unfolded_arrow_formals env t1 in
        let n_implicits =
          let uu___1 =
            FStarC_Util.prefix_until
              (fun uu___2 ->
                 match uu___2 with
                 | { FStarC_Syntax_Syntax.binder_bv = uu___3;
                     FStarC_Syntax_Syntax.binder_qual = imp;
                     FStarC_Syntax_Syntax.binder_positivity = uu___4;
                     FStarC_Syntax_Syntax.binder_attrs = uu___5;_} ->
                     if
                       (match imp with
                        | FStar_Pervasives_Native.None -> true
                        | uu___6 -> false)
                     then true
                     else
                       FStarC_Syntax_Util.eq_bqual imp
                         (FStar_Pervasives_Native.Some
                            FStarC_Syntax_Syntax.Equality)) formals in
          match uu___1 with
          | FStar_Pervasives_Native.None -> FStarC_List.length formals
          | FStar_Pervasives_Native.Some (implicits, _first_explicit, _rest)
              -> FStarC_List.length implicits in
        n_implicits in
      let inst_n_binders t1 =
        match FStarC_TypeChecker_Env.expected_typ env with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (expected_t, uu___1) ->
            let n_expected = number_of_implicits expected_t in
            let n_available = number_of_implicits t1 in
            if n_available < n_expected
            then
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      FStarC_Class_PP.pp FStarC_Class_PP.pp_int n_expected in
                    let uu___6 =
                      let uu___7 =
                        let uu___8 =
                          FStarC_Class_PP.pp FStarC_Syntax_Print.pretty_term
                            e in
                        let uu___9 =
                          let uu___10 =
                            let uu___11 =
                              FStarC_Class_PP.pp FStarC_Class_PP.pp_int
                                n_available in
                            FStar_Pprint.op_Hat_Hat uu___11
                              (FStarC_Errors_Msg.text ".") in
                          FStar_Pprint.op_Hat_Slash_Hat
                            (FStarC_Errors_Msg.text " has only ") uu___10 in
                        FStar_Pprint.op_Hat_Slash_Hat uu___8 uu___9 in
                      FStar_Pprint.op_Hat_Slash_Hat
                        (FStarC_Errors_Msg.text " implicit arguments, but ")
                        uu___7 in
                    FStar_Pprint.op_Hat_Slash_Hat uu___5 uu___6 in
                  FStar_Pprint.op_Hat_Slash_Hat
                    (FStarC_Errors_Msg.text "Expected a term with ") uu___4 in
                [uu___3] in
              FStarC_Errors.raise_error FStarC_TypeChecker_Env.hasRange_env
                env FStarC_Errors_Codes.Fatal_MissingImplicitArguments ()
                (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                (Obj.magic uu___2)
            else FStar_Pervasives_Native.Some (n_available - n_expected) in
      let decr_inst uu___1 =
        match uu___1 with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some i ->
            FStar_Pervasives_Native.Some (i - Prims.int_one) in
      let t1 = FStarC_TypeChecker_Normalize.unfold_whnf env t in
      let uu___1 = FStarC_Syntax_Util.arrow_formals_comp t1 in
      match uu___1 with
      | (bs, c) ->
          (match bs with
           | uu___2::uu___3 ->
               let rec aux subst inst_n bs1 =
                 match (inst_n, bs1) with
                 | (FStar_Pervasives_Native.Some uu___4, uu___5) when
                     uu___4 = Prims.int_zero ->
                     ([], bs1, subst, FStarC_TypeChecker_Env.trivial_guard)
                 | (uu___4,
                    { FStarC_Syntax_Syntax.binder_bv = uu___5;
                      FStarC_Syntax_Syntax.binder_qual =
                        FStar_Pervasives_Native.Some
                        (FStarC_Syntax_Syntax.Implicit uu___6);
                      FStarC_Syntax_Syntax.binder_positivity = uu___7;
                      FStarC_Syntax_Syntax.binder_attrs = uu___8;_}::rest)
                     ->
                     let b = FStarC_List.hd bs1 in
                     let b1 = FStarC_Syntax_Subst.subst_binder subst b in
                     let uu___9 =
                       instantiate_one_binder env e.FStarC_Syntax_Syntax.pos
                         b1 in
                     (match uu___9 with
                      | (tm, ty, aq, g) ->
                          let subst1 =
                            (FStarC_Syntax_Syntax.NT
                               ((b1.FStarC_Syntax_Syntax.binder_bv), tm))
                            :: subst in
                          let uu___10 = aux subst1 (decr_inst inst_n) rest in
                          (match uu___10 with
                           | (args, bs2, subst2, g') ->
                               let uu___11 =
                                 FStarC_Class_Monoid.op_Plus_Plus
                                   FStarC_TypeChecker_Common.monoid_guard_t g
                                   g' in
                               (((tm, aq) :: args), bs2, subst2, uu___11)))
                 | (uu___4,
                    { FStarC_Syntax_Syntax.binder_bv = uu___5;
                      FStarC_Syntax_Syntax.binder_qual =
                        FStar_Pervasives_Native.Some
                        (FStarC_Syntax_Syntax.Meta uu___6);
                      FStarC_Syntax_Syntax.binder_positivity = uu___7;
                      FStarC_Syntax_Syntax.binder_attrs = uu___8;_}::rest)
                     ->
                     let b = FStarC_List.hd bs1 in
                     let b1 = FStarC_Syntax_Subst.subst_binder subst b in
                     let uu___9 =
                       instantiate_one_binder env e.FStarC_Syntax_Syntax.pos
                         b1 in
                     (match uu___9 with
                      | (tm, ty, aq, g) ->
                          let subst1 =
                            (FStarC_Syntax_Syntax.NT
                               ((b1.FStarC_Syntax_Syntax.binder_bv), tm))
                            :: subst in
                          let uu___10 = aux subst1 (decr_inst inst_n) rest in
                          (match uu___10 with
                           | (args, bs2, subst2, g') ->
                               let uu___11 =
                                 FStarC_Class_Monoid.op_Plus_Plus
                                   FStarC_TypeChecker_Common.monoid_guard_t g
                                   g' in
                               (((tm, aq) :: args), bs2, subst2, uu___11)))
                 | (uu___4, bs2) ->
                     ([], bs2, subst,
                       (FStarC_Class_Monoid.mzero
                          FStarC_TypeChecker_Common.monoid_guard_t)) in
               let uu___4 =
                 let uu___5 = inst_n_binders t1 in aux [] uu___5 bs in
               (match uu___4 with
                | (args, bs1, subst, guard) ->
                    (match (args, bs1) with
                     | ([], uu___5) -> (e, torig, guard)
                     | (uu___5, []) when
                         let uu___6 = FStarC_Syntax_Util.is_total_comp c in
                         Prims.not uu___6 ->
                         (e, torig, FStarC_TypeChecker_Env.trivial_guard)
                     | uu___5 ->
                         let t2 =
                           match bs1 with
                           | [] -> FStarC_Syntax_Util.comp_result c
                           | uu___6 -> FStarC_Syntax_Util.arrow bs1 c in
                         let t3 = FStarC_Syntax_Subst.subst subst t2 in
                         let e1 =
                           FStarC_Syntax_Syntax.mk_Tm_app e args
                             e.FStarC_Syntax_Syntax.pos in
                         (e1, t3, guard)))
           | uu___2 -> (e, torig, FStarC_TypeChecker_Env.trivial_guard))))
let check_has_type (env : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (t1 : FStarC_Syntax_Syntax.typ)
  (t2 : FStarC_Syntax_Syntax.typ) (use_eq : Prims.bool) :
  FStarC_TypeChecker_Common.guard_t=
  let env1 = FStarC_TypeChecker_Env.set_range env e.FStarC_Syntax_Syntax.pos in
  let g_opt =
    if env1.FStarC_TypeChecker_Env.use_eq_strict
    then
      let uu___ = FStarC_TypeChecker_Rel.teq_nosmt_force env1 t1 t2 in
      (if uu___
       then FStar_Pervasives_Native.Some FStarC_TypeChecker_Env.trivial_guard
       else FStar_Pervasives_Native.None)
    else
      if use_eq
      then FStarC_TypeChecker_Rel.try_teq true env1 t1 t2
      else
        (let uu___ =
           FStarC_TypeChecker_Rel.get_subtyping_predicate env1 t1 t2 in
         match uu___ with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some f ->
             let uu___1 = FStarC_TypeChecker_Env.apply_guard f e in
             FStar_Pervasives_Native.Some uu___1) in
  match g_opt with
  | FStar_Pervasives_Native.None ->
      FStarC_TypeChecker_Err.expected_expression_of_type env1
        (FStarC_TypeChecker_Env.get_range env1) t2 e t1
  | FStar_Pervasives_Native.Some g -> g
let check_has_type_maybe_coerce (env : FStarC_TypeChecker_Env.env)
  (e : FStarC_Syntax_Syntax.term) (lc : FStarC_TypeChecker_Common.lcomp)
  (t2 : FStarC_Syntax_Syntax.typ) (use_eq : Prims.bool) :
  (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.lcomp *
    FStarC_TypeChecker_Common.guard_t)=
  let env1 = FStarC_TypeChecker_Env.set_range env e.FStarC_Syntax_Syntax.pos in
  let uu___ = maybe_coerce_lc env1 e lc t2 in
  match uu___ with
  | (e1, lc1, g_c) ->
      let g =
        check_has_type env1 e1 lc1.FStarC_TypeChecker_Common.res_typ t2
          use_eq in
      ((let uu___2 = FStarC_Effect.op_Bang dbg_Rel in
        if uu___2
        then
          let uu___3 = FStarC_TypeChecker_Rel.guard_to_string env1 g in
          FStarC_Format.print1 "Applied guard is %s\n" uu___3
        else ());
       (let uu___2 = FStarC_TypeChecker_Env.conj_guard g g_c in
        (e1, lc1, uu___2)))
let check_top_level (env : FStarC_TypeChecker_Env.env)
  (g : FStarC_TypeChecker_Common.guard_t)
  (lc : FStarC_TypeChecker_Common.lcomp) :
  (Prims.bool * FStarC_Syntax_Syntax.comp)=
  FStarC_Errors.with_ctx "While checking for top-level effects"
    (fun uu___ ->
       (let uu___2 = FStarC_Debug.medium () in
        if uu___2
        then
          let uu___3 = FStarC_TypeChecker_Common.lcomp_to_string lc in
          FStarC_Format.print1 "check_top_level, lc = %s\n" uu___3
        else ());
       (let discharge g1 =
          FStarC_TypeChecker_Rel.force_trivial_guard env g1;
          (let uu___3 = FStarC_TypeChecker_Common.is_pure_lcomp lc in
           if uu___3
           then true
           else
             (let uu___4 =
                let uu___5 =
                  FStarC_TypeChecker_Env.get_top_level_effect env
                    lc.FStarC_TypeChecker_Common.eff_name in
                match uu___5 with
                | FStar_Pervasives_Native.Some v -> true
                | uu___6 -> false in
              if uu___4
              then true
              else
                (let uu___5 =
                   FStarC_TypeChecker_Env.is_reifiable_effect env
                     lc.FStarC_TypeChecker_Common.eff_name in
                 if uu___5
                 then
                   let uu___6 =
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           FStarC_Class_PP.pp FStarC_Ident.pretty_lident
                             lc.FStarC_TypeChecker_Common.eff_name in
                         FStar_Pprint.op_Hat_Slash_Hat uu___9
                           (FStarC_Errors_Msg.text
                              "cannot be used as a top-level effect") in
                       FStar_Pprint.op_Hat_Slash_Hat
                         (FStarC_Errors_Msg.text "Effect") uu___8 in
                     [uu___7] in
                   FStarC_Errors.raise_error
                     FStarC_TypeChecker_Env.hasRange_env env
                     FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
                     (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
                     (Obj.magic uu___6)
                 else false))) in
        let g1 = FStarC_TypeChecker_Rel.solve_deferred_constraints env g in
        let uu___2 = FStarC_TypeChecker_Common.lcomp_comp lc in
        match uu___2 with
        | (c, g_c) ->
            let uu___3 = FStarC_TypeChecker_Common.is_total_lcomp lc in
            if uu___3
            then
              let uu___4 =
                let uu___5 = FStarC_TypeChecker_Env.conj_guard g1 g_c in
                discharge uu___5 in
              (uu___4, c)
            else
              (let c1 = FStarC_TypeChecker_Env.unfold_effect_abbrev env c in
               let us = c1.FStarC_Syntax_Syntax.comp_univs in
               let steps =
                 [FStarC_TypeChecker_Env.Beta;
                 FStarC_TypeChecker_Env.NoFullNorm;
                 FStarC_TypeChecker_Env.DoNotUnfoldPureLets] in
               let c2 =
                 let uu___4 = FStarC_Syntax_Syntax.mk_Comp c1 in
                 FStarC_TypeChecker_Normalize.normalize_comp steps env uu___4 in
               let uu___4 = check_trivial_precondition_wp env c2 in
               match uu___4 with
               | (ct, vc, g_pre) ->
                   ((let uu___6 = FStarC_Effect.op_Bang dbg_Simplification in
                     if uu___6
                     then
                       let uu___7 =
                         FStarC_Class_Show.show
                           FStarC_Syntax_Print.showable_term vc in
                       FStarC_Format.print1 "top-level VC: %s\n" uu___7
                     else ());
                    (let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           FStarC_TypeChecker_Env.conj_guard g_c g_pre in
                         FStarC_TypeChecker_Env.conj_guard g1 uu___8 in
                       discharge uu___7 in
                     let uu___7 = FStarC_Syntax_Syntax.mk_Comp ct in
                     (uu___6, uu___7))))))
let short_circuit (head : FStarC_Syntax_Syntax.term)
  (seen_args : FStarC_Syntax_Syntax.args) :
  FStarC_TypeChecker_Common.guard_formula=
  let short_bin_op f uu___ =
    match uu___ with
    | [] -> FStarC_TypeChecker_Common.Trivial
    | (fst, uu___1)::[] -> f fst
    | uu___1 -> FStarC_Effect.failwith "Unexpected args to binary operator" in
  let op_and_e e =
    let uu___ = FStarC_Syntax_Util.b2t e in
    FStarC_TypeChecker_Common.NonTrivial uu___ in
  let op_or_e e =
    let uu___ =
      let uu___1 = FStarC_Syntax_Util.b2t e in
      FStarC_Syntax_Util.mk_neg uu___1 in
    FStarC_TypeChecker_Common.NonTrivial uu___ in
  let op_and_t t = FStarC_TypeChecker_Common.NonTrivial t in
  let op_or_t t =
    let uu___ = FStarC_Syntax_Util.mk_neg t in
    FStarC_TypeChecker_Common.NonTrivial uu___ in
  let op_imp_t t = FStarC_TypeChecker_Common.NonTrivial t in
  let short_op_ite uu___ =
    match uu___ with
    | [] -> FStarC_TypeChecker_Common.Trivial
    | (guard, uu___1)::[] -> FStarC_TypeChecker_Common.NonTrivial guard
    | _then::(guard, uu___1)::[] ->
        let uu___2 = FStarC_Syntax_Util.mk_neg guard in
        FStarC_TypeChecker_Common.NonTrivial uu___2
    | uu___1 -> FStarC_Effect.failwith "Unexpected args to ITE" in
  let table =
    [(FStarC_Parser_Const.op_And, (short_bin_op op_and_e));
    (FStarC_Parser_Const.op_Or, (short_bin_op op_or_e));
    (FStarC_Parser_Const.and_lid, (short_bin_op op_and_t));
    (FStarC_Parser_Const.or_lid, (short_bin_op op_or_t));
    (FStarC_Parser_Const.imp_lid, (short_bin_op op_imp_t));
    (FStarC_Parser_Const.ite_lid, short_op_ite)] in
  match head.FStarC_Syntax_Syntax.n with
  | FStarC_Syntax_Syntax.Tm_fvar fv ->
      let lid = fv.FStarC_Syntax_Syntax.fv_name in
      let uu___ =
        FStarC_Util.find_map table
          (fun uu___1 ->
             match uu___1 with
             | (x, mk) ->
                 if FStarC_Ident.lid_equals x lid
                 then
                   let uu___2 = mk seen_args in
                   FStar_Pervasives_Native.Some uu___2
                 else FStar_Pervasives_Native.None) in
      (match uu___ with
       | FStar_Pervasives_Native.None -> FStarC_TypeChecker_Common.Trivial
       | FStar_Pervasives_Native.Some g -> g)
  | uu___ -> FStarC_TypeChecker_Common.Trivial
let short_circuit_head (l : FStarC_Syntax_Syntax.term) : Prims.bool=
  let uu___ = FStarC_Syntax_Util.head_and_args_full l in
  match uu___ with
  | (hd, uu___1) ->
      let uu___2 =
        let uu___3 = FStarC_Syntax_Util.un_uinst hd in
        uu___3.FStarC_Syntax_Syntax.n in
      (match uu___2 with
       | FStarC_Syntax_Syntax.Tm_fvar fv ->
           FStarC_Util.for_some (FStarC_Syntax_Syntax.fv_eq_lid fv)
             [FStarC_Parser_Const.op_And;
             FStarC_Parser_Const.op_Or;
             FStarC_Parser_Const.and_lid;
             FStarC_Parser_Const.or_lid;
             FStarC_Parser_Const.imp_lid;
             FStarC_Parser_Const.ite_lid]
       | uu___3 -> false)
let maybe_add_implicit_binders (env : FStarC_TypeChecker_Env.env)
  (bs : FStarC_Syntax_Syntax.binders) : FStarC_Syntax_Syntax.binders=
  let is_implicit_binder b =
    let q = b.FStarC_Syntax_Syntax.binder_qual in
    match q with
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit uu___) ->
        true
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta uu___) -> true
    | uu___ -> false in
  let pos bs1 =
    match bs1 with
    | { FStarC_Syntax_Syntax.binder_bv = hd;
        FStarC_Syntax_Syntax.binder_qual = uu___;
        FStarC_Syntax_Syntax.binder_positivity = uu___1;
        FStarC_Syntax_Syntax.binder_attrs = uu___2;_}::uu___3 ->
        FStarC_Syntax_Syntax.range_of_bv hd
    | uu___ -> FStarC_TypeChecker_Env.get_range env in
  match bs with
  | b::uu___ when is_implicit_binder b -> bs
  | uu___ ->
      (match FStarC_TypeChecker_Env.expected_typ env with
       | FStar_Pervasives_Native.None -> bs
       | FStar_Pervasives_Native.Some (t, uu___1) ->
           let uu___2 = FStarC_Syntax_Util.arrow_formals_comp_ln_strict t in
           (match uu___2 with
            | (bs', uu___3) ->
                (match bs' with
                 | uu___4::uu___5 ->
                     let uu___6 =
                       FStarC_Util.prefix_until
                         (fun b ->
                            let uu___7 = is_implicit_binder b in
                            Prims.not uu___7) bs' in
                     (match uu___6 with
                      | FStar_Pervasives_Native.None -> bs
                      | FStar_Pervasives_Native.Some ([], uu___7, uu___8) ->
                          bs
                      | FStar_Pervasives_Native.Some (imps, uu___7, uu___8)
                          ->
                          let r = pos bs in
                          let imps1 =
                            FStarC_List.map
                              (fun b ->
                                 {
                                   FStarC_Syntax_Syntax.binder_bv =
                                     (FStarC_Syntax_Syntax.set_range_of_bv
                                        b.FStarC_Syntax_Syntax.binder_bv r);
                                   FStarC_Syntax_Syntax.binder_qual =
                                     (b.FStarC_Syntax_Syntax.binder_qual);
                                   FStarC_Syntax_Syntax.binder_positivity =
                                     (b.FStarC_Syntax_Syntax.binder_positivity);
                                   FStarC_Syntax_Syntax.binder_attrs =
                                     (b.FStarC_Syntax_Syntax.binder_attrs)
                                 }) imps in
                          FStarC_List.op_At imps1 bs)
                 | uu___4 -> bs)))
let must_erase_for_extraction (g : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) : Prims.bool=
  let res = FStarC_TypeChecker_Normalize.non_info_norm g t in
  (let uu___1 = FStarC_Effect.op_Bang dbg_Extraction in
   if uu___1
   then
     let uu___2 = FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t in
     FStarC_Format.print2 "must_erase=%s: %s\n"
       (if res then "true" else "false") uu___2
   else ());
  res
let effect_extraction_mode (env : FStarC_TypeChecker_Env.env)
  (l : FStarC_Ident.lident) : FStarC_Syntax_Syntax.eff_extraction_mode=
  let uu___ =
    let uu___1 = FStarC_TypeChecker_Env.norm_eff_name env l in
    FStarC_TypeChecker_Env.get_effect_decl env uu___1 in
  uu___.FStarC_Syntax_Syntax.extraction_mode
let fresh_effect_repr (env : FStarC_TypeChecker_Env.env)
  (r : FStarC_Range_Type.t) (eff_name : FStarC_Ident.lident)
  (signature_ts : FStarC_Syntax_Syntax.tscheme)
  (repr_ts_opt : FStarC_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  (u : FStarC_Syntax_Syntax.universe) (a_tm : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.guard_t)=
  FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
    FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
    (Obj.magic FStarC_Errors_Msg.is_error_message_string)
    (Obj.magic "Effects no longer have representations")
let fresh_effect_repr_en (env : FStarC_TypeChecker_Env.env)
  (r : FStarC_Range_Type.t) (eff_name : FStarC_Ident.lident)
  (u : FStarC_Syntax_Syntax.universe) (a_tm : FStarC_Syntax_Syntax.term) :
  (FStarC_Syntax_Syntax.term * FStarC_TypeChecker_Common.guard_t)=
  let ed =
    let uu___ = FStarC_TypeChecker_Env.norm_eff_name env eff_name in
    FStarC_TypeChecker_Env.get_effect_decl env uu___ in
  match FStarC_Syntax_Util.get_eff_repr ed with
  | FStar_Pervasives_Native.None ->
      FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range r
        FStarC_Errors_Codes.Fatal_UnexpectedEffect ()
        (Obj.magic FStarC_Errors_Msg.is_error_message_string)
        (Obj.magic
           (FStarC_Format.fmt1 "Effect %s does not have a representation"
              (FStarC_Ident.string_of_lid eff_name)))
  | FStar_Pervasives_Native.Some ts ->
      let repr = FStarC_TypeChecker_Env.inst_effect_fun_with [u] env ed ts in
      let uu___ =
        FStarC_Syntax_Syntax.mk_Tm_app repr
          [FStarC_Syntax_Syntax.as_arg a_tm] r in
      (uu___, FStarC_TypeChecker_Env.trivial_guard)
let layered_effect_indices_as_binders (env : FStarC_TypeChecker_Env.env)
  (r : FStarC_Range_Type.t) (eff_name : FStarC_Ident.lident)
  (sig_ts : FStarC_Syntax_Syntax.tscheme) (u : FStarC_Syntax_Syntax.universe)
  (a_tm : FStarC_Syntax_Syntax.term) : FStarC_Syntax_Syntax.binders= []
let get_field_projector_name (env : FStarC_TypeChecker_Env.env)
  (datacon : FStarC_Ident.lident) (index : Prims.int) : FStarC_Ident.lident=
  let uu___ = FStarC_TypeChecker_Env.lookup_datacon env datacon in
  match uu___ with
  | (uu___1, t) ->
      let err n =
        let uu___2 =
          let uu___3 =
            FStarC_Class_Show.show FStarC_Ident.showable_lident datacon in
          let uu___4 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int n in
          let uu___5 =
            FStarC_Class_Show.show FStarC_Class_Show.showable_int index in
          FStarC_Format.fmt3
            "Data constructor %s does not have enough binders (has %s, tried %s)"
            uu___3 uu___4 uu___5 in
        FStarC_Errors.raise_error FStarC_TypeChecker_Env.hasRange_env env
          FStarC_Errors_Codes.Fatal_UnexpectedDataConstructor ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_string)
          (Obj.magic uu___2) in
      let uu___2 = FStarC_Syntax_Util.arrow_formals_comp_ln_strict t in
      (match uu___2 with
       | (bs, uu___3) ->
           (match bs with
            | uu___4::uu___5 ->
                let bs1 =
                  FStarC_List.filter
                    (fun uu___6 ->
                       match uu___6 with
                       | { FStarC_Syntax_Syntax.binder_bv = uu___7;
                           FStarC_Syntax_Syntax.binder_qual = q;
                           FStarC_Syntax_Syntax.binder_positivity = uu___8;
                           FStarC_Syntax_Syntax.binder_attrs = uu___9;_} ->
                           (match q with
                            | FStar_Pervasives_Native.Some
                                (FStarC_Syntax_Syntax.Implicit true) -> false
                            | uu___10 -> true)) bs in
                if (FStarC_List.length bs1) <= index
                then err (FStarC_List.length bs1)
                else
                  (let b = FStarC_List.nth bs1 index in
                   FStarC_Syntax_Util.mk_field_projector_name datacon
                     b.FStarC_Syntax_Syntax.binder_bv index)
            | uu___4 -> err Prims.int_zero))
let update_env_sub_eff (env : FStarC_TypeChecker_Env.env)
  (sub : FStarC_Syntax_Syntax.sub_eff) (r : FStarC_Range_Type.t) :
  FStarC_TypeChecker_Env.env=
  let r0 = env.FStarC_TypeChecker_Env.range in
  let env1 =
    FStarC_TypeChecker_Env.update_effect_lattice
      {
        FStarC_TypeChecker_Env.solver = (env.FStarC_TypeChecker_Env.solver);
        FStarC_TypeChecker_Env.range = r;
        FStarC_TypeChecker_Env.curmodule =
          (env.FStarC_TypeChecker_Env.curmodule);
        FStarC_TypeChecker_Env.gamma = (env.FStarC_TypeChecker_Env.gamma);
        FStarC_TypeChecker_Env.gamma_sig =
          (env.FStarC_TypeChecker_Env.gamma_sig);
        FStarC_TypeChecker_Env.gamma_cache =
          (env.FStarC_TypeChecker_Env.gamma_cache);
        FStarC_TypeChecker_Env.modules = (env.FStarC_TypeChecker_Env.modules);
        FStarC_TypeChecker_Env.expected_typ =
          (env.FStarC_TypeChecker_Env.expected_typ);
        FStarC_TypeChecker_Env.sigtab = (env.FStarC_TypeChecker_Env.sigtab);
        FStarC_TypeChecker_Env.attrtab = (env.FStarC_TypeChecker_Env.attrtab);
        FStarC_TypeChecker_Env.instantiate_imp =
          (env.FStarC_TypeChecker_Env.instantiate_imp);
        FStarC_TypeChecker_Env.effects = (env.FStarC_TypeChecker_Env.effects);
        FStarC_TypeChecker_Env.generalize =
          (env.FStarC_TypeChecker_Env.generalize);
        FStarC_TypeChecker_Env.letrecs = (env.FStarC_TypeChecker_Env.letrecs);
        FStarC_TypeChecker_Env.top_level =
          (env.FStarC_TypeChecker_Env.top_level);
        FStarC_TypeChecker_Env.check_uvars =
          (env.FStarC_TypeChecker_Env.check_uvars);
        FStarC_TypeChecker_Env.use_eq_strict =
          (env.FStarC_TypeChecker_Env.use_eq_strict);
        FStarC_TypeChecker_Env.is_iface =
          (env.FStarC_TypeChecker_Env.is_iface);
        FStarC_TypeChecker_Env.admit = (env.FStarC_TypeChecker_Env.admit);
        FStarC_TypeChecker_Env.phase1 = (env.FStarC_TypeChecker_Env.phase1);
        FStarC_TypeChecker_Env.failhard =
          (env.FStarC_TypeChecker_Env.failhard);
        FStarC_TypeChecker_Env.flychecking =
          (env.FStarC_TypeChecker_Env.flychecking);
        FStarC_TypeChecker_Env.uvar_subtyping =
          (env.FStarC_TypeChecker_Env.uvar_subtyping);
        FStarC_TypeChecker_Env.intactics =
          (env.FStarC_TypeChecker_Env.intactics);
        FStarC_TypeChecker_Env.nocoerce =
          (env.FStarC_TypeChecker_Env.nocoerce);
        FStarC_TypeChecker_Env.tc_term = (env.FStarC_TypeChecker_Env.tc_term);
        FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
          (env.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
        FStarC_TypeChecker_Env.universe_of =
          (env.FStarC_TypeChecker_Env.universe_of);
        FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
          (env.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
        FStarC_TypeChecker_Env.teq_nosmt_force =
          (env.FStarC_TypeChecker_Env.teq_nosmt_force);
        FStarC_TypeChecker_Env.subtype_nosmt_force =
          (env.FStarC_TypeChecker_Env.subtype_nosmt_force);
        FStarC_TypeChecker_Env.qtbl_name_and_index =
          (env.FStarC_TypeChecker_Env.qtbl_name_and_index);
        FStarC_TypeChecker_Env.normalized_eff_names =
          (env.FStarC_TypeChecker_Env.normalized_eff_names);
        FStarC_TypeChecker_Env.fv_delta_depths =
          (env.FStarC_TypeChecker_Env.fv_delta_depths);
        FStarC_TypeChecker_Env.proof_ns =
          (env.FStarC_TypeChecker_Env.proof_ns);
        FStarC_TypeChecker_Env.synth_hook =
          (env.FStarC_TypeChecker_Env.synth_hook);
        FStarC_TypeChecker_Env.try_solve_implicits_hook =
          (env.FStarC_TypeChecker_Env.try_solve_implicits_hook);
        FStarC_TypeChecker_Env.splice = (env.FStarC_TypeChecker_Env.splice);
        FStarC_TypeChecker_Env.mpreprocess =
          (env.FStarC_TypeChecker_Env.mpreprocess);
        FStarC_TypeChecker_Env.postprocess =
          (env.FStarC_TypeChecker_Env.postprocess);
        FStarC_TypeChecker_Env.identifier_info =
          (env.FStarC_TypeChecker_Env.identifier_info);
        FStarC_TypeChecker_Env.tc_hooks =
          (env.FStarC_TypeChecker_Env.tc_hooks);
        FStarC_TypeChecker_Env.dsenv = (env.FStarC_TypeChecker_Env.dsenv);
        FStarC_TypeChecker_Env.nbe = (env.FStarC_TypeChecker_Env.nbe);
        FStarC_TypeChecker_Env.strict_args_tab =
          (env.FStarC_TypeChecker_Env.strict_args_tab);
        FStarC_TypeChecker_Env.erasable_types_tab =
          (env.FStarC_TypeChecker_Env.erasable_types_tab);
        FStarC_TypeChecker_Env.enable_defer_to_tac =
          (env.FStarC_TypeChecker_Env.enable_defer_to_tac);
        FStarC_TypeChecker_Env.unif_allow_ref_guards =
          (env.FStarC_TypeChecker_Env.unif_allow_ref_guards);
        FStarC_TypeChecker_Env.erase_erasable_args =
          (env.FStarC_TypeChecker_Env.erase_erasable_args);
        FStarC_TypeChecker_Env.core_check =
          (env.FStarC_TypeChecker_Env.core_check);
        FStarC_TypeChecker_Env.missing_decl =
          (env.FStarC_TypeChecker_Env.missing_decl);
        FStarC_TypeChecker_Env.iface_todo =
          (env.FStarC_TypeChecker_Env.iface_todo);
        FStarC_TypeChecker_Env.iface_hidden =
          (env.FStarC_TypeChecker_Env.iface_hidden);
        FStarC_TypeChecker_Env.iface_lids =
          (env.FStarC_TypeChecker_Env.iface_lids);
        FStarC_TypeChecker_Env.iface_val_lids =
          (env.FStarC_TypeChecker_Env.iface_val_lids)
      } sub.FStarC_Syntax_Syntax.source sub.FStarC_Syntax_Syntax.target in
  let env2 =
    match sub.FStarC_Syntax_Syntax.lift with
    | FStar_Pervasives_Native.None -> env1
    | FStar_Pervasives_Native.Some ts ->
        FStarC_TypeChecker_Env.add_lift env1 sub.FStarC_Syntax_Syntax.source
          sub.FStarC_Syntax_Syntax.target ts in
  {
    FStarC_TypeChecker_Env.solver = (env2.FStarC_TypeChecker_Env.solver);
    FStarC_TypeChecker_Env.range = r0;
    FStarC_TypeChecker_Env.curmodule =
      (env2.FStarC_TypeChecker_Env.curmodule);
    FStarC_TypeChecker_Env.gamma = (env2.FStarC_TypeChecker_Env.gamma);
    FStarC_TypeChecker_Env.gamma_sig =
      (env2.FStarC_TypeChecker_Env.gamma_sig);
    FStarC_TypeChecker_Env.gamma_cache =
      (env2.FStarC_TypeChecker_Env.gamma_cache);
    FStarC_TypeChecker_Env.modules = (env2.FStarC_TypeChecker_Env.modules);
    FStarC_TypeChecker_Env.expected_typ =
      (env2.FStarC_TypeChecker_Env.expected_typ);
    FStarC_TypeChecker_Env.sigtab = (env2.FStarC_TypeChecker_Env.sigtab);
    FStarC_TypeChecker_Env.attrtab = (env2.FStarC_TypeChecker_Env.attrtab);
    FStarC_TypeChecker_Env.instantiate_imp =
      (env2.FStarC_TypeChecker_Env.instantiate_imp);
    FStarC_TypeChecker_Env.effects = (env2.FStarC_TypeChecker_Env.effects);
    FStarC_TypeChecker_Env.generalize =
      (env2.FStarC_TypeChecker_Env.generalize);
    FStarC_TypeChecker_Env.letrecs = (env2.FStarC_TypeChecker_Env.letrecs);
    FStarC_TypeChecker_Env.top_level =
      (env2.FStarC_TypeChecker_Env.top_level);
    FStarC_TypeChecker_Env.check_uvars =
      (env2.FStarC_TypeChecker_Env.check_uvars);
    FStarC_TypeChecker_Env.use_eq_strict =
      (env2.FStarC_TypeChecker_Env.use_eq_strict);
    FStarC_TypeChecker_Env.is_iface = (env2.FStarC_TypeChecker_Env.is_iface);
    FStarC_TypeChecker_Env.admit = (env2.FStarC_TypeChecker_Env.admit);
    FStarC_TypeChecker_Env.phase1 = (env2.FStarC_TypeChecker_Env.phase1);
    FStarC_TypeChecker_Env.failhard = (env2.FStarC_TypeChecker_Env.failhard);
    FStarC_TypeChecker_Env.flychecking =
      (env2.FStarC_TypeChecker_Env.flychecking);
    FStarC_TypeChecker_Env.uvar_subtyping =
      (env2.FStarC_TypeChecker_Env.uvar_subtyping);
    FStarC_TypeChecker_Env.intactics =
      (env2.FStarC_TypeChecker_Env.intactics);
    FStarC_TypeChecker_Env.nocoerce = (env2.FStarC_TypeChecker_Env.nocoerce);
    FStarC_TypeChecker_Env.tc_term = (env2.FStarC_TypeChecker_Env.tc_term);
    FStarC_TypeChecker_Env.typeof_tot_or_gtot_term =
      (env2.FStarC_TypeChecker_Env.typeof_tot_or_gtot_term);
    FStarC_TypeChecker_Env.universe_of =
      (env2.FStarC_TypeChecker_Env.universe_of);
    FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
      (env2.FStarC_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
    FStarC_TypeChecker_Env.teq_nosmt_force =
      (env2.FStarC_TypeChecker_Env.teq_nosmt_force);
    FStarC_TypeChecker_Env.subtype_nosmt_force =
      (env2.FStarC_TypeChecker_Env.subtype_nosmt_force);
    FStarC_TypeChecker_Env.qtbl_name_and_index =
      (env2.FStarC_TypeChecker_Env.qtbl_name_and_index);
    FStarC_TypeChecker_Env.normalized_eff_names =
      (env2.FStarC_TypeChecker_Env.normalized_eff_names);
    FStarC_TypeChecker_Env.fv_delta_depths =
      (env2.FStarC_TypeChecker_Env.fv_delta_depths);
    FStarC_TypeChecker_Env.proof_ns = (env2.FStarC_TypeChecker_Env.proof_ns);
    FStarC_TypeChecker_Env.synth_hook =
      (env2.FStarC_TypeChecker_Env.synth_hook);
    FStarC_TypeChecker_Env.try_solve_implicits_hook =
      (env2.FStarC_TypeChecker_Env.try_solve_implicits_hook);
    FStarC_TypeChecker_Env.splice = (env2.FStarC_TypeChecker_Env.splice);
    FStarC_TypeChecker_Env.mpreprocess =
      (env2.FStarC_TypeChecker_Env.mpreprocess);
    FStarC_TypeChecker_Env.postprocess =
      (env2.FStarC_TypeChecker_Env.postprocess);
    FStarC_TypeChecker_Env.identifier_info =
      (env2.FStarC_TypeChecker_Env.identifier_info);
    FStarC_TypeChecker_Env.tc_hooks = (env2.FStarC_TypeChecker_Env.tc_hooks);
    FStarC_TypeChecker_Env.dsenv = (env2.FStarC_TypeChecker_Env.dsenv);
    FStarC_TypeChecker_Env.nbe = (env2.FStarC_TypeChecker_Env.nbe);
    FStarC_TypeChecker_Env.strict_args_tab =
      (env2.FStarC_TypeChecker_Env.strict_args_tab);
    FStarC_TypeChecker_Env.erasable_types_tab =
      (env2.FStarC_TypeChecker_Env.erasable_types_tab);
    FStarC_TypeChecker_Env.enable_defer_to_tac =
      (env2.FStarC_TypeChecker_Env.enable_defer_to_tac);
    FStarC_TypeChecker_Env.unif_allow_ref_guards =
      (env2.FStarC_TypeChecker_Env.unif_allow_ref_guards);
    FStarC_TypeChecker_Env.erase_erasable_args =
      (env2.FStarC_TypeChecker_Env.erase_erasable_args);
    FStarC_TypeChecker_Env.core_check =
      (env2.FStarC_TypeChecker_Env.core_check);
    FStarC_TypeChecker_Env.missing_decl =
      (env2.FStarC_TypeChecker_Env.missing_decl);
    FStarC_TypeChecker_Env.iface_todo =
      (env2.FStarC_TypeChecker_Env.iface_todo);
    FStarC_TypeChecker_Env.iface_hidden =
      (env2.FStarC_TypeChecker_Env.iface_hidden);
    FStarC_TypeChecker_Env.iface_lids =
      (env2.FStarC_TypeChecker_Env.iface_lids);
    FStarC_TypeChecker_Env.iface_val_lids =
      (env2.FStarC_TypeChecker_Env.iface_val_lids)
  }
let try_lookup_record_type (env : FStarC_TypeChecker_Env.env)
  (typename : FStarC_Ident.lident) :
  FStarC_Syntax_DsEnv.record_or_dc FStar_Pervasives_Native.option=
  try
    (fun uu___ ->
       match () with
       | () ->
           let uu___1 = FStarC_TypeChecker_Env.datacons_of_typ env typename in
           (match uu___1 with
            | (uu___2, dc::[]) ->
                let se = FStarC_TypeChecker_Env.lookup_sigelt env dc in
                (match se with
                 | FStar_Pervasives_Native.Some
                     {
                       FStarC_Syntax_Syntax.sigel =
                         FStarC_Syntax_Syntax.Sig_datacon
                         { FStarC_Syntax_Syntax.lid1 = uu___3;
                           FStarC_Syntax_Syntax.us1 = uu___4;
                           FStarC_Syntax_Syntax.t1 = t;
                           FStarC_Syntax_Syntax.ty_lid = uu___5;
                           FStarC_Syntax_Syntax.num_ty_params = nparms;
                           FStarC_Syntax_Syntax.mutuals1 = uu___6;
                           FStarC_Syntax_Syntax.injective_type_params1 =
                             uu___7;
                           FStarC_Syntax_Syntax.proj_disc_lids = uu___8;_};
                       FStarC_Syntax_Syntax.sigrng = uu___9;
                       FStarC_Syntax_Syntax.sigquals = uu___10;
                       FStarC_Syntax_Syntax.sigmeta = uu___11;
                       FStarC_Syntax_Syntax.sigattrs = uu___12;
                       FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___13;
                       FStarC_Syntax_Syntax.sigopts = uu___14;_}
                     ->
                     let uu___15 = FStarC_Syntax_Util.arrow_formals t in
                     (match uu___15 with
                      | (formals, c) ->
                          if nparms < (FStarC_List.length formals)
                          then
                            let uu___16 = FStarC_List.splitAt nparms formals in
                            (match uu___16 with
                             | (parms, fields) ->
                                 let fields1 =
                                   FStarC_List.map
                                     (fun b ->
                                        (((b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.ppname),
                                          (FStarC_Syntax_Syntax.is_bqual_implicit_or_meta
                                             b.FStarC_Syntax_Syntax.binder_qual),
                                          ((b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)))
                                     fields in
                                 let is_rec =
                                   FStarC_TypeChecker_Env.is_record env
                                     typename in
                                 let r =
                                   {
                                     FStarC_Syntax_DsEnv.typename = typename;
                                     FStarC_Syntax_DsEnv.constrname =
                                       (FStarC_Ident.ident_of_lid dc);
                                     FStarC_Syntax_DsEnv.parms = parms;
                                     FStarC_Syntax_DsEnv.fields = fields1;
                                     FStarC_Syntax_DsEnv.is_private = false;
                                     FStarC_Syntax_DsEnv.is_record = is_rec
                                   } in
                                 FStar_Pervasives_Native.Some r)
                          else FStar_Pervasives_Native.None)
                 | uu___3 -> FStar_Pervasives_Native.None)
            | (uu___2, dcs) -> FStar_Pervasives_Native.None)) ()
  with | uu___ -> FStar_Pervasives_Native.None
let head_fv_of_typ (env : FStarC_TypeChecker_Env.env)
  (t : FStarC_Syntax_Syntax.typ) :
  FStarC_Syntax_Syntax.fv FStar_Pervasives_Native.option=
  FStarC_TypeChecker_Overload.base_head_fv env t
let find_record_or_dc_from_head_fv (env : FStarC_TypeChecker_Env.env)
  (head_fv : FStarC_Syntax_Syntax.fv FStar_Pervasives_Native.option)
  (uc : FStarC_Syntax_Syntax.unresolved_constructor)
  (rng : FStarC_Range_Type.t) :
  (FStarC_Syntax_DsEnv.record_or_dc * FStarC_Ident.lident *
    FStarC_Syntax_Syntax.fv)=
  let default_rdc uu___ =
    match ((uc.FStarC_Syntax_Syntax.uc_typename),
            (uc.FStarC_Syntax_Syntax.uc_fields))
    with
    | (FStar_Pervasives_Native.None, []) ->
        FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range rng
          FStarC_Errors_Codes.Error_CannotResolveRecord ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic
             [FStarC_Errors_Msg.text
                "Could not resolve the type for this record."])
    | (FStar_Pervasives_Native.None, f::uu___1) ->
        let f1 = FStarC_List.hd uc.FStarC_Syntax_Syntax.uc_fields in
        FStarC_Errors.raise_error FStarC_Ident.hasrange_lident f1
          FStarC_Errors_Codes.Error_CannotResolveRecord ()
          (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
          (Obj.magic
             [FStarC_Errors_Msg.text
                (FStarC_Format.fmt1 "Field name %s could not be resolved."
                   (FStarC_Ident.string_of_lid f1))])
    | (FStar_Pervasives_Native.Some tn, uu___1) ->
        let uu___2 = try_lookup_record_type env tn in
        (match uu___2 with
         | FStar_Pervasives_Native.Some rdc -> rdc
         | FStar_Pervasives_Native.None ->
             FStarC_Errors.raise_error FStarC_Ident.hasrange_lident tn
               FStarC_Errors_Codes.Fatal_NameNotFound ()
               (Obj.magic FStarC_Errors_Msg.is_error_message_string)
               (Obj.magic
                  (FStarC_Format.fmt1 "Record name %s not found."
                     (FStarC_Ident.string_of_lid tn)))) in
  let rdc =
    match head_fv with
    | FStar_Pervasives_Native.None -> default_rdc ()
    | FStar_Pervasives_Native.Some type_name ->
        let uu___ =
          try_lookup_record_type env type_name.FStarC_Syntax_Syntax.fv_name in
        (match uu___ with
         | FStar_Pervasives_Native.None -> default_rdc ()
         | FStar_Pervasives_Native.Some r -> r) in
  let constrname =
    let name =
      FStarC_Ident.lid_of_ids
        (FStarC_List.op_At
           (FStarC_Ident.ns_of_lid rdc.FStarC_Syntax_DsEnv.typename)
           [rdc.FStarC_Syntax_DsEnv.constrname]) in
    FStarC_Ident.set_lid_range name rng in
  let constructor =
    let qual =
      if rdc.FStarC_Syntax_DsEnv.is_record
      then
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_List.map
                (fun uu___3 -> match uu___3 with | (i, uu___4, uu___5) -> i)
                rdc.FStarC_Syntax_DsEnv.fields in
            ((rdc.FStarC_Syntax_DsEnv.typename), uu___2) in
          FStarC_Syntax_Syntax.Record_ctor uu___1 in
        FStar_Pervasives_Native.Some uu___
      else FStar_Pervasives_Native.None in
    FStarC_Syntax_Syntax.lid_as_fv constrname qual in
  (rdc, constrname, constructor)
let field_name_matches (field_name : FStarC_Ident.lident)
  (rdc : FStarC_Syntax_DsEnv.record_or_dc) (field : FStarC_Ident.ident) :
  Prims.bool=
  (FStarC_Ident.ident_equals field (FStarC_Ident.ident_of_lid field_name)) &&
    (if (FStarC_Ident.ns_of_lid field_name) <> []
     then
       (FStarC_Ident.nsstr field_name) =
         (FStarC_Ident.nsstr rdc.FStarC_Syntax_DsEnv.typename)
     else true)
let make_record_fields_in_order (env : FStarC_TypeChecker_Env.env)
  (uc : FStarC_Syntax_Syntax.unresolved_constructor)
  (topt :
    (FStarC_Syntax_Syntax.typ, FStarC_Syntax_Syntax.typ)
      FStar_Pervasives.either FStar_Pervasives_Native.option)
  (rdc : FStarC_Syntax_DsEnv.record_or_dc)
  (fas : (FStarC_Ident.lident * 'a) Prims.list)
  (not_found :
    FStarC_Ident.ident -> Prims.bool -> 'a FStar_Pervasives_Native.option)
  (rng : FStarC_Range_Type.t) : ('a * Prims.bool) Prims.list=
  let debug uu___ =
    let print_rdc rdc1 =
      let uu___1 =
        let uu___2 =
          FStarC_List.map
            (fun uu___3 ->
               match uu___3 with
               | (i, uu___4, uu___5) -> FStarC_Ident.string_of_id i)
            rdc1.FStarC_Syntax_DsEnv.fields in
        FStarC_String.concat "; " uu___2 in
      FStarC_Format.fmt3 "{typename=%s; constrname=%s; fields=[%s]}"
        (FStarC_Ident.string_of_lid rdc1.FStarC_Syntax_DsEnv.typename)
        (FStarC_Ident.string_of_id rdc1.FStarC_Syntax_DsEnv.constrname)
        uu___1 in
    let print_topt topt1 =
      let uu___1 =
        FStarC_Class_Show.show
          (FStarC_Class_Show.show_option
             (FStarC_Class_Show.show_either FStarC_Syntax_Print.showable_term
                FStarC_Syntax_Print.showable_term)) topt1 in
      let uu___2 = print_rdc rdc in
      FStarC_Format.fmt2 "topt=%s; rdc=%s" uu___1 uu___2 in
    let uu___1 =
      FStarC_Class_Show.show
        (FStarC_Class_Show.show_option FStarC_Ident.showable_lident)
        uc.FStarC_Syntax_Syntax.uc_typename in
    let uu___2 =
      FStarC_Class_Show.show
        (FStarC_Class_Show.show_list FStarC_Ident.showable_lident)
        uc.FStarC_Syntax_Syntax.uc_fields in
    let uu___3 = print_topt topt in
    let uu___4 = print_rdc rdc in
    let uu___5 =
      let uu___6 = FStarC_List.map FStar_Pervasives_Native.fst fas in
      FStarC_Class_Show.show
        (FStarC_Class_Show.show_list FStarC_Ident.showable_lident) uu___6 in
    FStarC_Format.print5
      "Resolved uc={typename=%s;fields=%s}\n\ttopt=%s\n\t{rdc = %s\n\tfield assignments=[%s]}\n"
      uu___1 uu___2 uu___3 uu___4 uu___5 in
  let uu___ =
    FStarC_List.fold_left
      (fun uu___1 uu___2 ->
         match (uu___1, uu___2) with
         | ((fields, as_rev, missing), (field_name, is_imp, uu___3)) ->
             let uu___4 =
               FStarC_List.partition
                 (fun uu___5 ->
                    match uu___5 with
                    | (fn, uu___6) -> field_name_matches fn rdc field_name)
                 fields in
             (match uu___4 with
              | (matching, rest) ->
                  (match matching with
                   | (uu___5, a1)::[] ->
                       (rest, ((a1, is_imp) :: as_rev), missing)
                   | [] ->
                       let uu___5 = not_found field_name is_imp in
                       (match uu___5 with
                        | FStar_Pervasives_Native.None ->
                            (rest, as_rev, (field_name :: missing))
                        | FStar_Pervasives_Native.Some a1 ->
                            (rest, ((a1, is_imp) :: as_rev), missing))
                   | x1::x2::uu___5 ->
                       FStarC_Errors.raise_error FStarC_Ident.hasrange_lident
                         (FStar_Pervasives_Native.fst x1)
                         FStarC_Errors_Codes.Fatal_MissingFieldInRecord ()
                         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
                         (Obj.magic
                            (FStarC_Format.fmt2
                               "Field \226\128\152%s\226\128\153 of record type \226\128\152%s\226\128\153 is given multiple assignments."
                               (FStarC_Ident.string_of_id field_name)
                               (FStarC_Ident.string_of_lid
                                  rdc.FStarC_Syntax_DsEnv.typename))))))
      (fas, [], []) rdc.FStarC_Syntax_DsEnv.fields in
  match uu___ with
  | (rest, as_rev, missing) ->
      let pp_missing uu___1 =
        FStarC_Pprint.separate_map
          (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
             (FStar_Pprint.break_ Prims.int_one))
          (fun f ->
             let uu___2 =
               let uu___3 =
                 FStarC_Class_Show.show FStarC_Ident.showable_ident f in
               FStar_Pprint.doc_of_string uu___3 in
             FStarC_Errors_Msg.fquotes uu___2) missing in
      ((match (rest, missing) with
        | ([], []) -> ()
        | ((f, uu___2)::uu___3, uu___4) ->
            let uu___5 =
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStarC_Class_Show.show FStarC_Ident.showable_lident f in
                  let uu___9 =
                    FStarC_Class_Show.show FStarC_Ident.showable_lident
                      rdc.FStarC_Syntax_DsEnv.typename in
                  FStarC_Format.fmt2
                    "No field \226\128\152%s\226\128\153 in record type \226\128\152%s\226\128\153."
                    uu___8 uu___9 in
                FStarC_Errors_Msg.text uu___7 in
              let uu___7 =
                let uu___8 =
                  if match missing with | hd::tl -> true | uu___9 -> false
                  then
                    let uu___9 = pp_missing () in
                    FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one
                      (FStarC_Errors_Msg.text "Missing fields:") uu___9
                  else FStar_Pprint.empty in
                [uu___8] in
              uu___6 :: uu___7 in
            FStarC_Errors.raise_error FStarC_Ident.hasrange_lident f
              FStarC_Errors_Codes.Fatal_MissingFieldInRecord ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___5)
        | ([], uu___2) ->
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      FStarC_Class_Show.show FStarC_Ident.showable_lident
                        rdc.FStarC_Syntax_DsEnv.typename in
                    FStarC_Format.fmt1
                      "Missing fields for record type \226\128\152%s\226\128\153:"
                      uu___7 in
                  FStarC_Errors_Msg.text uu___6 in
                let uu___6 = pp_missing () in
                FStar_Pprint.prefix (Prims.of_int 2) Prims.int_one uu___5
                  uu___6 in
              [uu___4] in
            FStarC_Errors.raise_error FStarC_Class_HasRange.hasRange_range
              rng FStarC_Errors_Codes.Fatal_MissingFieldInRecord ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_list_doc)
              (Obj.magic uu___3));
       FStarC_List.rev as_rev)
