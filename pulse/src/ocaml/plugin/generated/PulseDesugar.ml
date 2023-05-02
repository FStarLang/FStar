open Prims
type env_t =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  local_refs: FStar_Ident.ident Prims.list }
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee -> match projectee with | { tcenv; local_refs;_} -> tcenv
let (__proj__Mkenv_t__item__local_refs :
  env_t -> FStar_Ident.ident Prims.list) =
  fun projectee ->
    match projectee with | { tcenv; local_refs;_} -> local_refs
let (push_bv :
  env_t -> FStar_Ident.ident -> (env_t * FStar_Syntax_Syntax.bv)) =
  fun env ->
    fun x ->
      let uu___ =
        FStar_Syntax_DsEnv.push_bv (env.tcenv).FStar_TypeChecker_Env.dsenv x in
      match uu___ with
      | (dsenv, bv) ->
          let tcenv =
            let uu___1 = env.tcenv in
            {
              FStar_TypeChecker_Env.solver =
                (uu___1.FStar_TypeChecker_Env.solver);
              FStar_TypeChecker_Env.range =
                (uu___1.FStar_TypeChecker_Env.range);
              FStar_TypeChecker_Env.curmodule =
                (uu___1.FStar_TypeChecker_Env.curmodule);
              FStar_TypeChecker_Env.gamma =
                (uu___1.FStar_TypeChecker_Env.gamma);
              FStar_TypeChecker_Env.gamma_sig =
                (uu___1.FStar_TypeChecker_Env.gamma_sig);
              FStar_TypeChecker_Env.gamma_cache =
                (uu___1.FStar_TypeChecker_Env.gamma_cache);
              FStar_TypeChecker_Env.modules =
                (uu___1.FStar_TypeChecker_Env.modules);
              FStar_TypeChecker_Env.expected_typ =
                (uu___1.FStar_TypeChecker_Env.expected_typ);
              FStar_TypeChecker_Env.sigtab =
                (uu___1.FStar_TypeChecker_Env.sigtab);
              FStar_TypeChecker_Env.attrtab =
                (uu___1.FStar_TypeChecker_Env.attrtab);
              FStar_TypeChecker_Env.instantiate_imp =
                (uu___1.FStar_TypeChecker_Env.instantiate_imp);
              FStar_TypeChecker_Env.effects =
                (uu___1.FStar_TypeChecker_Env.effects);
              FStar_TypeChecker_Env.generalize =
                (uu___1.FStar_TypeChecker_Env.generalize);
              FStar_TypeChecker_Env.letrecs =
                (uu___1.FStar_TypeChecker_Env.letrecs);
              FStar_TypeChecker_Env.top_level =
                (uu___1.FStar_TypeChecker_Env.top_level);
              FStar_TypeChecker_Env.check_uvars =
                (uu___1.FStar_TypeChecker_Env.check_uvars);
              FStar_TypeChecker_Env.use_eq_strict =
                (uu___1.FStar_TypeChecker_Env.use_eq_strict);
              FStar_TypeChecker_Env.is_iface =
                (uu___1.FStar_TypeChecker_Env.is_iface);
              FStar_TypeChecker_Env.admit =
                (uu___1.FStar_TypeChecker_Env.admit);
              FStar_TypeChecker_Env.lax = (uu___1.FStar_TypeChecker_Env.lax);
              FStar_TypeChecker_Env.lax_universes =
                (uu___1.FStar_TypeChecker_Env.lax_universes);
              FStar_TypeChecker_Env.phase1 =
                (uu___1.FStar_TypeChecker_Env.phase1);
              FStar_TypeChecker_Env.failhard =
                (uu___1.FStar_TypeChecker_Env.failhard);
              FStar_TypeChecker_Env.nosynth =
                (uu___1.FStar_TypeChecker_Env.nosynth);
              FStar_TypeChecker_Env.uvar_subtyping =
                (uu___1.FStar_TypeChecker_Env.uvar_subtyping);
              FStar_TypeChecker_Env.tc_term =
                (uu___1.FStar_TypeChecker_Env.tc_term);
              FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                (uu___1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
              FStar_TypeChecker_Env.universe_of =
                (uu___1.FStar_TypeChecker_Env.universe_of);
              FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                (uu___1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
              FStar_TypeChecker_Env.teq_nosmt_force =
                (uu___1.FStar_TypeChecker_Env.teq_nosmt_force);
              FStar_TypeChecker_Env.subtype_nosmt_force =
                (uu___1.FStar_TypeChecker_Env.subtype_nosmt_force);
              FStar_TypeChecker_Env.qtbl_name_and_index =
                (uu___1.FStar_TypeChecker_Env.qtbl_name_and_index);
              FStar_TypeChecker_Env.normalized_eff_names =
                (uu___1.FStar_TypeChecker_Env.normalized_eff_names);
              FStar_TypeChecker_Env.fv_delta_depths =
                (uu___1.FStar_TypeChecker_Env.fv_delta_depths);
              FStar_TypeChecker_Env.proof_ns =
                (uu___1.FStar_TypeChecker_Env.proof_ns);
              FStar_TypeChecker_Env.synth_hook =
                (uu___1.FStar_TypeChecker_Env.synth_hook);
              FStar_TypeChecker_Env.try_solve_implicits_hook =
                (uu___1.FStar_TypeChecker_Env.try_solve_implicits_hook);
              FStar_TypeChecker_Env.splice =
                (uu___1.FStar_TypeChecker_Env.splice);
              FStar_TypeChecker_Env.mpreprocess =
                (uu___1.FStar_TypeChecker_Env.mpreprocess);
              FStar_TypeChecker_Env.postprocess =
                (uu___1.FStar_TypeChecker_Env.postprocess);
              FStar_TypeChecker_Env.identifier_info =
                (uu___1.FStar_TypeChecker_Env.identifier_info);
              FStar_TypeChecker_Env.tc_hooks =
                (uu___1.FStar_TypeChecker_Env.tc_hooks);
              FStar_TypeChecker_Env.dsenv = dsenv;
              FStar_TypeChecker_Env.nbe = (uu___1.FStar_TypeChecker_Env.nbe);
              FStar_TypeChecker_Env.strict_args_tab =
                (uu___1.FStar_TypeChecker_Env.strict_args_tab);
              FStar_TypeChecker_Env.erasable_types_tab =
                (uu___1.FStar_TypeChecker_Env.erasable_types_tab);
              FStar_TypeChecker_Env.enable_defer_to_tac =
                (uu___1.FStar_TypeChecker_Env.enable_defer_to_tac);
              FStar_TypeChecker_Env.unif_allow_ref_guards =
                (uu___1.FStar_TypeChecker_Env.unif_allow_ref_guards);
              FStar_TypeChecker_Env.erase_erasable_args =
                (uu___1.FStar_TypeChecker_Env.erase_erasable_args);
              FStar_TypeChecker_Env.core_check =
                (uu___1.FStar_TypeChecker_Env.core_check)
            } in
          let env1 = { tcenv; local_refs = (env.local_refs) } in (env1, bv)
let (r_ : FStar_Compiler_Range.range) = FStar_Compiler_Range.dummyRange
let (star_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Steel"; "Effect"; "Common"; "star"] r_
let (emp_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Steel"; "Effect"; "Common"; "emp"] r_
let (pure_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Steel"; "Effect"; "Common"; "pure"] r_
let (stt_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "stt"] r_
let (assign_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "write"] r_
let (stt_ghost_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "stt_ghost"] r_
let (stt_atomic_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Pulse"; "Steel"; "Wrapper"; "stt_atomic"] r_
let (stapp_assignment :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.st_term)
  =
  fun lhs ->
    fun rhs ->
      let head_fv =
        FStar_Syntax_Syntax.lid_as_fv assign_lid
          FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
      let head = FStar_Syntax_Syntax.fv_to_tm head_fv in
      let app =
        FStar_Syntax_Syntax.mk_Tm_app head
          [(lhs, FStar_Pervasives_Native.None)] lhs.FStar_Syntax_Syntax.pos in
      let uu___ = PulseSyntaxWrapper.tm_expr app in
      let uu___1 = PulseSyntaxWrapper.tm_expr rhs in
      PulseSyntaxWrapper.tm_st_app uu___ FStar_Pervasives_Native.None uu___1
let (resolve_name : env_t -> FStar_Ident.ident -> FStar_Syntax_Syntax.term) =
  fun env ->
    fun id ->
      let uu___ =
        FStar_Syntax_DsEnv.try_lookup_id
          (env.tcenv).FStar_TypeChecker_Env.dsenv id in
      match uu___ with
      | FStar_Pervasives_Native.None -> failwith "Name not found"
      | FStar_Pervasives_Native.Some t -> t
let (pulse_arrow_formals :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.binder Prims.list FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStar_Syntax_Util.arrow_formals_comp_ln t in
    match uu___ with
    | (formals, comp) ->
        let uu___1 = FStar_Syntax_Util.is_total_comp comp in
        if uu___1
        then
          let res = FStar_Syntax_Util.comp_result comp in
          let uu___2 = FStar_Syntax_Util.head_and_args_full res in
          (match uu___2 with
           | (head, uu___3) ->
               let uu___4 =
                 let uu___5 = FStar_Syntax_Subst.compress head in
                 uu___5.FStar_Syntax_Syntax.n in
               (match uu___4 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    let uu___5 =
                      FStar_Compiler_List.existsML
                        (FStar_Syntax_Syntax.fv_eq_lid fv)
                        [stt_lid; stt_ghost_lid; stt_atomic_lid] in
                    if uu___5
                    then FStar_Pervasives_Native.Some formals
                    else FStar_Pervasives_Native.None
                | FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu___5;
                       FStar_Syntax_Syntax.vars = uu___6;
                       FStar_Syntax_Syntax.hash_code = uu___7;_},
                     uu___8)
                    ->
                    let uu___9 =
                      FStar_Compiler_List.existsML
                        (FStar_Syntax_Syntax.fv_eq_lid fv)
                        [stt_lid; stt_ghost_lid; stt_atomic_lid] in
                    if uu___9
                    then FStar_Pervasives_Native.Some formals
                    else FStar_Pervasives_Native.None
                | uu___5 -> FStar_Pervasives_Native.None))
        else FStar_Pervasives_Native.None
let (stapp_or_return :
  env_t -> FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.st_term) =
  fun env ->
    fun s ->
      let ret s1 =
        let uu___ = PulseSyntaxWrapper.tm_expr s1 in
        PulseSyntaxWrapper.tm_return uu___ in
      let uu___ = FStar_Syntax_Util.head_and_args_full s in
      match uu___ with
      | (head, args) ->
          (match head.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu___1 =
                 FStar_TypeChecker_Env.try_lookup_lid env.tcenv
                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
               (match uu___1 with
                | FStar_Pervasives_Native.None -> ret s
                | FStar_Pervasives_Native.Some ((uu___2, t), uu___3) ->
                    let uu___4 = pulse_arrow_formals t in
                    (match uu___4 with
                     | FStar_Pervasives_Native.None -> ret s
                     | FStar_Pervasives_Native.Some formals ->
                         let is_binder_implicit b =
                           match b.FStar_Syntax_Syntax.binder_qual with
                           | FStar_Pervasives_Native.Some
                               (FStar_Syntax_Syntax.Implicit uu___5) -> true
                           | uu___5 -> false in
                         let is_arg_implicit aq =
                           match FStar_Pervasives_Native.snd aq with
                           | FStar_Pervasives_Native.Some
                               { FStar_Syntax_Syntax.aqual_implicit = b;
                                 FStar_Syntax_Syntax.aqual_attributes =
                                   uu___5;_}
                               -> b
                           | uu___5 -> false in
                         let rec uninst_formals formals1 args1 =
                           match (formals1, args1) with
                           | (uu___5, []) ->
                               FStar_Pervasives_Native.Some formals1
                           | ([], uu___5) -> FStar_Pervasives_Native.None
                           | (f::formals2, a::args2) ->
                               if is_binder_implicit f
                               then
                                 (if is_arg_implicit a
                                  then uninst_formals formals2 args2
                                  else uninst_formals formals2 (a :: args2))
                               else
                                 if is_arg_implicit a
                                 then FStar_Pervasives_Native.None
                                 else uninst_formals formals2 args2 in
                         let uu___5 = uninst_formals formals args in
                         (match uu___5 with
                          | FStar_Pervasives_Native.None -> ret s
                          | FStar_Pervasives_Native.Some formals1 ->
                              let uu___6 =
                                FStar_Compiler_List.for_all
                                  is_binder_implicit formals1 in
                              if uu___6
                              then
                                let head1 =
                                  let uu___7 = FStar_Compiler_List.init args in
                                  FStar_Syntax_Syntax.mk_Tm_app head uu___7
                                    s.FStar_Syntax_Syntax.pos in
                                let uu___7 = FStar_Compiler_List.last args in
                                (match uu___7 with
                                 | (last, q) ->
                                     let uu___8 =
                                       PulseSyntaxWrapper.tm_expr head1 in
                                     let uu___9 =
                                       PulseSyntaxWrapper.tm_expr last in
                                     PulseSyntaxWrapper.tm_st_app uu___8 q
                                       uu___9)
                              else ret s)))
           | uu___1 -> ret s)
let (tosyntax : env_t -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term) =
  fun env ->
    fun t ->
      FStar_ToSyntax_ToSyntax.desugar_term
        (env.tcenv).FStar_TypeChecker_Env.dsenv t
let (desugar_term :
  env_t -> FStar_Parser_AST.term -> PulseSyntaxWrapper.term) =
  fun env ->
    fun t -> let uu___ = tosyntax env t in PulseSyntaxWrapper.tm_expr uu___
let (desugar_term_opt :
  env_t ->
    FStar_Parser_AST.term FStar_Pervasives_Native.option ->
      PulseSyntaxWrapper.term)
  =
  fun env ->
    fun t ->
      match t with
      | FStar_Pervasives_Native.None -> PulseSyntaxWrapper.tm_unknown
      | FStar_Pervasives_Native.Some e -> desugar_term env e
let rec (interpret_vprop_constructors :
  env_t -> FStar_Syntax_Syntax.term -> PulseSyntaxWrapper.term) =
  fun env ->
    fun v ->
      let uu___ = FStar_Syntax_Util.head_and_args_full v in
      match uu___ with
      | (head, args) ->
          (match ((head.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___1)::(r, uu___2)::[])
               when FStar_Syntax_Syntax.fv_eq_lid fv star_lid ->
               let uu___3 = interpret_vprop_constructors env l in
               let uu___4 = interpret_vprop_constructors env r in
               PulseSyntaxWrapper.tm_star uu___3 uu___4
           | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___1)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv pure_lid ->
               let uu___2 = PulseSyntaxWrapper.tm_expr l in
               PulseSyntaxWrapper.tm_pure uu___2
           | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
               FStar_Syntax_Syntax.fv_eq_lid fv emp_lid ->
               PulseSyntaxWrapper.tm_emp
           | uu___1 -> PulseSyntaxWrapper.tm_expr v)
let rec (desugar_vprop :
  env_t -> PulseSugar.vprop -> PulseSyntaxWrapper.vprop) =
  fun env ->
    fun v ->
      match v with
      | PulseSugar.VPropTerm t ->
          let t1 = tosyntax env t in interpret_vprop_constructors env t1
      | PulseSugar.VPropExists
          { PulseSugar.binders = binders; PulseSugar.body = body;_} ->
          let rec aux env1 binders1 =
            match binders1 with
            | [] -> desugar_vprop env1 body
            | (uu___, i, t)::bs ->
                let t1 = desugar_term env1 t in
                let uu___1 = push_bv env1 i in
                (match uu___1 with
                 | (env2, bv) ->
                     let body1 =
                       let uu___2 = aux env2 bs in
                       PulseSyntaxWrapper.close_term uu___2
                         bv.FStar_Syntax_Syntax.index in
                     let b = PulseSyntaxWrapper.mk_binder i t1 in
                     PulseSyntaxWrapper.tm_exists b body1) in
          aux env binders
let rec (desugar_stmt :
  env_t -> PulseSugar.stmt -> PulseSyntaxWrapper.st_term) =
  fun env ->
    fun s ->
      match s.PulseSugar.s with
      | PulseSugar.Expr { PulseSugar.e = e;_} ->
          let tm = tosyntax env e in
          let uu___ = PulseSyntaxWrapper.tm_expr tm in
          PulseSyntaxWrapper.tm_return uu___
      | PulseSugar.Assignment
          { PulseSugar.id = id; PulseSugar.value = value;_} ->
          let lhs = resolve_name env id in
          let value1 = tosyntax env value in stapp_assignment lhs value1
      | PulseSugar.Sequence
          {
            PulseSugar.s1 =
              { PulseSugar.s = PulseSugar.LetBinding lb;
                PulseSugar.range1 = uu___;_};
            PulseSugar.s2 = s2;_}
          -> desugar_bind env lb s2
      | PulseSugar.Sequence { PulseSugar.s1 = s1; PulseSugar.s2 = s2;_} ->
          desugar_sequence env s1 s2
      | PulseSugar.Block { PulseSugar.stmt = stmt;_} -> desugar_stmt env stmt
      | PulseSugar.If
          { PulseSugar.head1 = head; PulseSugar.join_vprop = join_vprop;
            PulseSugar.then_ = then_; PulseSugar.else_opt = else_opt;_}
          ->
          let head1 = desugar_term env head in
          let join_vprop1 =
            match join_vprop with
            | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
            | FStar_Pervasives_Native.Some t ->
                let uu___ = desugar_vprop env t in
                FStar_Pervasives_Native.Some uu___ in
          let then_1 = desugar_stmt env then_ in
          let else_ =
            match else_opt with
            | FStar_Pervasives_Native.None ->
                let uu___ =
                  PulseSyntaxWrapper.tm_expr FStar_Syntax_Syntax.unit_const in
                PulseSyntaxWrapper.tm_return uu___ in
          PulseSyntaxWrapper.tm_if head1 join_vprop1 then_1 else_
      | PulseSugar.Match
          { PulseSugar.head2 = head;
            PulseSugar.returns_annot = returns_annot;
            PulseSugar.branches = branches;_}
          -> failwith "Match is not yet handled"
      | PulseSugar.While
          { PulseSugar.head3 = head; PulseSugar.id2 = id;
            PulseSugar.invariant = invariant; PulseSugar.body1 = body;_}
          ->
          let head1 =
            let uu___ = tosyntax env head in stapp_or_return env uu___ in
          let invariant1 =
            let uu___ = push_bv env id in
            match uu___ with
            | (env1, bv) ->
                let uu___1 = desugar_vprop env1 invariant in
                PulseSyntaxWrapper.close_term uu___1
                  bv.FStar_Syntax_Syntax.index in
          let body1 = desugar_stmt env body in
          PulseSyntaxWrapper.tm_while head1 (id, invariant1) body1
      | PulseSugar.LetBinding uu___ -> failwith "Terminal let binding"
and (desugar_bind :
  env_t ->
    PulseSugar.stmt'__LetBinding__payload ->
      PulseSugar.stmt -> PulseSyntaxWrapper.st_term)
  =
  fun env ->
    fun lb ->
      fun s2 ->
        let annot = desugar_term_opt env lb.PulseSugar.typ in
        let s21 =
          let uu___ = push_bv env lb.PulseSugar.id1 in
          match uu___ with
          | (env1, bv) ->
              let uu___1 = desugar_stmt env1 s2 in
              PulseSyntaxWrapper.close_st_term uu___1
                bv.FStar_Syntax_Syntax.index in
        match lb.PulseSugar.init with
        | FStar_Pervasives_Native.None ->
            failwith "Uninitialized variables are not yet handled"
        | FStar_Pervasives_Native.Some e1 ->
            (match lb.PulseSugar.qualifier with
             | FStar_Pervasives_Native.None ->
                 let s1 =
                   let uu___ = tosyntax env e1 in stapp_or_return env uu___ in
                 PulseSyntaxWrapper.tm_bind
                   (FStar_Pervasives_Native.Some ((lb.PulseSugar.id1), annot))
                   s1 s21
             | FStar_Pervasives_Native.Some (PulseSugar.MUT) ->
                 let e11 = desugar_term env e1 in
                 PulseSyntaxWrapper.tm_let_mut lb.PulseSugar.id1 annot e11
                   s21
             | FStar_Pervasives_Native.Some (PulseSugar.REF) ->
                 let e11 = desugar_term env e1 in
                 PulseSyntaxWrapper.tm_let_mut lb.PulseSugar.id1 annot e11
                   s21)
and (desugar_sequence :
  env_t -> PulseSugar.stmt -> PulseSugar.stmt -> PulseSyntaxWrapper.st_term)
  =
  fun env ->
    fun s1 ->
      fun s2 ->
        let s11 = desugar_stmt env s1 in
        let s21 = desugar_stmt env s2 in
        PulseSyntaxWrapper.tm_bind FStar_Pervasives_Native.None s11 s21
let (explicit_rvalues : env_t -> PulseSugar.stmt -> PulseSugar.stmt) =
  fun env -> fun s -> s
type qual = PulseSyntaxWrapper.qualifier FStar_Pervasives_Native.option
let (as_qual : FStar_Parser_AST.aqual -> qual) =
  fun q ->
    match q with
    | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
        PulseSyntaxWrapper.as_qual true
    | uu___ -> PulseSyntaxWrapper.as_qual false
let (desugar_binders :
  env_t ->
    PulseSugar.binders ->
      (env_t * (PulseSyntaxWrapper.qualifier FStar_Pervasives_Native.option *
        PulseSyntaxWrapper.binder) Prims.list * FStar_Syntax_Syntax.bv
        Prims.list))
  =
  fun env ->
    fun bs ->
      let rec aux env1 bs1 =
        match bs1 with
        | [] -> (env1, [], [])
        | (aq, b, t)::bs2 ->
            let t1 = desugar_term env1 t in
            let uu___ = push_bv env1 b in
            (match uu___ with
             | (env2, bv) ->
                 let uu___1 = aux env2 bs2 in
                 (match uu___1 with
                  | (env3, bs3, bvs) ->
                      let bs4 =
                        FStar_Compiler_List.map
                          (fun uu___2 ->
                             match uu___2 with
                             | (aq1, x, t2) ->
                                 let uu___3 =
                                   PulseSyntaxWrapper.close_term t2
                                     bv.FStar_Syntax_Syntax.index in
                                 (aq1, x, uu___3)) bs3 in
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = as_qual aq in (uu___4, b, t1) in
                        uu___3 :: bs4 in
                      (env3, uu___2, (bv :: bvs)))) in
      let uu___ = aux env bs in
      match uu___ with
      | (env1, bs1, bvs) ->
          let uu___1 =
            FStar_Compiler_List.map
              (fun uu___2 ->
                 match uu___2 with
                 | (aq, b, t) ->
                     let uu___3 = PulseSyntaxWrapper.mk_binder b t in
                     (aq, uu___3)) bs1 in
          (env1, uu___1, bvs)
let (desugar_computation_type :
  env_t -> PulseSugar.computation_type -> PulseSyntaxWrapper.comp) =
  fun env ->
    fun c ->
      let pre = desugar_vprop env c.PulseSugar.precondition in
      let ret = desugar_term env c.PulseSugar.return_type in
      let uu___ = push_bv env c.PulseSugar.return_name in
      match uu___ with
      | (env1, bv) ->
          let post =
            let uu___1 = desugar_vprop env1 c.PulseSugar.postcondition in
            PulseSyntaxWrapper.close_term uu___1 bv.FStar_Syntax_Syntax.index in
          (match c.PulseSugar.tag with
           | PulseSugar.ST ->
               let uu___1 =
                 PulseSyntaxWrapper.mk_binder c.PulseSugar.return_name ret in
               PulseSyntaxWrapper.mk_comp pre uu___1 post
           | PulseSugar.STAtomic inames ->
               let inames1 = desugar_term env inames in
               let uu___1 =
                 PulseSyntaxWrapper.mk_binder c.PulseSugar.return_name ret in
               PulseSyntaxWrapper.atomic_comp inames1 pre uu___1 post
           | PulseSugar.STGhost inames ->
               let inames1 = desugar_term env inames in
               let uu___1 =
                 PulseSyntaxWrapper.mk_binder c.PulseSugar.return_name ret in
               PulseSyntaxWrapper.ghost_comp inames1 pre uu___1 post)
let (desugar_decl : env_t -> PulseSugar.decl -> PulseSyntaxWrapper.st_term) =
  fun env ->
    fun p ->
      let uu___ = desugar_binders env p.PulseSugar.binders1 in
      match uu___ with
      | (env1, bs, bvs) ->
          let body = desugar_stmt env1 p.PulseSugar.body2 in
          let body1 =
            FStar_Compiler_List.fold_right
              (fun bv ->
                 fun body2 ->
                   PulseSyntaxWrapper.close_st_term body2
                     bv.FStar_Syntax_Syntax.index) bvs body in
          let comp = desugar_computation_type env1 p.PulseSugar.ascription in
          PulseSyntaxWrapper.tm_abs bs comp body1
type name = Prims.string Prims.list
let (initialize_env :
  FStar_TypeChecker_Env.env ->
    name Prims.list -> (Prims.string * name) Prims.list -> env_t)
  =
  fun env ->
    fun open_namespaces ->
      fun module_abbrevs ->
        let dsenv = env.FStar_TypeChecker_Env.dsenv in
        let dsenv1 =
          FStar_Compiler_List.fold_left
            (fun env1 ->
               fun ns ->
                 let uu___ = FStar_Ident.lid_of_path ns r_ in
                 FStar_Syntax_DsEnv.push_namespace env1 uu___) dsenv
            open_namespaces in
        let dsenv2 =
          FStar_Compiler_List.fold_left
            (fun env1 ->
               fun uu___ ->
                 match uu___ with
                 | (m, n) ->
                     let uu___1 = FStar_Ident.id_of_text m in
                     let uu___2 = FStar_Ident.lid_of_path n r_ in
                     FStar_Syntax_DsEnv.push_module_abbrev env1 uu___1 uu___2)
            dsenv1 module_abbrevs in
        let env1 =
          {
            FStar_TypeChecker_Env.solver = (env.FStar_TypeChecker_Env.solver);
            FStar_TypeChecker_Env.range = (env.FStar_TypeChecker_Env.range);
            FStar_TypeChecker_Env.curmodule =
              (env.FStar_TypeChecker_Env.curmodule);
            FStar_TypeChecker_Env.gamma = (env.FStar_TypeChecker_Env.gamma);
            FStar_TypeChecker_Env.gamma_sig =
              (env.FStar_TypeChecker_Env.gamma_sig);
            FStar_TypeChecker_Env.gamma_cache =
              (env.FStar_TypeChecker_Env.gamma_cache);
            FStar_TypeChecker_Env.modules =
              (env.FStar_TypeChecker_Env.modules);
            FStar_TypeChecker_Env.expected_typ =
              (env.FStar_TypeChecker_Env.expected_typ);
            FStar_TypeChecker_Env.sigtab = (env.FStar_TypeChecker_Env.sigtab);
            FStar_TypeChecker_Env.attrtab =
              (env.FStar_TypeChecker_Env.attrtab);
            FStar_TypeChecker_Env.instantiate_imp =
              (env.FStar_TypeChecker_Env.instantiate_imp);
            FStar_TypeChecker_Env.effects =
              (env.FStar_TypeChecker_Env.effects);
            FStar_TypeChecker_Env.generalize =
              (env.FStar_TypeChecker_Env.generalize);
            FStar_TypeChecker_Env.letrecs =
              (env.FStar_TypeChecker_Env.letrecs);
            FStar_TypeChecker_Env.top_level =
              (env.FStar_TypeChecker_Env.top_level);
            FStar_TypeChecker_Env.check_uvars =
              (env.FStar_TypeChecker_Env.check_uvars);
            FStar_TypeChecker_Env.use_eq_strict =
              (env.FStar_TypeChecker_Env.use_eq_strict);
            FStar_TypeChecker_Env.is_iface =
              (env.FStar_TypeChecker_Env.is_iface);
            FStar_TypeChecker_Env.admit = (env.FStar_TypeChecker_Env.admit);
            FStar_TypeChecker_Env.lax = (env.FStar_TypeChecker_Env.lax);
            FStar_TypeChecker_Env.lax_universes =
              (env.FStar_TypeChecker_Env.lax_universes);
            FStar_TypeChecker_Env.phase1 = (env.FStar_TypeChecker_Env.phase1);
            FStar_TypeChecker_Env.failhard =
              (env.FStar_TypeChecker_Env.failhard);
            FStar_TypeChecker_Env.nosynth =
              (env.FStar_TypeChecker_Env.nosynth);
            FStar_TypeChecker_Env.uvar_subtyping =
              (env.FStar_TypeChecker_Env.uvar_subtyping);
            FStar_TypeChecker_Env.tc_term =
              (env.FStar_TypeChecker_Env.tc_term);
            FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
            FStar_TypeChecker_Env.universe_of =
              (env.FStar_TypeChecker_Env.universe_of);
            FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
              (env.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
            FStar_TypeChecker_Env.teq_nosmt_force =
              (env.FStar_TypeChecker_Env.teq_nosmt_force);
            FStar_TypeChecker_Env.subtype_nosmt_force =
              (env.FStar_TypeChecker_Env.subtype_nosmt_force);
            FStar_TypeChecker_Env.qtbl_name_and_index =
              (env.FStar_TypeChecker_Env.qtbl_name_and_index);
            FStar_TypeChecker_Env.normalized_eff_names =
              (env.FStar_TypeChecker_Env.normalized_eff_names);
            FStar_TypeChecker_Env.fv_delta_depths =
              (env.FStar_TypeChecker_Env.fv_delta_depths);
            FStar_TypeChecker_Env.proof_ns =
              (env.FStar_TypeChecker_Env.proof_ns);
            FStar_TypeChecker_Env.synth_hook =
              (env.FStar_TypeChecker_Env.synth_hook);
            FStar_TypeChecker_Env.try_solve_implicits_hook =
              (env.FStar_TypeChecker_Env.try_solve_implicits_hook);
            FStar_TypeChecker_Env.splice = (env.FStar_TypeChecker_Env.splice);
            FStar_TypeChecker_Env.mpreprocess =
              (env.FStar_TypeChecker_Env.mpreprocess);
            FStar_TypeChecker_Env.postprocess =
              (env.FStar_TypeChecker_Env.postprocess);
            FStar_TypeChecker_Env.identifier_info =
              (env.FStar_TypeChecker_Env.identifier_info);
            FStar_TypeChecker_Env.tc_hooks =
              (env.FStar_TypeChecker_Env.tc_hooks);
            FStar_TypeChecker_Env.dsenv = dsenv2;
            FStar_TypeChecker_Env.nbe = (env.FStar_TypeChecker_Env.nbe);
            FStar_TypeChecker_Env.strict_args_tab =
              (env.FStar_TypeChecker_Env.strict_args_tab);
            FStar_TypeChecker_Env.erasable_types_tab =
              (env.FStar_TypeChecker_Env.erasable_types_tab);
            FStar_TypeChecker_Env.enable_defer_to_tac =
              (env.FStar_TypeChecker_Env.enable_defer_to_tac);
            FStar_TypeChecker_Env.unif_allow_ref_guards =
              (env.FStar_TypeChecker_Env.unif_allow_ref_guards);
            FStar_TypeChecker_Env.erase_erasable_args =
              (env.FStar_TypeChecker_Env.erase_erasable_args);
            FStar_TypeChecker_Env.core_check =
              (env.FStar_TypeChecker_Env.core_check)
          } in
        { tcenv = env1; local_refs = [] }