open Prims
let (get_env : unit -> FStarC_TypeChecker_Env.env) =
  fun uu___ ->
    let uu___1 =
      FStarC_Compiler_Effect.op_Bang
        FStarC_TypeChecker_Normalize.reflection_env_hook in
    match uu___1 with
    | FStar_Pervasives_Native.None ->
        failwith "impossible: env_hook unset in reflection"
    | FStar_Pervasives_Native.Some e -> e
let (inspect_bqual :
  FStarC_Syntax_Syntax.bqual -> FStarC_Reflection_V1_Data.aqualv) =
  fun bq ->
    match bq with
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit uu___) ->
        FStarC_Reflection_V1_Data.Q_Implicit
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t) ->
        FStarC_Reflection_V1_Data.Q_Meta t
    | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Equality) ->
        FStarC_Reflection_V1_Data.Q_Explicit
    | FStar_Pervasives_Native.None -> FStarC_Reflection_V1_Data.Q_Explicit
let (inspect_aqual :
  FStarC_Syntax_Syntax.aqual -> FStarC_Reflection_V1_Data.aqualv) =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.Some
        { FStarC_Syntax_Syntax.aqual_implicit = true;
          FStarC_Syntax_Syntax.aqual_attributes = uu___;_}
        -> FStarC_Reflection_V1_Data.Q_Implicit
    | uu___ -> FStarC_Reflection_V1_Data.Q_Explicit
let (pack_bqual :
  FStarC_Reflection_V1_Data.aqualv -> FStarC_Syntax_Syntax.bqual) =
  fun aqv ->
    match aqv with
    | FStarC_Reflection_V1_Data.Q_Explicit -> FStar_Pervasives_Native.None
    | FStarC_Reflection_V1_Data.Q_Implicit ->
        FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Implicit false)
    | FStarC_Reflection_V1_Data.Q_Meta t ->
        FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.Meta t)
let (pack_aqual :
  FStarC_Reflection_V1_Data.aqualv -> FStarC_Syntax_Syntax.aqual) =
  fun aqv ->
    match aqv with
    | FStarC_Reflection_V1_Data.Q_Implicit ->
        FStarC_Syntax_Syntax.as_aqual_implicit true
    | uu___ -> FStar_Pervasives_Native.None
let (inspect_fv : FStarC_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv ->
    let uu___ = FStarC_Syntax_Syntax.lid_of_fv fv in
    FStarC_Ident.path_of_lid uu___
let (pack_fv : Prims.string Prims.list -> FStarC_Syntax_Syntax.fv) =
  fun ns ->
    let lid = FStarC_Parser_Const.p2l ns in
    let fallback uu___ =
      let quals =
        let uu___1 = FStarC_Ident.lid_equals lid FStarC_Parser_Const.cons_lid in
        if uu___1
        then FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor
        else
          (let uu___3 =
             FStarC_Ident.lid_equals lid FStarC_Parser_Const.nil_lid in
           if uu___3
           then FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor
           else
             (let uu___5 =
                FStarC_Ident.lid_equals lid FStarC_Parser_Const.some_lid in
              if uu___5
              then
                FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor
              else
                (let uu___7 =
                   FStarC_Ident.lid_equals lid FStarC_Parser_Const.none_lid in
                 if uu___7
                 then
                   FStar_Pervasives_Native.Some
                     FStarC_Syntax_Syntax.Data_ctor
                 else FStar_Pervasives_Native.None))) in
      let uu___1 = FStarC_Parser_Const.p2l ns in
      FStarC_Syntax_Syntax.lid_as_fv uu___1 quals in
    let uu___ =
      FStarC_Compiler_Effect.op_Bang
        FStarC_TypeChecker_Normalize.reflection_env_hook in
    match uu___ with
    | FStar_Pervasives_Native.None -> fallback ()
    | FStar_Pervasives_Native.Some env ->
        let qninfo = FStarC_TypeChecker_Env.lookup_qname env lid in
        (match qninfo with
         | FStar_Pervasives_Native.Some
             (FStar_Pervasives.Inr (se, _us), _rng) ->
             let quals = FStarC_Syntax_DsEnv.fv_qual_of_se se in
             let uu___1 = FStarC_Parser_Const.p2l ns in
             FStarC_Syntax_Syntax.lid_as_fv uu___1 quals
         | uu___1 -> fallback ())
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu___::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu___ = init xs in x :: uu___
let (inspect_const :
  FStarC_Syntax_Syntax.sconst -> FStarC_Reflection_V1_Data.vconst) =
  fun c ->
    match c with
    | FStarC_Const.Const_unit -> FStarC_Reflection_V1_Data.C_Unit
    | FStarC_Const.Const_int (s, uu___) ->
        let uu___1 = FStarC_BigInt.big_int_of_string s in
        FStarC_Reflection_V1_Data.C_Int uu___1
    | FStarC_Const.Const_bool (true) -> FStarC_Reflection_V1_Data.C_True
    | FStarC_Const.Const_bool (false) -> FStarC_Reflection_V1_Data.C_False
    | FStarC_Const.Const_string (s, uu___) ->
        FStarC_Reflection_V1_Data.C_String s
    | FStarC_Const.Const_range r -> FStarC_Reflection_V1_Data.C_Range r
    | FStarC_Const.Const_reify uu___ -> FStarC_Reflection_V1_Data.C_Reify
    | FStarC_Const.Const_reflect l ->
        let uu___ = FStarC_Ident.path_of_lid l in
        FStarC_Reflection_V1_Data.C_Reflect uu___
    | uu___ ->
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_const c in
          FStarC_Compiler_Util.format1 "unknown constant: %s" uu___2 in
        failwith uu___1
let (inspect_universe :
  FStarC_Syntax_Syntax.universe -> FStarC_Reflection_V1_Data.universe_view) =
  fun u ->
    match u with
    | FStarC_Syntax_Syntax.U_zero -> FStarC_Reflection_V1_Data.Uv_Zero
    | FStarC_Syntax_Syntax.U_succ u1 -> FStarC_Reflection_V1_Data.Uv_Succ u1
    | FStarC_Syntax_Syntax.U_max us -> FStarC_Reflection_V1_Data.Uv_Max us
    | FStarC_Syntax_Syntax.U_bvar n ->
        let uu___ = FStarC_BigInt.of_int_fs n in
        FStarC_Reflection_V1_Data.Uv_BVar uu___
    | FStarC_Syntax_Syntax.U_name i ->
        let uu___ =
          let uu___1 = FStarC_Ident.string_of_id i in
          let uu___2 = FStarC_Ident.range_of_id i in (uu___1, uu___2) in
        FStarC_Reflection_V1_Data.Uv_Name uu___
    | FStarC_Syntax_Syntax.U_unif u1 -> FStarC_Reflection_V1_Data.Uv_Unif u1
    | FStarC_Syntax_Syntax.U_unknown -> FStarC_Reflection_V1_Data.Uv_Unk
let (pack_universe :
  FStarC_Reflection_V1_Data.universe_view -> FStarC_Syntax_Syntax.universe) =
  fun uv ->
    match uv with
    | FStarC_Reflection_V1_Data.Uv_Zero -> FStarC_Syntax_Syntax.U_zero
    | FStarC_Reflection_V1_Data.Uv_Succ u -> FStarC_Syntax_Syntax.U_succ u
    | FStarC_Reflection_V1_Data.Uv_Max us -> FStarC_Syntax_Syntax.U_max us
    | FStarC_Reflection_V1_Data.Uv_BVar n ->
        let uu___ = FStarC_BigInt.to_int_fs n in
        FStarC_Syntax_Syntax.U_bvar uu___
    | FStarC_Reflection_V1_Data.Uv_Name i ->
        let uu___ = FStarC_Ident.mk_ident i in
        FStarC_Syntax_Syntax.U_name uu___
    | FStarC_Reflection_V1_Data.Uv_Unif u -> FStarC_Syntax_Syntax.U_unif u
    | FStarC_Reflection_V1_Data.Uv_Unk -> FStarC_Syntax_Syntax.U_unknown
let rec (inspect_ln :
  FStarC_Syntax_Syntax.term -> FStarC_Reflection_V1_Data.term_view) =
  fun t ->
    let t1 = FStarC_Syntax_Subst.compress_subst t in
    match t1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t2; FStarC_Syntax_Syntax.meta = uu___;_}
        -> inspect_ln t2
    | FStarC_Syntax_Syntax.Tm_name bv -> FStarC_Reflection_V1_Data.Tv_Var bv
    | FStarC_Syntax_Syntax.Tm_bvar bv -> FStarC_Reflection_V1_Data.Tv_BVar bv
    | FStarC_Syntax_Syntax.Tm_fvar fv -> FStarC_Reflection_V1_Data.Tv_FVar fv
    | FStarC_Syntax_Syntax.Tm_uinst (t2, us) ->
        (match t2.FStarC_Syntax_Syntax.n with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             FStarC_Reflection_V1_Data.Tv_UInst (fv, us)
         | uu___ ->
             failwith "Reflection::inspect_ln: uinst for a non-fvar node")
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t2;
          FStarC_Syntax_Syntax.asc = (FStar_Pervasives.Inl ty, tacopt, eq);
          FStarC_Syntax_Syntax.eff_opt = uu___;_}
        -> FStarC_Reflection_V1_Data.Tv_AscribedT (t2, ty, tacopt, eq)
    | FStarC_Syntax_Syntax.Tm_ascribed
        { FStarC_Syntax_Syntax.tm = t2;
          FStarC_Syntax_Syntax.asc = (FStar_Pervasives.Inr cty, tacopt, eq);
          FStarC_Syntax_Syntax.eff_opt = uu___;_}
        -> FStarC_Reflection_V1_Data.Tv_AscribedC (t2, cty, tacopt, eq)
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = uu___; FStarC_Syntax_Syntax.args = [];_}
        -> failwith "inspect_ln: empty arguments on Tm_app"
    | FStarC_Syntax_Syntax.Tm_app
        { FStarC_Syntax_Syntax.hd = hd; FStarC_Syntax_Syntax.args = args;_}
        ->
        let uu___ = last args in
        (match uu___ with
         | (a, q) ->
             let q' = inspect_aqual q in
             let uu___1 =
               let uu___2 =
                 let uu___3 = init args in
                 FStarC_Syntax_Util.mk_app hd uu___3 in
               (uu___2, (a, q')) in
             FStarC_Reflection_V1_Data.Tv_App uu___1)
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = []; FStarC_Syntax_Syntax.body = uu___;
          FStarC_Syntax_Syntax.rc_opt = uu___1;_}
        -> failwith "inspect_ln: empty arguments on Tm_abs"
    | FStarC_Syntax_Syntax.Tm_abs
        { FStarC_Syntax_Syntax.bs = b::bs; FStarC_Syntax_Syntax.body = t2;
          FStarC_Syntax_Syntax.rc_opt = k;_}
        ->
        let body =
          match bs with
          | [] -> t2
          | bs1 ->
              FStarC_Syntax_Syntax.mk
                (FStarC_Syntax_Syntax.Tm_abs
                   {
                     FStarC_Syntax_Syntax.bs = bs1;
                     FStarC_Syntax_Syntax.body = t2;
                     FStarC_Syntax_Syntax.rc_opt = k
                   }) t2.FStarC_Syntax_Syntax.pos in
        FStarC_Reflection_V1_Data.Tv_Abs (b, body)
    | FStarC_Syntax_Syntax.Tm_type u -> FStarC_Reflection_V1_Data.Tv_Type u
    | FStarC_Syntax_Syntax.Tm_arrow
        { FStarC_Syntax_Syntax.bs1 = []; FStarC_Syntax_Syntax.comp = uu___;_}
        -> failwith "inspect_ln: empty binders on arrow"
    | FStarC_Syntax_Syntax.Tm_arrow uu___ ->
        let uu___1 = FStarC_Syntax_Util.arrow_one_ln t1 in
        (match uu___1 with
         | FStar_Pervasives_Native.Some (b, c) ->
             FStarC_Reflection_V1_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None -> failwith "impossible")
    | FStarC_Syntax_Syntax.Tm_refine
        { FStarC_Syntax_Syntax.b = bv; FStarC_Syntax_Syntax.phi = t2;_} ->
        FStarC_Reflection_V1_Data.Tv_Refine
          (bv, (bv.FStarC_Syntax_Syntax.sort), t2)
    | FStarC_Syntax_Syntax.Tm_constant c ->
        let uu___ = inspect_const c in
        FStarC_Reflection_V1_Data.Tv_Const uu___
    | FStarC_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Syntax_Unionfind.uvar_unique_id
                ctx_u.FStarC_Syntax_Syntax.ctx_uvar_head in
            FStarC_BigInt.of_int_fs uu___2 in
          (uu___1, (ctx_u, s)) in
        FStarC_Reflection_V1_Data.Tv_Uvar uu___
    | FStarC_Syntax_Syntax.Tm_let
        { FStarC_Syntax_Syntax.lbs = (false, lb::[]);
          FStarC_Syntax_Syntax.body1 = t2;_}
        ->
        if lb.FStarC_Syntax_Syntax.lbunivs <> []
        then FStarC_Reflection_V1_Data.Tv_Unsupp
        else
          (match lb.FStarC_Syntax_Syntax.lbname with
           | FStar_Pervasives.Inr uu___1 ->
               FStarC_Reflection_V1_Data.Tv_Unsupp
           | FStar_Pervasives.Inl bv ->
               FStarC_Reflection_V1_Data.Tv_Let
                 (false, (lb.FStarC_Syntax_Syntax.lbattrs), bv,
                   (bv.FStarC_Syntax_Syntax.sort),
                   (lb.FStarC_Syntax_Syntax.lbdef), t2))
    | FStarC_Syntax_Syntax.Tm_let
        { FStarC_Syntax_Syntax.lbs = (true, lb::[]);
          FStarC_Syntax_Syntax.body1 = t2;_}
        ->
        if lb.FStarC_Syntax_Syntax.lbunivs <> []
        then FStarC_Reflection_V1_Data.Tv_Unsupp
        else
          (match lb.FStarC_Syntax_Syntax.lbname with
           | FStar_Pervasives.Inr uu___1 ->
               FStarC_Reflection_V1_Data.Tv_Unsupp
           | FStar_Pervasives.Inl bv ->
               FStarC_Reflection_V1_Data.Tv_Let
                 (true, (lb.FStarC_Syntax_Syntax.lbattrs), bv,
                   (bv.FStarC_Syntax_Syntax.sort),
                   (lb.FStarC_Syntax_Syntax.lbdef), t2))
    | FStarC_Syntax_Syntax.Tm_match
        { FStarC_Syntax_Syntax.scrutinee = t2;
          FStarC_Syntax_Syntax.ret_opt = ret_opt;
          FStarC_Syntax_Syntax.brs = brs;
          FStarC_Syntax_Syntax.rc_opt1 = uu___;_}
        ->
        let rec inspect_pat p =
          match p.FStarC_Syntax_Syntax.v with
          | FStarC_Syntax_Syntax.Pat_constant c ->
              let uu___1 = inspect_const c in
              FStarC_Reflection_V1_Data.Pat_Constant uu___1
          | FStarC_Syntax_Syntax.Pat_cons (fv, us_opt, ps) ->
              let uu___1 =
                let uu___2 =
                  FStarC_Compiler_List.map
                    (fun uu___3 ->
                       match uu___3 with
                       | (p1, b) ->
                           let uu___4 = inspect_pat p1 in (uu___4, b)) ps in
                (fv, us_opt, uu___2) in
              FStarC_Reflection_V1_Data.Pat_Cons uu___1
          | FStarC_Syntax_Syntax.Pat_var bv ->
              FStarC_Reflection_V1_Data.Pat_Var
                (bv,
                  (FStarC_Compiler_Sealed.seal bv.FStarC_Syntax_Syntax.sort))
          | FStarC_Syntax_Syntax.Pat_dot_term eopt ->
              FStarC_Reflection_V1_Data.Pat_Dot_Term eopt in
        let brs1 =
          FStarC_Compiler_List.map
            (fun uu___1 ->
               match uu___1 with
               | (pat, uu___2, t3) ->
                   let uu___3 = inspect_pat pat in (uu___3, t3)) brs in
        FStarC_Reflection_V1_Data.Tv_Match (t2, ret_opt, brs1)
    | FStarC_Syntax_Syntax.Tm_unknown -> FStarC_Reflection_V1_Data.Tv_Unknown
    | FStarC_Syntax_Syntax.Tm_lazy i ->
        let uu___ = FStarC_Syntax_Util.unfold_lazy i in inspect_ln uu___
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              FStarC_Class_Tagged.tag_of FStarC_Syntax_Syntax.tagged_term t1 in
            let uu___4 =
              FStarC_Class_Show.show FStarC_Syntax_Print.showable_term t1 in
            FStarC_Compiler_Util.format2
              "inspect_ln: outside of expected syntax (%s, %s)" uu___3 uu___4 in
          FStarC_Errors.log_issue (FStarC_Syntax_Syntax.has_range_syntax ())
            t1 FStarC_Errors_Codes.Warning_CantInspect ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStarC_Reflection_V1_Data.Tv_Unsupp)
let (inspect_comp :
  FStarC_Syntax_Syntax.comp -> FStarC_Reflection_V1_Data.comp_view) =
  fun c ->
    let get_dec flags =
      let uu___ =
        FStarC_Compiler_List.tryFind
          (fun uu___1 ->
             match uu___1 with
             | FStarC_Syntax_Syntax.DECREASES uu___2 -> true
             | uu___2 -> false) flags in
      match uu___ with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.DECREASES
          (FStarC_Syntax_Syntax.Decreases_lex ts)) -> ts
      | FStar_Pervasives_Native.Some (FStarC_Syntax_Syntax.DECREASES
          (FStarC_Syntax_Syntax.Decreases_wf uu___1)) ->
          ((let uu___3 =
              let uu___4 =
                FStarC_Class_Show.show FStarC_Syntax_Print.showable_comp c in
              FStarC_Compiler_Util.format1
                "inspect_comp: inspecting comp with wf decreases clause is not yet supported: %s skipping the decreases clause"
                uu___4 in
            FStarC_Errors.log_issue
              (FStarC_Syntax_Syntax.has_range_syntax ()) c
              FStarC_Errors_Codes.Warning_CantInspect ()
              (Obj.magic FStarC_Errors_Msg.is_error_message_string)
              (Obj.magic uu___3));
           [])
      | uu___1 -> failwith "Impossible!" in
    match c.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Total t -> FStarC_Reflection_V1_Data.C_Total t
    | FStarC_Syntax_Syntax.GTotal t -> FStarC_Reflection_V1_Data.C_GTotal t
    | FStarC_Syntax_Syntax.Comp ct ->
        let uopt =
          if
            (FStarC_Compiler_List.length ct.FStarC_Syntax_Syntax.comp_univs)
              = Prims.int_zero
          then FStarC_Syntax_Syntax.U_unknown
          else FStarC_Compiler_List.hd ct.FStarC_Syntax_Syntax.comp_univs in
        let uu___ =
          FStarC_Ident.lid_equals ct.FStarC_Syntax_Syntax.effect_name
            FStarC_Parser_Const.effect_Lemma_lid in
        if uu___
        then
          (match ct.FStarC_Syntax_Syntax.effect_args with
           | (pre, uu___1)::(post, uu___2)::(pats, uu___3)::uu___4 ->
               FStarC_Reflection_V1_Data.C_Lemma (pre, post, pats)
           | uu___1 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          (let inspect_arg uu___2 =
             match uu___2 with
             | (a, q) -> let uu___3 = inspect_aqual q in (a, uu___3) in
           let uu___2 =
             let uu___3 =
               FStarC_Ident.path_of_lid ct.FStarC_Syntax_Syntax.effect_name in
             let uu___4 =
               FStarC_Compiler_List.map inspect_arg
                 ct.FStarC_Syntax_Syntax.effect_args in
             let uu___5 = get_dec ct.FStarC_Syntax_Syntax.flags in
             ((ct.FStarC_Syntax_Syntax.comp_univs), uu___3,
               (ct.FStarC_Syntax_Syntax.result_typ), uu___4, uu___5) in
           FStarC_Reflection_V1_Data.C_Eff uu___2)
let (pack_comp :
  FStarC_Reflection_V1_Data.comp_view -> FStarC_Syntax_Syntax.comp) =
  fun cv ->
    let urefl_to_univs u =
      if u = FStarC_Syntax_Syntax.U_unknown then [] else [u] in
    let urefl_to_univ_opt u =
      if u = FStarC_Syntax_Syntax.U_unknown
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some u in
    match cv with
    | FStarC_Reflection_V1_Data.C_Total t -> FStarC_Syntax_Syntax.mk_Total t
    | FStarC_Reflection_V1_Data.C_GTotal t ->
        FStarC_Syntax_Syntax.mk_GTotal t
    | FStarC_Reflection_V1_Data.C_Lemma (pre, post, pats) ->
        let ct =
          let uu___ =
            let uu___1 = FStarC_Syntax_Syntax.as_arg pre in
            let uu___2 =
              let uu___3 = FStarC_Syntax_Syntax.as_arg post in
              let uu___4 =
                let uu___5 = FStarC_Syntax_Syntax.as_arg pats in [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          {
            FStarC_Syntax_Syntax.comp_univs = [];
            FStarC_Syntax_Syntax.effect_name =
              FStarC_Parser_Const.effect_Lemma_lid;
            FStarC_Syntax_Syntax.result_typ = FStarC_Syntax_Syntax.t_unit;
            FStarC_Syntax_Syntax.effect_args = uu___;
            FStarC_Syntax_Syntax.flags = []
          } in
        FStarC_Syntax_Syntax.mk_Comp ct
    | FStarC_Reflection_V1_Data.C_Eff (us, ef, res, args, decrs) ->
        let pack_arg uu___ =
          match uu___ with
          | (a, q) -> let uu___1 = pack_aqual q in (a, uu___1) in
        let flags =
          if (FStarC_Compiler_List.length decrs) = Prims.int_zero
          then []
          else
            [FStarC_Syntax_Syntax.DECREASES
               (FStarC_Syntax_Syntax.Decreases_lex decrs)] in
        let ct =
          let uu___ =
            FStarC_Ident.lid_of_path ef FStarC_Compiler_Range_Type.dummyRange in
          let uu___1 = FStarC_Compiler_List.map pack_arg args in
          {
            FStarC_Syntax_Syntax.comp_univs = us;
            FStarC_Syntax_Syntax.effect_name = uu___;
            FStarC_Syntax_Syntax.result_typ = res;
            FStarC_Syntax_Syntax.effect_args = uu___1;
            FStarC_Syntax_Syntax.flags = flags
          } in
        FStarC_Syntax_Syntax.mk_Comp ct
let (pack_const :
  FStarC_Reflection_V1_Data.vconst -> FStarC_Syntax_Syntax.sconst) =
  fun c ->
    match c with
    | FStarC_Reflection_V1_Data.C_Unit -> FStarC_Const.Const_unit
    | FStarC_Reflection_V1_Data.C_Int i ->
        let uu___ =
          let uu___1 = FStarC_BigInt.string_of_big_int i in
          (uu___1, FStar_Pervasives_Native.None) in
        FStarC_Const.Const_int uu___
    | FStarC_Reflection_V1_Data.C_True -> FStarC_Const.Const_bool true
    | FStarC_Reflection_V1_Data.C_False -> FStarC_Const.Const_bool false
    | FStarC_Reflection_V1_Data.C_String s ->
        FStarC_Const.Const_string (s, FStarC_Compiler_Range_Type.dummyRange)
    | FStarC_Reflection_V1_Data.C_Range r -> FStarC_Const.Const_range r
    | FStarC_Reflection_V1_Data.C_Reify ->
        FStarC_Const.Const_reify FStar_Pervasives_Native.None
    | FStarC_Reflection_V1_Data.C_Reflect ns ->
        let uu___ =
          FStarC_Ident.lid_of_path ns FStarC_Compiler_Range_Type.dummyRange in
        FStarC_Const.Const_reflect uu___
let (pack_ln :
  FStarC_Reflection_V1_Data.term_view -> FStarC_Syntax_Syntax.term) =
  fun tv ->
    match tv with
    | FStarC_Reflection_V1_Data.Tv_Var bv ->
        FStarC_Syntax_Syntax.bv_to_name bv
    | FStarC_Reflection_V1_Data.Tv_BVar bv ->
        FStarC_Syntax_Syntax.bv_to_tm bv
    | FStarC_Reflection_V1_Data.Tv_FVar fv ->
        FStarC_Syntax_Syntax.fv_to_tm fv
    | FStarC_Reflection_V1_Data.Tv_UInst (fv, us) ->
        let uu___ = FStarC_Syntax_Syntax.fv_to_tm fv in
        FStarC_Syntax_Syntax.mk_Tm_uinst uu___ us
    | FStarC_Reflection_V1_Data.Tv_App (l, (r, q)) ->
        let q' = pack_aqual q in FStarC_Syntax_Util.mk_app l [(r, q')]
    | FStarC_Reflection_V1_Data.Tv_Abs (b, t) ->
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_abs
             {
               FStarC_Syntax_Syntax.bs = [b];
               FStarC_Syntax_Syntax.body = t;
               FStarC_Syntax_Syntax.rc_opt = FStar_Pervasives_Native.None
             }) t.FStarC_Syntax_Syntax.pos
    | FStarC_Reflection_V1_Data.Tv_Arrow (b, c) ->
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_arrow
             { FStarC_Syntax_Syntax.bs1 = [b]; FStarC_Syntax_Syntax.comp = c
             }) c.FStarC_Syntax_Syntax.pos
    | FStarC_Reflection_V1_Data.Tv_Type u ->
        FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_type u)
          FStarC_Compiler_Range_Type.dummyRange
    | FStarC_Reflection_V1_Data.Tv_Refine (bv, sort, t) ->
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_refine
             {
               FStarC_Syntax_Syntax.b =
                 {
                   FStarC_Syntax_Syntax.ppname =
                     (bv.FStarC_Syntax_Syntax.ppname);
                   FStarC_Syntax_Syntax.index =
                     (bv.FStarC_Syntax_Syntax.index);
                   FStarC_Syntax_Syntax.sort = sort
                 };
               FStarC_Syntax_Syntax.phi = t
             }) t.FStarC_Syntax_Syntax.pos
    | FStarC_Reflection_V1_Data.Tv_Const c ->
        let uu___ =
          let uu___1 = pack_const c in
          FStarC_Syntax_Syntax.Tm_constant uu___1 in
        FStarC_Syntax_Syntax.mk uu___ FStarC_Compiler_Range_Type.dummyRange
    | FStarC_Reflection_V1_Data.Tv_Uvar (u, ctx_u_s) ->
        FStarC_Syntax_Syntax.mk (FStarC_Syntax_Syntax.Tm_uvar ctx_u_s)
          FStarC_Compiler_Range_Type.dummyRange
    | FStarC_Reflection_V1_Data.Tv_Let (false, attrs, bv, ty, t1, t2) ->
        let bv1 =
          {
            FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = ty
          } in
        let lb =
          FStarC_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl bv1) []
            bv1.FStarC_Syntax_Syntax.sort FStarC_Parser_Const.effect_Tot_lid
            t1 attrs FStarC_Compiler_Range_Type.dummyRange in
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_let
             {
               FStarC_Syntax_Syntax.lbs = (false, [lb]);
               FStarC_Syntax_Syntax.body1 = t2
             }) FStarC_Compiler_Range_Type.dummyRange
    | FStarC_Reflection_V1_Data.Tv_Let (true, attrs, bv, ty, t1, t2) ->
        let bv1 =
          {
            FStarC_Syntax_Syntax.ppname = (bv.FStarC_Syntax_Syntax.ppname);
            FStarC_Syntax_Syntax.index = (bv.FStarC_Syntax_Syntax.index);
            FStarC_Syntax_Syntax.sort = ty
          } in
        let lb =
          FStarC_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl bv1) []
            bv1.FStarC_Syntax_Syntax.sort FStarC_Parser_Const.effect_Tot_lid
            t1 attrs FStarC_Compiler_Range_Type.dummyRange in
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_let
             {
               FStarC_Syntax_Syntax.lbs = (true, [lb]);
               FStarC_Syntax_Syntax.body1 = t2
             }) FStarC_Compiler_Range_Type.dummyRange
    | FStarC_Reflection_V1_Data.Tv_Match (t, ret_opt, brs) ->
        let wrap v =
          {
            FStarC_Syntax_Syntax.v = v;
            FStarC_Syntax_Syntax.p = FStarC_Compiler_Range_Type.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStarC_Reflection_V1_Data.Pat_Constant c ->
              let uu___ =
                let uu___1 = pack_const c in
                FStarC_Syntax_Syntax.Pat_constant uu___1 in
              wrap uu___
          | FStarC_Reflection_V1_Data.Pat_Cons (fv, us_opt, ps) ->
              let uu___ =
                let uu___1 =
                  let uu___2 =
                    FStarC_Compiler_List.map
                      (fun uu___3 ->
                         match uu___3 with
                         | (p1, b) -> let uu___4 = pack_pat p1 in (uu___4, b))
                      ps in
                  (fv, us_opt, uu___2) in
                FStarC_Syntax_Syntax.Pat_cons uu___1 in
              wrap uu___
          | FStarC_Reflection_V1_Data.Pat_Var (bv, _sort) ->
              wrap (FStarC_Syntax_Syntax.Pat_var bv)
          | FStarC_Reflection_V1_Data.Pat_Dot_Term eopt ->
              wrap (FStarC_Syntax_Syntax.Pat_dot_term eopt) in
        let brs1 =
          FStarC_Compiler_List.map
            (fun uu___ ->
               match uu___ with
               | (pat, t1) ->
                   let uu___1 = pack_pat pat in
                   (uu___1, FStar_Pervasives_Native.None, t1)) brs in
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_match
             {
               FStarC_Syntax_Syntax.scrutinee = t;
               FStarC_Syntax_Syntax.ret_opt = ret_opt;
               FStarC_Syntax_Syntax.brs = brs1;
               FStarC_Syntax_Syntax.rc_opt1 = FStar_Pervasives_Native.None
             }) FStarC_Compiler_Range_Type.dummyRange
    | FStarC_Reflection_V1_Data.Tv_AscribedT (e, t, tacopt, use_eq) ->
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_ascribed
             {
               FStarC_Syntax_Syntax.tm = e;
               FStarC_Syntax_Syntax.asc =
                 ((FStar_Pervasives.Inl t), tacopt, use_eq);
               FStarC_Syntax_Syntax.eff_opt = FStar_Pervasives_Native.None
             }) FStarC_Compiler_Range_Type.dummyRange
    | FStarC_Reflection_V1_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
        FStarC_Syntax_Syntax.mk
          (FStarC_Syntax_Syntax.Tm_ascribed
             {
               FStarC_Syntax_Syntax.tm = e;
               FStarC_Syntax_Syntax.asc =
                 ((FStar_Pervasives.Inr c), tacopt, use_eq);
               FStarC_Syntax_Syntax.eff_opt = FStar_Pervasives_Native.None
             }) FStarC_Compiler_Range_Type.dummyRange
    | FStarC_Reflection_V1_Data.Tv_Unknown ->
        FStarC_Syntax_Syntax.mk FStarC_Syntax_Syntax.Tm_unknown
          FStarC_Compiler_Range_Type.dummyRange
    | FStarC_Reflection_V1_Data.Tv_Unsupp ->
        (FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_CantInspect ()
           (Obj.magic FStarC_Errors_Msg.is_error_message_string)
           (Obj.magic "packing a Tv_Unsupp into Tm_unknown");
         FStarC_Syntax_Syntax.mk FStarC_Syntax_Syntax.Tm_unknown
           FStarC_Compiler_Range_Type.dummyRange)
let (compare_bv :
  FStarC_Syntax_Syntax.bv -> FStarC_Syntax_Syntax.bv -> FStar_Order.order) =
  fun x ->
    fun y ->
      let n = FStarC_Syntax_Syntax.order_bv x y in
      if n < Prims.int_zero
      then FStar_Order.Lt
      else if n = Prims.int_zero then FStar_Order.Eq else FStar_Order.Gt
let (lookup_attr :
  FStarC_Syntax_Syntax.term ->
    FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.fv Prims.list)
  =
  fun attr ->
    fun env ->
      let uu___ =
        let uu___1 = FStarC_Syntax_Subst.compress_subst attr in
        uu___1.FStarC_Syntax_Syntax.n in
      match uu___ with
      | FStarC_Syntax_Syntax.Tm_fvar fv ->
          let ses =
            let uu___1 =
              let uu___2 = FStarC_Syntax_Syntax.lid_of_fv fv in
              FStarC_Ident.string_of_lid uu___2 in
            FStarC_TypeChecker_Env.lookup_attr env uu___1 in
          FStarC_Compiler_List.concatMap
            (fun se ->
               let uu___1 = FStarC_Syntax_Util.lid_of_sigelt se in
               match uu___1 with
               | FStar_Pervasives_Native.None -> []
               | FStar_Pervasives_Native.Some l ->
                   let uu___2 =
                     FStarC_Syntax_Syntax.lid_as_fv l
                       FStar_Pervasives_Native.None in
                   [uu___2]) ses
      | uu___1 -> []
let (all_defs_in_env :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.fv Prims.list) =
  fun env ->
    let uu___ = FStarC_TypeChecker_Env.lidents env in
    FStarC_Compiler_List.map
      (fun l -> FStarC_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None)
      uu___
let (defs_in_module :
  FStarC_TypeChecker_Env.env ->
    FStarC_Reflection_V1_Data.name -> FStarC_Syntax_Syntax.fv Prims.list)
  =
  fun env ->
    fun modul ->
      let uu___ = FStarC_TypeChecker_Env.lidents env in
      FStarC_Compiler_List.concatMap
        (fun l ->
           let ns =
             let uu___1 =
               let uu___2 = FStarC_Ident.ids_of_lid l in init uu___2 in
             FStarC_Compiler_List.map FStarC_Ident.string_of_id uu___1 in
           if ns = modul
           then
             let uu___1 =
               FStarC_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
             [uu___1]
           else []) uu___
let (lookup_typ :
  FStarC_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      FStarC_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ns ->
      let lid = FStarC_Parser_Const.p2l ns in
      FStarC_TypeChecker_Env.lookup_sigelt env lid
let (sigelt_attrs :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.attribute Prims.list) =
  fun se -> se.FStarC_Syntax_Syntax.sigattrs
let (set_sigelt_attrs :
  FStarC_Syntax_Syntax.attribute Prims.list ->
    FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.sigelt)
  =
  fun attrs ->
    fun se ->
      {
        FStarC_Syntax_Syntax.sigel = (se.FStarC_Syntax_Syntax.sigel);
        FStarC_Syntax_Syntax.sigrng = (se.FStarC_Syntax_Syntax.sigrng);
        FStarC_Syntax_Syntax.sigquals = (se.FStarC_Syntax_Syntax.sigquals);
        FStarC_Syntax_Syntax.sigmeta = (se.FStarC_Syntax_Syntax.sigmeta);
        FStarC_Syntax_Syntax.sigattrs = attrs;
        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
          (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
        FStarC_Syntax_Syntax.sigopts = (se.FStarC_Syntax_Syntax.sigopts)
      }
let (inspect_ident : FStarC_Ident.ident -> FStarC_Reflection_V1_Data.ident) =
  fun i -> FStarC_Reflection_V2_Builtins.inspect_ident i
let (pack_ident : FStarC_Reflection_V1_Data.ident -> FStarC_Ident.ident) =
  fun i -> FStarC_Reflection_V2_Builtins.pack_ident i
let (rd_to_syntax_qual :
  FStarC_Reflection_V1_Data.qualifier -> FStarC_Syntax_Syntax.qualifier) =
  fun uu___ ->
    match uu___ with
    | FStarC_Reflection_V1_Data.Assumption -> FStarC_Syntax_Syntax.Assumption
    | FStarC_Reflection_V1_Data.New -> FStarC_Syntax_Syntax.New
    | FStarC_Reflection_V1_Data.Private -> FStarC_Syntax_Syntax.Private
    | FStarC_Reflection_V1_Data.Unfold_for_unification_and_vcgen ->
        FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen
    | FStarC_Reflection_V1_Data.Visible_default ->
        FStarC_Syntax_Syntax.Visible_default
    | FStarC_Reflection_V1_Data.Irreducible ->
        FStarC_Syntax_Syntax.Irreducible
    | FStarC_Reflection_V1_Data.Inline_for_extraction ->
        FStarC_Syntax_Syntax.Inline_for_extraction
    | FStarC_Reflection_V1_Data.NoExtract -> FStarC_Syntax_Syntax.NoExtract
    | FStarC_Reflection_V1_Data.Noeq -> FStarC_Syntax_Syntax.Noeq
    | FStarC_Reflection_V1_Data.Unopteq -> FStarC_Syntax_Syntax.Unopteq
    | FStarC_Reflection_V1_Data.TotalEffect ->
        FStarC_Syntax_Syntax.TotalEffect
    | FStarC_Reflection_V1_Data.Logic -> FStarC_Syntax_Syntax.Logic
    | FStarC_Reflection_V1_Data.Reifiable -> FStarC_Syntax_Syntax.Reifiable
    | FStarC_Reflection_V1_Data.Reflectable l ->
        let uu___1 =
          FStarC_Ident.lid_of_path l FStarC_Compiler_Range_Type.dummyRange in
        FStarC_Syntax_Syntax.Reflectable uu___1
    | FStarC_Reflection_V1_Data.Discriminator l ->
        let uu___1 =
          FStarC_Ident.lid_of_path l FStarC_Compiler_Range_Type.dummyRange in
        FStarC_Syntax_Syntax.Discriminator uu___1
    | FStarC_Reflection_V1_Data.Projector (l, i) ->
        let uu___1 =
          let uu___2 =
            FStarC_Ident.lid_of_path l FStarC_Compiler_Range_Type.dummyRange in
          let uu___3 = pack_ident i in (uu___2, uu___3) in
        FStarC_Syntax_Syntax.Projector uu___1
    | FStarC_Reflection_V1_Data.RecordType (l1, l2) ->
        let uu___1 =
          let uu___2 = FStarC_Compiler_List.map pack_ident l1 in
          let uu___3 = FStarC_Compiler_List.map pack_ident l2 in
          (uu___2, uu___3) in
        FStarC_Syntax_Syntax.RecordType uu___1
    | FStarC_Reflection_V1_Data.RecordConstructor (l1, l2) ->
        let uu___1 =
          let uu___2 = FStarC_Compiler_List.map pack_ident l1 in
          let uu___3 = FStarC_Compiler_List.map pack_ident l2 in
          (uu___2, uu___3) in
        FStarC_Syntax_Syntax.RecordConstructor uu___1
    | FStarC_Reflection_V1_Data.Action l ->
        let uu___1 =
          FStarC_Ident.lid_of_path l FStarC_Compiler_Range_Type.dummyRange in
        FStarC_Syntax_Syntax.Action uu___1
    | FStarC_Reflection_V1_Data.ExceptionConstructor ->
        FStarC_Syntax_Syntax.ExceptionConstructor
    | FStarC_Reflection_V1_Data.HasMaskedEffect ->
        FStarC_Syntax_Syntax.HasMaskedEffect
    | FStarC_Reflection_V1_Data.Effect -> FStarC_Syntax_Syntax.Effect
    | FStarC_Reflection_V1_Data.OnlyName -> FStarC_Syntax_Syntax.OnlyName
let (syntax_to_rd_qual :
  FStarC_Syntax_Syntax.qualifier -> FStarC_Reflection_V1_Data.qualifier) =
  fun uu___ ->
    match uu___ with
    | FStarC_Syntax_Syntax.Assumption -> FStarC_Reflection_V1_Data.Assumption
    | FStarC_Syntax_Syntax.New -> FStarC_Reflection_V1_Data.New
    | FStarC_Syntax_Syntax.Private -> FStarC_Reflection_V1_Data.Private
    | FStarC_Syntax_Syntax.Unfold_for_unification_and_vcgen ->
        FStarC_Reflection_V1_Data.Unfold_for_unification_and_vcgen
    | FStarC_Syntax_Syntax.Visible_default ->
        FStarC_Reflection_V1_Data.Visible_default
    | FStarC_Syntax_Syntax.Irreducible ->
        FStarC_Reflection_V1_Data.Irreducible
    | FStarC_Syntax_Syntax.Inline_for_extraction ->
        FStarC_Reflection_V1_Data.Inline_for_extraction
    | FStarC_Syntax_Syntax.NoExtract -> FStarC_Reflection_V1_Data.NoExtract
    | FStarC_Syntax_Syntax.Noeq -> FStarC_Reflection_V1_Data.Noeq
    | FStarC_Syntax_Syntax.Unopteq -> FStarC_Reflection_V1_Data.Unopteq
    | FStarC_Syntax_Syntax.TotalEffect ->
        FStarC_Reflection_V1_Data.TotalEffect
    | FStarC_Syntax_Syntax.Logic -> FStarC_Reflection_V1_Data.Logic
    | FStarC_Syntax_Syntax.Reifiable -> FStarC_Reflection_V1_Data.Reifiable
    | FStarC_Syntax_Syntax.Reflectable l ->
        let uu___1 = FStarC_Ident.path_of_lid l in
        FStarC_Reflection_V1_Data.Reflectable uu___1
    | FStarC_Syntax_Syntax.Discriminator l ->
        let uu___1 = FStarC_Ident.path_of_lid l in
        FStarC_Reflection_V1_Data.Discriminator uu___1
    | FStarC_Syntax_Syntax.Projector (l, i) ->
        let uu___1 =
          let uu___2 = FStarC_Ident.path_of_lid l in
          let uu___3 = inspect_ident i in (uu___2, uu___3) in
        FStarC_Reflection_V1_Data.Projector uu___1
    | FStarC_Syntax_Syntax.RecordType (l1, l2) ->
        let uu___1 =
          let uu___2 = FStarC_Compiler_List.map inspect_ident l1 in
          let uu___3 = FStarC_Compiler_List.map inspect_ident l2 in
          (uu___2, uu___3) in
        FStarC_Reflection_V1_Data.RecordType uu___1
    | FStarC_Syntax_Syntax.RecordConstructor (l1, l2) ->
        let uu___1 =
          let uu___2 = FStarC_Compiler_List.map inspect_ident l1 in
          let uu___3 = FStarC_Compiler_List.map inspect_ident l2 in
          (uu___2, uu___3) in
        FStarC_Reflection_V1_Data.RecordConstructor uu___1
    | FStarC_Syntax_Syntax.Action l ->
        let uu___1 = FStarC_Ident.path_of_lid l in
        FStarC_Reflection_V1_Data.Action uu___1
    | FStarC_Syntax_Syntax.ExceptionConstructor ->
        FStarC_Reflection_V1_Data.ExceptionConstructor
    | FStarC_Syntax_Syntax.HasMaskedEffect ->
        FStarC_Reflection_V1_Data.HasMaskedEffect
    | FStarC_Syntax_Syntax.Effect -> FStarC_Reflection_V1_Data.Effect
    | FStarC_Syntax_Syntax.OnlyName -> FStarC_Reflection_V1_Data.OnlyName
let (sigelt_quals :
  FStarC_Syntax_Syntax.sigelt ->
    FStarC_Reflection_V1_Data.qualifier Prims.list)
  =
  fun se ->
    FStarC_Compiler_List.map syntax_to_rd_qual
      se.FStarC_Syntax_Syntax.sigquals
let (set_sigelt_quals :
  FStarC_Reflection_V1_Data.qualifier Prims.list ->
    FStarC_Syntax_Syntax.sigelt -> FStarC_Syntax_Syntax.sigelt)
  =
  fun quals ->
    fun se ->
      let uu___ = FStarC_Compiler_List.map rd_to_syntax_qual quals in
      {
        FStarC_Syntax_Syntax.sigel = (se.FStarC_Syntax_Syntax.sigel);
        FStarC_Syntax_Syntax.sigrng = (se.FStarC_Syntax_Syntax.sigrng);
        FStarC_Syntax_Syntax.sigquals = uu___;
        FStarC_Syntax_Syntax.sigmeta = (se.FStarC_Syntax_Syntax.sigmeta);
        FStarC_Syntax_Syntax.sigattrs = (se.FStarC_Syntax_Syntax.sigattrs);
        FStarC_Syntax_Syntax.sigopens_and_abbrevs =
          (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
        FStarC_Syntax_Syntax.sigopts = (se.FStarC_Syntax_Syntax.sigopts)
      }
let (sigelt_opts :
  FStarC_Syntax_Syntax.sigelt ->
    FStarC_VConfig.vconfig FStar_Pervasives_Native.option)
  = fun se -> se.FStarC_Syntax_Syntax.sigopts
let (embed_vconfig : FStarC_VConfig.vconfig -> FStarC_Syntax_Syntax.term) =
  fun vcfg ->
    let uu___ =
      FStarC_Syntax_Embeddings_Base.embed FStarC_Syntax_Embeddings.e_vconfig
        vcfg in
    uu___ FStarC_Compiler_Range_Type.dummyRange FStar_Pervasives_Native.None
      FStarC_Syntax_Embeddings_Base.id_norm_cb
let (inspect_sigelt :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Reflection_V1_Data.sigelt_view) =
  fun se ->
    match se.FStarC_Syntax_Syntax.sigel with
    | FStarC_Syntax_Syntax.Sig_let
        { FStarC_Syntax_Syntax.lbs1 = (r, lbs);
          FStarC_Syntax_Syntax.lids1 = uu___;_}
        ->
        let inspect_letbinding lb =
          let uu___1 = lb in
          match uu___1 with
          | { FStarC_Syntax_Syntax.lbname = nm;
              FStarC_Syntax_Syntax.lbunivs = us;
              FStarC_Syntax_Syntax.lbtyp = typ;
              FStarC_Syntax_Syntax.lbeff = eff;
              FStarC_Syntax_Syntax.lbdef = def;
              FStarC_Syntax_Syntax.lbattrs = attrs;
              FStarC_Syntax_Syntax.lbpos = pos;_} ->
              let uu___2 = FStarC_Syntax_Subst.univ_var_opening us in
              (match uu___2 with
               | (s, us1) ->
                   let typ1 = FStarC_Syntax_Subst.subst s typ in
                   let def1 = FStarC_Syntax_Subst.subst s def in
                   FStarC_Syntax_Util.mk_letbinding nm us1 typ1 eff def1
                     attrs pos) in
        let uu___1 =
          let uu___2 = FStarC_Compiler_List.map inspect_letbinding lbs in
          (r, uu___2) in
        FStarC_Reflection_V1_Data.Sg_Let uu___1
    | FStarC_Syntax_Syntax.Sig_inductive_typ
        { FStarC_Syntax_Syntax.lid = lid; FStarC_Syntax_Syntax.us = us;
          FStarC_Syntax_Syntax.params = param_bs;
          FStarC_Syntax_Syntax.num_uniform_params = uu___;
          FStarC_Syntax_Syntax.t = ty; FStarC_Syntax_Syntax.mutuals = uu___1;
          FStarC_Syntax_Syntax.ds = c_lids;
          FStarC_Syntax_Syntax.injective_type_params = uu___2;_}
        ->
        let nm = FStarC_Ident.path_of_lid lid in
        let uu___3 = FStarC_Syntax_Subst.univ_var_opening us in
        (match uu___3 with
         | (s, us1) ->
             let param_bs1 = FStarC_Syntax_Subst.subst_binders s param_bs in
             let ty1 = FStarC_Syntax_Subst.subst s ty in
             let uu___4 = FStarC_Syntax_Subst.open_term param_bs1 ty1 in
             (match uu___4 with
              | (param_bs2, ty2) ->
                  let inspect_ctor c_lid =
                    let uu___5 =
                      let uu___6 = get_env () in
                      FStarC_TypeChecker_Env.lookup_sigelt uu___6 c_lid in
                    match uu___5 with
                    | FStar_Pervasives_Native.Some
                        {
                          FStarC_Syntax_Syntax.sigel =
                            FStarC_Syntax_Syntax.Sig_datacon
                            { FStarC_Syntax_Syntax.lid1 = lid1;
                              FStarC_Syntax_Syntax.us1 = us2;
                              FStarC_Syntax_Syntax.t1 = cty;
                              FStarC_Syntax_Syntax.ty_lid = uu___6;
                              FStarC_Syntax_Syntax.num_ty_params = nparam;
                              FStarC_Syntax_Syntax.mutuals1 = uu___7;
                              FStarC_Syntax_Syntax.injective_type_params1 =
                                uu___8;_};
                          FStarC_Syntax_Syntax.sigrng = uu___9;
                          FStarC_Syntax_Syntax.sigquals = uu___10;
                          FStarC_Syntax_Syntax.sigmeta = uu___11;
                          FStarC_Syntax_Syntax.sigattrs = uu___12;
                          FStarC_Syntax_Syntax.sigopens_and_abbrevs = uu___13;
                          FStarC_Syntax_Syntax.sigopts = uu___14;_}
                        ->
                        let cty1 = FStarC_Syntax_Subst.subst s cty in
                        let uu___15 =
                          let uu___16 = get_env () in
                          FStarC_TypeChecker_Normalize.get_n_binders uu___16
                            nparam cty1 in
                        (match uu___15 with
                         | (param_ctor_bs, c) ->
                             (if
                                (FStarC_Compiler_List.length param_ctor_bs)
                                  <> nparam
                              then
                                failwith
                                  "impossible: inspect_sigelt: could not obtain sufficient ctor param binders"
                              else ();
                              (let uu___18 =
                                 let uu___19 =
                                   FStarC_Syntax_Util.is_total_comp c in
                                 Prims.op_Negation uu___19 in
                               if uu___18
                               then
                                 failwith
                                   "impossible: inspect_sigelt: removed parameters and got an effectful comp"
                               else ());
                              (let cty2 = FStarC_Syntax_Util.comp_result c in
                               let s' =
                                 FStarC_Compiler_List.map2
                                   (fun b1 ->
                                      fun b2 ->
                                        let uu___18 =
                                          let uu___19 =
                                            FStarC_Syntax_Syntax.bv_to_name
                                              b2.FStarC_Syntax_Syntax.binder_bv in
                                          ((b1.FStarC_Syntax_Syntax.binder_bv),
                                            uu___19) in
                                        FStarC_Syntax_Syntax.NT uu___18)
                                   param_ctor_bs param_bs2 in
                               let cty3 = FStarC_Syntax_Subst.subst s' cty2 in
                               let cty4 =
                                 FStarC_Syntax_Util.remove_inacc cty3 in
                               let uu___18 = FStarC_Ident.path_of_lid lid1 in
                               (uu___18, cty4))))
                    | uu___6 ->
                        failwith
                          "impossible: inspect_sigelt: did not find ctor" in
                  let uu___5 =
                    let uu___6 = FStarC_Compiler_List.map inspect_ident us1 in
                    let uu___7 = FStarC_Compiler_List.map inspect_ctor c_lids in
                    (nm, uu___6, param_bs2, ty2, uu___7) in
                  FStarC_Reflection_V1_Data.Sg_Inductive uu___5))
    | FStarC_Syntax_Syntax.Sig_declare_typ
        { FStarC_Syntax_Syntax.lid2 = lid; FStarC_Syntax_Syntax.us2 = us;
          FStarC_Syntax_Syntax.t2 = ty;_}
        ->
        let nm = FStarC_Ident.path_of_lid lid in
        let uu___ = FStarC_Syntax_Subst.open_univ_vars us ty in
        (match uu___ with
         | (us1, ty1) ->
             let uu___1 =
               let uu___2 = FStarC_Compiler_List.map inspect_ident us1 in
               (nm, uu___2, ty1) in
             FStarC_Reflection_V1_Data.Sg_Val uu___1)
    | uu___ -> FStarC_Reflection_V1_Data.Unk
let (pack_sigelt :
  FStarC_Reflection_V1_Data.sigelt_view -> FStarC_Syntax_Syntax.sigelt) =
  fun sv ->
    let check_lid lid =
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Ident.path_of_lid lid in
          FStarC_Compiler_List.length uu___2 in
        uu___1 <= Prims.int_one in
      if uu___
      then
        let uu___1 =
          let uu___2 =
            let uu___3 = FStarC_Ident.string_of_lid lid in
            Prims.strcat uu___3 "\" (did you forget a module path?)" in
          Prims.strcat "pack_sigelt: invalid long identifier \"" uu___2 in
        failwith uu___1
      else () in
    match sv with
    | FStarC_Reflection_V1_Data.Sg_Let (r, lbs) ->
        let pack_letbinding lb =
          let uu___ = lb in
          match uu___ with
          | { FStarC_Syntax_Syntax.lbname = nm;
              FStarC_Syntax_Syntax.lbunivs = us;
              FStarC_Syntax_Syntax.lbtyp = typ;
              FStarC_Syntax_Syntax.lbeff = eff;
              FStarC_Syntax_Syntax.lbdef = def;
              FStarC_Syntax_Syntax.lbattrs = attrs;
              FStarC_Syntax_Syntax.lbpos = pos;_} ->
              let lid =
                match nm with
                | FStar_Pervasives.Inr fv ->
                    FStarC_Syntax_Syntax.lid_of_fv fv
                | uu___1 ->
                    failwith
                      "impossible: pack_sigelt: bv in toplevel let binding" in
              (check_lid lid;
               (let s = FStarC_Syntax_Subst.univ_var_closing us in
                let typ1 = FStarC_Syntax_Subst.subst s typ in
                let def1 = FStarC_Syntax_Subst.subst s def in
                let lb1 =
                  FStarC_Syntax_Util.mk_letbinding nm us typ1 eff def1 attrs
                    pos in
                (lid, lb1))) in
        let packed = FStarC_Compiler_List.map pack_letbinding lbs in
        let lbs1 =
          FStarC_Compiler_List.map FStar_Pervasives_Native.snd packed in
        let lids =
          FStarC_Compiler_List.map FStar_Pervasives_Native.fst packed in
        FStarC_Syntax_Syntax.mk_sigelt
          (FStarC_Syntax_Syntax.Sig_let
             {
               FStarC_Syntax_Syntax.lbs1 = (r, lbs1);
               FStarC_Syntax_Syntax.lids1 = lids
             })
    | FStarC_Reflection_V1_Data.Sg_Inductive
        (nm, us_names, param_bs, ty, ctors) ->
        let us_names1 = FStarC_Compiler_List.map pack_ident us_names in
        let ind_lid =
          FStarC_Ident.lid_of_path nm FStarC_Compiler_Range_Type.dummyRange in
        (check_lid ind_lid;
         (let s = FStarC_Syntax_Subst.univ_var_closing us_names1 in
          let nparam = FStarC_Compiler_List.length param_bs in
          let injective_type_params = false in
          let pack_ctor c =
            let uu___1 = c in
            match uu___1 with
            | (nm1, ty1) ->
                let lid =
                  FStarC_Ident.lid_of_path nm1
                    FStarC_Compiler_Range_Type.dummyRange in
                let ty2 =
                  let uu___2 = FStarC_Syntax_Syntax.mk_Total ty1 in
                  FStarC_Syntax_Util.arrow param_bs uu___2 in
                let ty3 = FStarC_Syntax_Subst.subst s ty2 in
                FStarC_Syntax_Syntax.mk_sigelt
                  (FStarC_Syntax_Syntax.Sig_datacon
                     {
                       FStarC_Syntax_Syntax.lid1 = lid;
                       FStarC_Syntax_Syntax.us1 = us_names1;
                       FStarC_Syntax_Syntax.t1 = ty3;
                       FStarC_Syntax_Syntax.ty_lid = ind_lid;
                       FStarC_Syntax_Syntax.num_ty_params = nparam;
                       FStarC_Syntax_Syntax.mutuals1 = [];
                       FStarC_Syntax_Syntax.injective_type_params1 =
                         injective_type_params
                     }) in
          let ctor_ses = FStarC_Compiler_List.map pack_ctor ctors in
          let c_lids =
            FStarC_Compiler_List.map
              (fun se ->
                 let uu___1 = FStarC_Syntax_Util.lid_of_sigelt se in
                 FStarC_Compiler_Util.must uu___1) ctor_ses in
          let ind_se =
            let param_bs1 = FStarC_Syntax_Subst.close_binders param_bs in
            let ty1 = FStarC_Syntax_Subst.close param_bs1 ty in
            let param_bs2 = FStarC_Syntax_Subst.subst_binders s param_bs1 in
            let ty2 = FStarC_Syntax_Subst.subst s ty1 in
            FStarC_Syntax_Syntax.mk_sigelt
              (FStarC_Syntax_Syntax.Sig_inductive_typ
                 {
                   FStarC_Syntax_Syntax.lid = ind_lid;
                   FStarC_Syntax_Syntax.us = us_names1;
                   FStarC_Syntax_Syntax.params = param_bs2;
                   FStarC_Syntax_Syntax.num_uniform_params =
                     FStar_Pervasives_Native.None;
                   FStarC_Syntax_Syntax.t = ty2;
                   FStarC_Syntax_Syntax.mutuals = [];
                   FStarC_Syntax_Syntax.ds = c_lids;
                   FStarC_Syntax_Syntax.injective_type_params =
                     injective_type_params
                 }) in
          let se =
            FStarC_Syntax_Syntax.mk_sigelt
              (FStarC_Syntax_Syntax.Sig_bundle
                 {
                   FStarC_Syntax_Syntax.ses = (ind_se :: ctor_ses);
                   FStarC_Syntax_Syntax.lids = (ind_lid :: c_lids)
                 }) in
          {
            FStarC_Syntax_Syntax.sigel = (se.FStarC_Syntax_Syntax.sigel);
            FStarC_Syntax_Syntax.sigrng = (se.FStarC_Syntax_Syntax.sigrng);
            FStarC_Syntax_Syntax.sigquals = (FStarC_Syntax_Syntax.Noeq ::
              (se.FStarC_Syntax_Syntax.sigquals));
            FStarC_Syntax_Syntax.sigmeta = (se.FStarC_Syntax_Syntax.sigmeta);
            FStarC_Syntax_Syntax.sigattrs =
              (se.FStarC_Syntax_Syntax.sigattrs);
            FStarC_Syntax_Syntax.sigopens_and_abbrevs =
              (se.FStarC_Syntax_Syntax.sigopens_and_abbrevs);
            FStarC_Syntax_Syntax.sigopts = (se.FStarC_Syntax_Syntax.sigopts)
          }))
    | FStarC_Reflection_V1_Data.Sg_Val (nm, us_names, ty) ->
        let us_names1 = FStarC_Compiler_List.map pack_ident us_names in
        let val_lid =
          FStarC_Ident.lid_of_path nm FStarC_Compiler_Range_Type.dummyRange in
        (check_lid val_lid;
         (let typ = FStarC_Syntax_Subst.close_univ_vars us_names1 ty in
          FStarC_Syntax_Syntax.mk_sigelt
            (FStarC_Syntax_Syntax.Sig_declare_typ
               {
                 FStarC_Syntax_Syntax.lid2 = val_lid;
                 FStarC_Syntax_Syntax.us2 = us_names1;
                 FStarC_Syntax_Syntax.t2 = typ
               })))
    | FStarC_Reflection_V1_Data.Unk -> failwith "packing Unk, sorry"
let (inspect_lb :
  FStarC_Syntax_Syntax.letbinding -> FStarC_Reflection_V1_Data.lb_view) =
  fun lb ->
    let uu___ = lb in
    match uu___ with
    | { FStarC_Syntax_Syntax.lbname = nm; FStarC_Syntax_Syntax.lbunivs = us;
        FStarC_Syntax_Syntax.lbtyp = typ; FStarC_Syntax_Syntax.lbeff = eff;
        FStarC_Syntax_Syntax.lbdef = def;
        FStarC_Syntax_Syntax.lbattrs = attrs;
        FStarC_Syntax_Syntax.lbpos = pos;_} ->
        let uu___1 = FStarC_Syntax_Subst.univ_var_opening us in
        (match uu___1 with
         | (s, us1) ->
             let typ1 = FStarC_Syntax_Subst.subst s typ in
             let def1 = FStarC_Syntax_Subst.subst s def in
             let us2 = FStarC_Compiler_List.map inspect_ident us1 in
             (match nm with
              | FStar_Pervasives.Inr fv ->
                  {
                    FStarC_Reflection_V1_Data.lb_fv = fv;
                    FStarC_Reflection_V1_Data.lb_us = us2;
                    FStarC_Reflection_V1_Data.lb_typ = typ1;
                    FStarC_Reflection_V1_Data.lb_def = def1
                  }
              | uu___2 -> failwith "Impossible: bv in top-level let binding"))
let (pack_lb :
  FStarC_Reflection_V1_Data.lb_view -> FStarC_Syntax_Syntax.letbinding) =
  fun lbv ->
    let uu___ = lbv in
    match uu___ with
    | { FStarC_Reflection_V1_Data.lb_fv = fv;
        FStarC_Reflection_V1_Data.lb_us = us;
        FStarC_Reflection_V1_Data.lb_typ = typ;
        FStarC_Reflection_V1_Data.lb_def = def;_} ->
        let us1 = FStarC_Compiler_List.map pack_ident us in
        let s = FStarC_Syntax_Subst.univ_var_closing us1 in
        let typ1 = FStarC_Syntax_Subst.subst s typ in
        let def1 = FStarC_Syntax_Subst.subst s def in
        FStarC_Syntax_Util.mk_letbinding (FStar_Pervasives.Inr fv) us1 typ1
          FStarC_Parser_Const.effect_Tot_lid def1 []
          FStarC_Compiler_Range_Type.dummyRange
let (inspect_bv :
  FStarC_Syntax_Syntax.bv -> FStarC_Reflection_V1_Data.bv_view) =
  fun bv ->
    if bv.FStarC_Syntax_Syntax.index < Prims.int_zero
    then
      (let uu___1 =
         let uu___2 =
           FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname in
         let uu___3 =
           FStarC_Class_Show.show FStarC_Syntax_Print.showable_term
             bv.FStarC_Syntax_Syntax.sort in
         let uu___4 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_int
             bv.FStarC_Syntax_Syntax.index in
         FStarC_Compiler_Util.format3
           "inspect_bv: index is negative (%s : %s), index = %s" uu___2
           uu___3 uu___4 in
       FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_CantInspect ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic uu___1))
    else ();
    (let uu___1 =
       let uu___2 = FStarC_Ident.string_of_id bv.FStarC_Syntax_Syntax.ppname in
       FStarC_Compiler_Sealed.seal uu___2 in
     let uu___2 = FStarC_BigInt.of_int_fs bv.FStarC_Syntax_Syntax.index in
     {
       FStarC_Reflection_V1_Data.bv_ppname = uu___1;
       FStarC_Reflection_V1_Data.bv_index = uu___2
     })
let (pack_bv : FStarC_Reflection_V1_Data.bv_view -> FStarC_Syntax_Syntax.bv)
  =
  fun bvv ->
    (let uu___1 =
       let uu___2 =
         FStarC_BigInt.to_int_fs bvv.FStarC_Reflection_V1_Data.bv_index in
       uu___2 < Prims.int_zero in
     if uu___1
     then
       let uu___2 =
         let uu___3 =
           let uu___4 =
             FStarC_BigInt.to_int_fs bvv.FStarC_Reflection_V1_Data.bv_index in
           FStarC_Class_Show.show FStarC_Class_Show.showable_int uu___4 in
         FStarC_Compiler_Util.format2
           "pack_bv: index is negative (%s), index = %s"
           (FStarC_Compiler_Sealed.unseal
              bvv.FStarC_Reflection_V1_Data.bv_ppname) uu___3 in
       FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_CantInspect ()
         (Obj.magic FStarC_Errors_Msg.is_error_message_string)
         (Obj.magic uu___2)
     else ());
    (let uu___1 =
       FStarC_Ident.mk_ident
         ((FStarC_Compiler_Sealed.unseal
             bvv.FStarC_Reflection_V1_Data.bv_ppname),
           FStarC_Compiler_Range_Type.dummyRange) in
     let uu___2 =
       FStarC_BigInt.to_int_fs bvv.FStarC_Reflection_V1_Data.bv_index in
     {
       FStarC_Syntax_Syntax.ppname = uu___1;
       FStarC_Syntax_Syntax.index = uu___2;
       FStarC_Syntax_Syntax.sort = FStarC_Syntax_Syntax.tun
     })
let (inspect_binder :
  FStarC_Syntax_Syntax.binder -> FStarC_Reflection_V1_Data.binder_view) =
  fun b ->
    let attrs =
      FStarC_Syntax_Util.encode_positivity_attributes
        b.FStarC_Syntax_Syntax.binder_positivity
        b.FStarC_Syntax_Syntax.binder_attrs in
    let uu___ = inspect_bqual b.FStarC_Syntax_Syntax.binder_qual in
    {
      FStarC_Reflection_V1_Data.binder_bv =
        (b.FStarC_Syntax_Syntax.binder_bv);
      FStarC_Reflection_V1_Data.binder_qual = uu___;
      FStarC_Reflection_V1_Data.binder_attrs = attrs;
      FStarC_Reflection_V1_Data.binder_sort =
        ((b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort)
    }
let (pack_binder :
  FStarC_Reflection_V1_Data.binder_view -> FStarC_Syntax_Syntax.binder) =
  fun bview ->
    let uu___ =
      FStarC_Syntax_Util.parse_positivity_attributes
        bview.FStarC_Reflection_V1_Data.binder_attrs in
    match uu___ with
    | (pqual, attrs) ->
        let uu___1 = pack_bqual bview.FStarC_Reflection_V1_Data.binder_qual in
        {
          FStarC_Syntax_Syntax.binder_bv =
            (let uu___2 = bview.FStarC_Reflection_V1_Data.binder_bv in
             {
               FStarC_Syntax_Syntax.ppname =
                 (uu___2.FStarC_Syntax_Syntax.ppname);
               FStarC_Syntax_Syntax.index =
                 (uu___2.FStarC_Syntax_Syntax.index);
               FStarC_Syntax_Syntax.sort =
                 (bview.FStarC_Reflection_V1_Data.binder_sort)
             });
          FStarC_Syntax_Syntax.binder_qual = uu___1;
          FStarC_Syntax_Syntax.binder_positivity = pqual;
          FStarC_Syntax_Syntax.binder_attrs = attrs
        }
let (moduleof : FStarC_TypeChecker_Env.env -> Prims.string Prims.list) =
  fun e -> FStarC_Ident.path_of_lid e.FStarC_TypeChecker_Env.curmodule
let (env_open_modules :
  FStarC_TypeChecker_Env.env -> FStarC_Reflection_V1_Data.name Prims.list) =
  fun e ->
    let uu___ =
      FStarC_Syntax_DsEnv.open_modules e.FStarC_TypeChecker_Env.dsenv in
    FStarC_Compiler_List.map
      (fun uu___1 ->
         match uu___1 with
         | (l, m) ->
             let uu___2 = FStarC_Ident.ids_of_lid l in
             FStarC_Compiler_List.map FStarC_Ident.string_of_id uu___2) uu___
let (binders_of_env :
  FStarC_TypeChecker_Env.env -> FStarC_Syntax_Syntax.binders) =
  fun e -> FStarC_TypeChecker_Env.all_binders e
let eqopt :
  'uuuuu .
    unit ->
      ('uuuuu -> 'uuuuu -> Prims.bool) ->
        'uuuuu FStar_Pervasives_Native.option ->
          'uuuuu FStar_Pervasives_Native.option -> Prims.bool
  = fun uu___ -> FStarC_Syntax_Util.eqopt
let eqlist :
  'uuuuu .
    unit ->
      ('uuuuu -> 'uuuuu -> Prims.bool) ->
        'uuuuu Prims.list -> 'uuuuu Prims.list -> Prims.bool
  = fun uu___ -> FStarC_Syntax_Util.eqlist
let eqprod :
  'uuuuu 'uuuuu1 .
    unit ->
      ('uuuuu -> 'uuuuu -> Prims.bool) ->
        ('uuuuu1 -> 'uuuuu1 -> Prims.bool) ->
          ('uuuuu * 'uuuuu1) -> ('uuuuu * 'uuuuu1) -> Prims.bool
  = fun uu___ -> FStarC_Syntax_Util.eqprod
let rec (term_eq :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let uu___ =
        let uu___1 = inspect_ln t1 in
        let uu___2 = inspect_ln t2 in (uu___1, uu___2) in
      match uu___ with
      | (FStarC_Reflection_V1_Data.Tv_Var bv1,
         FStarC_Reflection_V1_Data.Tv_Var bv2) -> bv_eq bv1 bv2
      | (FStarC_Reflection_V1_Data.Tv_BVar bv1,
         FStarC_Reflection_V1_Data.Tv_BVar bv2) -> bv_eq bv1 bv2
      | (FStarC_Reflection_V1_Data.Tv_FVar fv1,
         FStarC_Reflection_V1_Data.Tv_FVar fv2) ->
          FStarC_Syntax_Syntax.fv_eq fv1 fv2
      | (FStarC_Reflection_V1_Data.Tv_UInst (fv1, us1),
         FStarC_Reflection_V1_Data.Tv_UInst (fv2, us2)) ->
          (FStarC_Syntax_Syntax.fv_eq fv1 fv2) && (univs_eq us1 us2)
      | (FStarC_Reflection_V1_Data.Tv_App (h1, arg1),
         FStarC_Reflection_V1_Data.Tv_App (h2, arg2)) ->
          (term_eq h1 h2) && (arg_eq arg1 arg2)
      | (FStarC_Reflection_V1_Data.Tv_Abs (b1, t11),
         FStarC_Reflection_V1_Data.Tv_Abs (b2, t21)) ->
          (binder_eq b1 b2) && (term_eq t11 t21)
      | (FStarC_Reflection_V1_Data.Tv_Arrow (b1, c1),
         FStarC_Reflection_V1_Data.Tv_Arrow (b2, c2)) ->
          (binder_eq b1 b2) && (comp_eq c1 c2)
      | (FStarC_Reflection_V1_Data.Tv_Type u1,
         FStarC_Reflection_V1_Data.Tv_Type u2) -> univ_eq u1 u2
      | (FStarC_Reflection_V1_Data.Tv_Refine (b1, sort1, t11),
         FStarC_Reflection_V1_Data.Tv_Refine (b2, sort2, t21)) ->
          (term_eq sort1 sort2) && (term_eq t11 t21)
      | (FStarC_Reflection_V1_Data.Tv_Const c1,
         FStarC_Reflection_V1_Data.Tv_Const c2) -> const_eq c1 c2
      | (FStarC_Reflection_V1_Data.Tv_Uvar (n1, uv1),
         FStarC_Reflection_V1_Data.Tv_Uvar (n2, uv2)) -> n1 = n2
      | (FStarC_Reflection_V1_Data.Tv_Let (r1, ats1, bv1, ty1, m1, n1),
         FStarC_Reflection_V1_Data.Tv_Let (r2, ats2, bv2, ty2, m2, n2)) ->
          ((((r1 = r2) && ((eqlist ()) term_eq ats1 ats2)) &&
              (term_eq ty1 ty2))
             && (term_eq m1 m2))
            && (term_eq n1 n2)
      | (FStarC_Reflection_V1_Data.Tv_Match (h1, an1, brs1),
         FStarC_Reflection_V1_Data.Tv_Match (h2, an2, brs2)) ->
          ((term_eq h1 h2) && ((eqopt ()) match_ret_asc_eq an1 an2)) &&
            ((eqlist ()) branch_eq brs1 brs2)
      | (FStarC_Reflection_V1_Data.Tv_AscribedT (e1, t11, topt1, eq1),
         FStarC_Reflection_V1_Data.Tv_AscribedT (e2, t21, topt2, eq2)) ->
          (((term_eq e1 e2) && (term_eq t11 t21)) &&
             ((eqopt ()) term_eq topt1 topt2))
            && (eq1 = eq2)
      | (FStarC_Reflection_V1_Data.Tv_AscribedC (e1, c1, topt1, eq1),
         FStarC_Reflection_V1_Data.Tv_AscribedC (e2, c2, topt2, eq2)) ->
          (((term_eq e1 e2) && (comp_eq c1 c2)) &&
             ((eqopt ()) term_eq topt1 topt2))
            && (eq1 = eq2)
      | (FStarC_Reflection_V1_Data.Tv_Unknown,
         FStarC_Reflection_V1_Data.Tv_Unknown) -> true
      | uu___1 -> false
and (arg_eq :
  FStarC_Reflection_V1_Data.argv ->
    FStarC_Reflection_V1_Data.argv -> Prims.bool)
  =
  fun arg1 ->
    fun arg2 ->
      let uu___ = arg1 in
      match uu___ with
      | (a1, aq1) ->
          let uu___1 = arg2 in
          (match uu___1 with
           | (a2, aq2) -> (term_eq a1 a2) && (aqual_eq aq1 aq2))
and (aqual_eq :
  FStarC_Reflection_V1_Data.aqualv ->
    FStarC_Reflection_V1_Data.aqualv -> Prims.bool)
  =
  fun aq1 ->
    fun aq2 ->
      match (aq1, aq2) with
      | (FStarC_Reflection_V1_Data.Q_Implicit,
         FStarC_Reflection_V1_Data.Q_Implicit) -> true
      | (FStarC_Reflection_V1_Data.Q_Explicit,
         FStarC_Reflection_V1_Data.Q_Explicit) -> true
      | (FStarC_Reflection_V1_Data.Q_Meta t1,
         FStarC_Reflection_V1_Data.Q_Meta t2) -> term_eq t1 t2
      | uu___ -> false
and (binder_eq :
  FStarC_Syntax_Syntax.binder -> FStarC_Syntax_Syntax.binder -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      let bview1 = inspect_binder b1 in
      let bview2 = inspect_binder b2 in
      ((binding_bv_eq bview1.FStarC_Reflection_V1_Data.binder_bv
          bview2.FStarC_Reflection_V1_Data.binder_bv)
         &&
         (aqual_eq bview1.FStarC_Reflection_V1_Data.binder_qual
            bview2.FStarC_Reflection_V1_Data.binder_qual))
        &&
        ((eqlist ()) term_eq bview1.FStarC_Reflection_V1_Data.binder_attrs
           bview2.FStarC_Reflection_V1_Data.binder_attrs)
and (binding_bv_eq :
  FStarC_Syntax_Syntax.bv -> FStarC_Syntax_Syntax.bv -> Prims.bool) =
  fun bv1 ->
    fun bv2 ->
      term_eq bv1.FStarC_Syntax_Syntax.sort bv2.FStarC_Syntax_Syntax.sort
and (bv_eq :
  FStarC_Syntax_Syntax.bv -> FStarC_Syntax_Syntax.bv -> Prims.bool) =
  fun bv1 ->
    fun bv2 ->
      bv1.FStarC_Syntax_Syntax.index = bv2.FStarC_Syntax_Syntax.index
and (comp_eq :
  FStarC_Syntax_Syntax.comp -> FStarC_Syntax_Syntax.comp -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      let uu___ =
        let uu___1 = inspect_comp c1 in
        let uu___2 = inspect_comp c2 in (uu___1, uu___2) in
      match uu___ with
      | (FStarC_Reflection_V1_Data.C_Total t1,
         FStarC_Reflection_V1_Data.C_Total t2) -> term_eq t1 t2
      | (FStarC_Reflection_V1_Data.C_GTotal t1,
         FStarC_Reflection_V1_Data.C_GTotal t2) -> term_eq t1 t2
      | (FStarC_Reflection_V1_Data.C_Lemma (pre1, post1, pats1),
         FStarC_Reflection_V1_Data.C_Lemma (pre2, post2, pats2)) ->
          ((term_eq pre1 pre2) && (term_eq post1 post2)) &&
            (term_eq pats1 pats2)
      | (FStarC_Reflection_V1_Data.C_Eff (us1, name1, t1, args1, decrs1),
         FStarC_Reflection_V1_Data.C_Eff (us2, name2, t2, args2, decrs2)) ->
          ((((univs_eq us1 us2) && (name1 = name2)) && (term_eq t1 t2)) &&
             ((eqlist ()) arg_eq args1 args2))
            && ((eqlist ()) term_eq decrs1 decrs2)
      | uu___1 -> false
and (match_ret_asc_eq :
  FStarC_Syntax_Syntax.match_returns_ascription ->
    FStarC_Syntax_Syntax.match_returns_ascription -> Prims.bool)
  = fun a1 -> fun a2 -> (eqprod ()) binder_eq ascription_eq a1 a2
and (ascription_eq :
  FStarC_Syntax_Syntax.ascription ->
    FStarC_Syntax_Syntax.ascription -> Prims.bool)
  =
  fun asc1 ->
    fun asc2 ->
      let uu___ = asc1 in
      match uu___ with
      | (a1, topt1, eq1) ->
          let uu___1 = asc2 in
          (match uu___1 with
           | (a2, topt2, eq2) ->
               ((match (a1, a2) with
                 | (FStar_Pervasives.Inl t1, FStar_Pervasives.Inl t2) ->
                     term_eq t1 t2
                 | (FStar_Pervasives.Inr c1, FStar_Pervasives.Inr c2) ->
                     comp_eq c1 c2)
                  && ((eqopt ()) term_eq topt1 topt2))
                 && (eq1 = eq2))
and (branch_eq :
  FStarC_Reflection_V1_Data.branch ->
    FStarC_Reflection_V1_Data.branch -> Prims.bool)
  = fun c1 -> fun c2 -> (eqprod ()) pattern_eq term_eq c1 c2
and (pattern_eq :
  FStarC_Reflection_V1_Data.pattern ->
    FStarC_Reflection_V1_Data.pattern -> Prims.bool)
  =
  fun p1 ->
    fun p2 ->
      match (p1, p2) with
      | (FStarC_Reflection_V1_Data.Pat_Constant c1,
         FStarC_Reflection_V1_Data.Pat_Constant c2) -> const_eq c1 c2
      | (FStarC_Reflection_V1_Data.Pat_Cons (fv1, us1, subpats1),
         FStarC_Reflection_V1_Data.Pat_Cons (fv2, us2, subpats2)) ->
          ((FStarC_Syntax_Syntax.fv_eq fv1 fv2) &&
             ((eqopt ()) ((eqlist ()) univ_eq) us1 us2))
            &&
            ((eqlist ())
               ((eqprod ()) pattern_eq (fun b1 -> fun b2 -> b1 = b2))
               subpats1 subpats2)
      | (FStarC_Reflection_V1_Data.Pat_Var (bv1, uu___),
         FStarC_Reflection_V1_Data.Pat_Var (bv2, uu___1)) ->
          binding_bv_eq bv1 bv2
      | (FStarC_Reflection_V1_Data.Pat_Dot_Term topt1,
         FStarC_Reflection_V1_Data.Pat_Dot_Term topt2) ->
          (eqopt ()) term_eq topt1 topt2
      | uu___ -> false
and (const_eq :
  FStarC_Reflection_V1_Data.vconst ->
    FStarC_Reflection_V1_Data.vconst -> Prims.bool)
  = fun c1 -> fun c2 -> c1 = c2
and (univ_eq :
  FStarC_Syntax_Syntax.universe ->
    FStarC_Syntax_Syntax.universe -> Prims.bool)
  = fun u1 -> fun u2 -> FStarC_Syntax_Util.eq_univs u1 u2
and (univs_eq :
  FStarC_Syntax_Syntax.universe Prims.list ->
    FStarC_Syntax_Syntax.universe Prims.list -> Prims.bool)
  = fun us1 -> fun us2 -> (eqlist ()) univ_eq us1 us2
let (implode_qn : Prims.string Prims.list -> Prims.string) =
  fun ns -> FStarC_Compiler_String.concat "." ns
let (explode_qn : Prims.string -> Prims.string Prims.list) =
  fun s -> FStarC_Compiler_String.split [46] s
let (compare_string : Prims.string -> Prims.string -> FStarC_BigInt.t) =
  fun s1 ->
    fun s2 -> FStarC_BigInt.of_int_fs (FStarC_Compiler_String.compare s1 s2)
let (push_binder :
  FStarC_TypeChecker_Env.env ->
    FStarC_Syntax_Syntax.binder -> FStarC_TypeChecker_Env.env)
  = fun e -> fun b -> FStarC_TypeChecker_Env.push_binders e [b]
let (subst :
  FStarC_Syntax_Syntax.bv ->
    FStarC_Syntax_Syntax.term ->
      FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  =
  fun x ->
    fun n ->
      fun m -> FStarC_Syntax_Subst.subst [FStarC_Syntax_Syntax.NT (x, n)] m
let (close_term :
  FStarC_Syntax_Syntax.binder ->
    FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term)
  = fun b -> fun t -> FStarC_Syntax_Subst.close [b] t
let (range_of_term :
  FStarC_Syntax_Syntax.term -> FStarC_Compiler_Range_Type.range) =
  fun t -> t.FStarC_Syntax_Syntax.pos
let (range_of_sigelt :
  FStarC_Syntax_Syntax.sigelt -> FStarC_Compiler_Range_Type.range) =
  fun s -> s.FStarC_Syntax_Syntax.sigrng