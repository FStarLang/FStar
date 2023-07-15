open Prims
let (get_env : unit -> FStar_TypeChecker_Env.env) =
  fun uu___ ->
    let uu___1 =
      FStar_Compiler_Effect.op_Bang
        FStar_TypeChecker_Normalize.reflection_env_hook in
    match uu___1 with
    | FStar_Pervasives_Native.None ->
        failwith "impossible: env_hook unset in reflection"
    | FStar_Pervasives_Native.Some e -> e
let (inspect_bqual :
  FStar_Syntax_Syntax.bqual -> FStar_Reflection_V2_Data.aqualv) =
  fun bq ->
    match bq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu___) ->
        FStar_Reflection_V2_Data.Q_Implicit
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t) ->
        FStar_Reflection_V2_Data.Q_Meta t
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
        FStar_Reflection_V2_Data.Q_Explicit
    | FStar_Pervasives_Native.None -> FStar_Reflection_V2_Data.Q_Explicit
let (inspect_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Reflection_V2_Data.aqualv) =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.Some
        { FStar_Syntax_Syntax.aqual_implicit = true;
          FStar_Syntax_Syntax.aqual_attributes = uu___;_}
        -> FStar_Reflection_V2_Data.Q_Implicit
    | uu___ -> FStar_Reflection_V2_Data.Q_Explicit
let (pack_bqual :
  FStar_Reflection_V2_Data.aqualv -> FStar_Syntax_Syntax.bqual) =
  fun aqv ->
    match aqv with
    | FStar_Reflection_V2_Data.Q_Explicit -> FStar_Pervasives_Native.None
    | FStar_Reflection_V2_Data.Q_Implicit ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit false)
    | FStar_Reflection_V2_Data.Q_Meta t ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t)
let (pack_aqual :
  FStar_Reflection_V2_Data.aqualv -> FStar_Syntax_Syntax.aqual) =
  fun aqv ->
    match aqv with
    | FStar_Reflection_V2_Data.Q_Implicit ->
        FStar_Syntax_Syntax.as_aqual_implicit true
    | uu___ -> FStar_Pervasives_Native.None
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv ->
    let uu___ = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu___
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns ->
    let lid = FStar_Parser_Const.p2l ns in
    let fallback uu___ =
      let quals =
        let uu___1 = FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid in
        if uu___1
        then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
        else
          (let uu___3 = FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid in
           if uu___3
           then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
           else
             (let uu___5 =
                FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid in
              if uu___5
              then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
              else
                (let uu___7 =
                   FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid in
                 if uu___7
                 then
                   FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
                 else FStar_Pervasives_Native.None))) in
      let uu___1 = FStar_Parser_Const.p2l ns in
      FStar_Syntax_Syntax.lid_as_fv uu___1 quals in
    let uu___ =
      FStar_Compiler_Effect.op_Bang
        FStar_TypeChecker_Normalize.reflection_env_hook in
    match uu___ with
    | FStar_Pervasives_Native.None -> fallback ()
    | FStar_Pervasives_Native.Some env ->
        let qninfo = FStar_TypeChecker_Env.lookup_qname env lid in
        (match qninfo with
         | FStar_Pervasives_Native.Some
             (FStar_Pervasives.Inr (se, _us), _rng) ->
             let quals = FStar_Syntax_DsEnv.fv_qual_of_se se in
             let uu___1 = FStar_Parser_Const.p2l ns in
             FStar_Syntax_Syntax.lid_as_fv uu___1 quals
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
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_V2_Data.vconst) =
  fun c ->
    match c with
    | FStar_Const.Const_unit -> FStar_Reflection_V2_Data.C_Unit
    | FStar_Const.Const_int (s, uu___) ->
        let uu___1 = FStar_BigInt.big_int_of_string s in
        FStar_Reflection_V2_Data.C_Int uu___1
    | FStar_Const.Const_bool (true) -> FStar_Reflection_V2_Data.C_True
    | FStar_Const.Const_bool (false) -> FStar_Reflection_V2_Data.C_False
    | FStar_Const.Const_string (s, uu___) ->
        FStar_Reflection_V2_Data.C_String s
    | FStar_Const.Const_range r -> FStar_Reflection_V2_Data.C_Range r
    | FStar_Const.Const_reify uu___ -> FStar_Reflection_V2_Data.C_Reify
    | FStar_Const.Const_reflect l ->
        let uu___ = FStar_Ident.path_of_lid l in
        FStar_Reflection_V2_Data.C_Reflect uu___
    | uu___ ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Print.const_to_string c in
          FStar_Compiler_Util.format1 "unknown constant: %s" uu___2 in
        failwith uu___1
let (inspect_universe :
  FStar_Syntax_Syntax.universe -> FStar_Reflection_V2_Data.universe_view) =
  fun u ->
    match u with
    | FStar_Syntax_Syntax.U_zero -> FStar_Reflection_V2_Data.Uv_Zero
    | FStar_Syntax_Syntax.U_succ u1 -> FStar_Reflection_V2_Data.Uv_Succ u1
    | FStar_Syntax_Syntax.U_max us -> FStar_Reflection_V2_Data.Uv_Max us
    | FStar_Syntax_Syntax.U_bvar n ->
        let uu___ = FStar_BigInt.of_int_fs n in
        FStar_Reflection_V2_Data.Uv_BVar uu___
    | FStar_Syntax_Syntax.U_name i -> FStar_Reflection_V2_Data.Uv_Name i
    | FStar_Syntax_Syntax.U_unif u1 -> FStar_Reflection_V2_Data.Uv_Unif u1
    | FStar_Syntax_Syntax.U_unknown -> FStar_Reflection_V2_Data.Uv_Unk
let (pack_universe :
  FStar_Reflection_V2_Data.universe_view -> FStar_Syntax_Syntax.universe) =
  fun uv ->
    match uv with
    | FStar_Reflection_V2_Data.Uv_Zero -> FStar_Syntax_Syntax.U_zero
    | FStar_Reflection_V2_Data.Uv_Succ u -> FStar_Syntax_Syntax.U_succ u
    | FStar_Reflection_V2_Data.Uv_Max us -> FStar_Syntax_Syntax.U_max us
    | FStar_Reflection_V2_Data.Uv_BVar n ->
        let uu___ = FStar_BigInt.to_int_fs n in
        FStar_Syntax_Syntax.U_bvar uu___
    | FStar_Reflection_V2_Data.Uv_Name i -> FStar_Syntax_Syntax.U_name i
    | FStar_Reflection_V2_Data.Uv_Unif u -> FStar_Syntax_Syntax.U_unif u
    | FStar_Reflection_V2_Data.Uv_Unk -> FStar_Syntax_Syntax.U_unknown
let rec (inspect_pat :
  FStar_Syntax_Syntax.pat -> FStar_Reflection_V2_Data.pattern) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_constant c ->
        let uu___ = inspect_const c in
        FStar_Reflection_V2_Data.Pat_Constant uu___
    | FStar_Syntax_Syntax.Pat_cons (fv, us_opt, ps) ->
        let uu___ =
          FStar_Compiler_List.map
            (fun uu___1 ->
               match uu___1 with
               | (p1, b) -> let uu___2 = inspect_pat p1 in (uu___2, b)) ps in
        FStar_Reflection_V2_Data.Pat_Cons (fv, us_opt, uu___)
    | FStar_Syntax_Syntax.Pat_var bv ->
        let uu___ = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
        FStar_Reflection_V2_Data.Pat_Var
          ((bv.FStar_Syntax_Syntax.sort), uu___)
    | FStar_Syntax_Syntax.Pat_dot_term eopt ->
        FStar_Reflection_V2_Data.Pat_Dot_Term eopt
let rec (inspect_ln :
  FStar_Syntax_Syntax.term -> FStar_Reflection_V2_Data.term_view) =
  fun t ->
    let t1 =
      FStar_Compiler_Effect.op_Bar_Greater t
        FStar_Syntax_Subst.compress_subst in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        { FStar_Syntax_Syntax.tm2 = t2; FStar_Syntax_Syntax.meta = uu___;_}
        -> inspect_ln t2
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Reflection_V2_Data.Tv_Var bv
    | FStar_Syntax_Syntax.Tm_bvar bv -> FStar_Reflection_V2_Data.Tv_BVar bv
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_V2_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_uinst (t2, us) ->
        (match t2.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Reflection_V2_Data.Tv_UInst (fv, us)
         | uu___ ->
             failwith "Reflection::inspect_ln: uinst for a non-fvar node")
    | FStar_Syntax_Syntax.Tm_ascribed
        { FStar_Syntax_Syntax.tm = t2;
          FStar_Syntax_Syntax.asc = (FStar_Pervasives.Inl ty, tacopt, eq);
          FStar_Syntax_Syntax.eff_opt = uu___;_}
        -> FStar_Reflection_V2_Data.Tv_AscribedT (t2, ty, tacopt, eq)
    | FStar_Syntax_Syntax.Tm_ascribed
        { FStar_Syntax_Syntax.tm = t2;
          FStar_Syntax_Syntax.asc = (FStar_Pervasives.Inr cty, tacopt, eq);
          FStar_Syntax_Syntax.eff_opt = uu___;_}
        -> FStar_Reflection_V2_Data.Tv_AscribedC (t2, cty, tacopt, eq)
    | FStar_Syntax_Syntax.Tm_app
        { FStar_Syntax_Syntax.hd = uu___; FStar_Syntax_Syntax.args = [];_} ->
        failwith "inspect_ln: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app
        { FStar_Syntax_Syntax.hd = hd; FStar_Syntax_Syntax.args = args;_} ->
        let uu___ = last args in
        (match uu___ with
         | (a, q) ->
             let q' = inspect_aqual q in
             let uu___1 =
               let uu___2 =
                 let uu___3 = init args in FStar_Syntax_Util.mk_app hd uu___3 in
               (uu___2, (a, q')) in
             FStar_Reflection_V2_Data.Tv_App uu___1)
    | FStar_Syntax_Syntax.Tm_abs
        { FStar_Syntax_Syntax.bs = []; FStar_Syntax_Syntax.body = uu___;
          FStar_Syntax_Syntax.rc_opt = uu___1;_}
        -> failwith "inspect_ln: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs
        { FStar_Syntax_Syntax.bs = b::bs; FStar_Syntax_Syntax.body = t2;
          FStar_Syntax_Syntax.rc_opt = k;_}
        ->
        let body =
          match bs with
          | [] -> t2
          | bs1 ->
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_abs
                   {
                     FStar_Syntax_Syntax.bs = bs1;
                     FStar_Syntax_Syntax.body = t2;
                     FStar_Syntax_Syntax.rc_opt = k
                   }) t2.FStar_Syntax_Syntax.pos in
        FStar_Reflection_V2_Data.Tv_Abs (b, body)
    | FStar_Syntax_Syntax.Tm_type u -> FStar_Reflection_V2_Data.Tv_Type u
    | FStar_Syntax_Syntax.Tm_arrow
        { FStar_Syntax_Syntax.bs1 = []; FStar_Syntax_Syntax.comp = uu___;_}
        -> failwith "inspect_ln: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu___ ->
        let uu___1 = FStar_Syntax_Util.arrow_one_ln t1 in
        (match uu___1 with
         | FStar_Pervasives_Native.Some (b, c) ->
             FStar_Reflection_V2_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine
        { FStar_Syntax_Syntax.b = bv; FStar_Syntax_Syntax.phi = t2;_} ->
        let uu___ =
          let uu___1 = FStar_Syntax_Syntax.mk_binder bv in (uu___1, t2) in
        FStar_Reflection_V2_Data.Tv_Refine uu___
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu___ = inspect_const c in
        FStar_Reflection_V2_Data.Tv_Const uu___
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Syntax_Unionfind.uvar_unique_id
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
            FStar_BigInt.of_int_fs uu___2 in
          (uu___1, (ctx_u, s)) in
        FStar_Reflection_V2_Data.Tv_Uvar uu___
    | FStar_Syntax_Syntax.Tm_let
        { FStar_Syntax_Syntax.lbs = (isrec, lb::[]);
          FStar_Syntax_Syntax.body1 = t2;_}
        ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_V2_Data.Tv_Unsupp
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Pervasives.Inr uu___1 ->
               FStar_Reflection_V2_Data.Tv_Unsupp
           | FStar_Pervasives.Inl bv ->
               let uu___1 =
                 let uu___2 = FStar_Syntax_Syntax.mk_binder bv in
                 (isrec, (lb.FStar_Syntax_Syntax.lbattrs), uu___2,
                   (lb.FStar_Syntax_Syntax.lbdef), t2) in
               FStar_Reflection_V2_Data.Tv_Let uu___1)
    | FStar_Syntax_Syntax.Tm_match
        { FStar_Syntax_Syntax.scrutinee = t2;
          FStar_Syntax_Syntax.ret_opt = ret_opt;
          FStar_Syntax_Syntax.brs = brs;
          FStar_Syntax_Syntax.rc_opt1 = uu___;_}
        ->
        let brs1 =
          FStar_Compiler_List.map
            (fun uu___1 ->
               match uu___1 with
               | (pat, uu___2, t3) ->
                   let uu___3 = inspect_pat pat in (uu___3, t3)) brs in
        FStar_Reflection_V2_Data.Tv_Match (t2, ret_opt, brs1)
    | FStar_Syntax_Syntax.Tm_unknown -> FStar_Reflection_V2_Data.Tv_Unknown
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu___ =
          FStar_Compiler_Effect.op_Bar_Greater i
            FStar_Syntax_Util.unfold_lazy in
        FStar_Compiler_Effect.op_Bar_Greater uu___ inspect_ln
    | uu___ ->
        ((let uu___2 =
            let uu___3 =
              let uu___4 = FStar_Syntax_Print.tag_of_term t1 in
              let uu___5 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Compiler_Util.format2
                "inspect_ln: outside of expected syntax (%s, %s)" uu___4
                uu___5 in
            (FStar_Errors_Codes.Warning_CantInspect, uu___3) in
          FStar_Errors.log_issue t1.FStar_Syntax_Syntax.pos uu___2);
         FStar_Reflection_V2_Data.Tv_Unsupp)
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_V2_Data.comp_view) =
  fun c ->
    let get_dec flags =
      let uu___ =
        FStar_Compiler_List.tryFind
          (fun uu___1 ->
             match uu___1 with
             | FStar_Syntax_Syntax.DECREASES uu___2 -> true
             | uu___2 -> false) flags in
      match uu___ with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
          (FStar_Syntax_Syntax.Decreases_lex ts)) -> ts
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
          (FStar_Syntax_Syntax.Decreases_wf uu___1)) ->
          ((let uu___3 =
              let uu___4 =
                let uu___5 = FStar_Syntax_Print.comp_to_string c in
                FStar_Compiler_Util.format1
                  "inspect_comp: inspecting comp with wf decreases clause is not yet supported: %s skipping the decreases clause"
                  uu___5 in
              (FStar_Errors_Codes.Warning_CantInspect, uu___4) in
            FStar_Errors.log_issue c.FStar_Syntax_Syntax.pos uu___3);
           [])
      | uu___1 -> failwith "Impossible!" in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total t -> FStar_Reflection_V2_Data.C_Total t
    | FStar_Syntax_Syntax.GTotal t -> FStar_Reflection_V2_Data.C_GTotal t
    | FStar_Syntax_Syntax.Comp ct ->
        let uopt =
          if
            (FStar_Compiler_List.length ct.FStar_Syntax_Syntax.comp_univs) =
              Prims.int_zero
          then FStar_Syntax_Syntax.U_unknown
          else
            FStar_Compiler_Effect.op_Bar_Greater
              ct.FStar_Syntax_Syntax.comp_univs FStar_Compiler_List.hd in
        let uu___ =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid in
        if uu___
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre, uu___1)::(post, uu___2)::(pats, uu___3)::uu___4 ->
               FStar_Reflection_V2_Data.C_Lemma (pre, post, pats)
           | uu___1 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          (let inspect_arg uu___2 =
             match uu___2 with
             | (a, q) -> let uu___3 = inspect_aqual q in (a, uu___3) in
           let uu___2 =
             let uu___3 =
               FStar_Ident.path_of_lid ct.FStar_Syntax_Syntax.effect_name in
             let uu___4 =
               FStar_Compiler_List.map inspect_arg
                 ct.FStar_Syntax_Syntax.effect_args in
             let uu___5 = get_dec ct.FStar_Syntax_Syntax.flags in
             ((ct.FStar_Syntax_Syntax.comp_univs), uu___3,
               (ct.FStar_Syntax_Syntax.result_typ), uu___4, uu___5) in
           FStar_Reflection_V2_Data.C_Eff uu___2)
let (pack_comp :
  FStar_Reflection_V2_Data.comp_view -> FStar_Syntax_Syntax.comp) =
  fun cv ->
    let urefl_to_univs u =
      if u = FStar_Syntax_Syntax.U_unknown then [] else [u] in
    let urefl_to_univ_opt u =
      if u = FStar_Syntax_Syntax.U_unknown
      then FStar_Pervasives_Native.None
      else FStar_Pervasives_Native.Some u in
    match cv with
    | FStar_Reflection_V2_Data.C_Total t -> FStar_Syntax_Syntax.mk_Total t
    | FStar_Reflection_V2_Data.C_GTotal t -> FStar_Syntax_Syntax.mk_GTotal t
    | FStar_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
        let ct =
          let uu___ =
            let uu___1 = FStar_Syntax_Syntax.as_arg pre in
            let uu___2 =
              let uu___3 = FStar_Syntax_Syntax.as_arg post in
              let uu___4 =
                let uu___5 = FStar_Syntax_Syntax.as_arg pats in [uu___5] in
              uu___3 :: uu___4 in
            uu___1 :: uu___2 in
          {
            FStar_Syntax_Syntax.comp_univs = [];
            FStar_Syntax_Syntax.effect_name =
              FStar_Parser_Const.effect_Lemma_lid;
            FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
            FStar_Syntax_Syntax.effect_args = uu___;
            FStar_Syntax_Syntax.flags = []
          } in
        FStar_Syntax_Syntax.mk_Comp ct
    | FStar_Reflection_V2_Data.C_Eff (us, ef, res, args, decrs) ->
        let pack_arg uu___ =
          match uu___ with
          | (a, q) -> let uu___1 = pack_aqual q in (a, uu___1) in
        let flags =
          if (FStar_Compiler_List.length decrs) = Prims.int_zero
          then []
          else
            [FStar_Syntax_Syntax.DECREASES
               (FStar_Syntax_Syntax.Decreases_lex decrs)] in
        let ct =
          let uu___ =
            FStar_Ident.lid_of_path ef FStar_Compiler_Range_Type.dummyRange in
          let uu___1 = FStar_Compiler_List.map pack_arg args in
          {
            FStar_Syntax_Syntax.comp_univs = us;
            FStar_Syntax_Syntax.effect_name = uu___;
            FStar_Syntax_Syntax.result_typ = res;
            FStar_Syntax_Syntax.effect_args = uu___1;
            FStar_Syntax_Syntax.flags = flags
          } in
        FStar_Syntax_Syntax.mk_Comp ct
let (pack_const :
  FStar_Reflection_V2_Data.vconst -> FStar_Syntax_Syntax.sconst) =
  fun c ->
    match c with
    | FStar_Reflection_V2_Data.C_Unit -> FStar_Const.Const_unit
    | FStar_Reflection_V2_Data.C_Int i ->
        let uu___ =
          let uu___1 = FStar_BigInt.string_of_big_int i in
          (uu___1, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu___
    | FStar_Reflection_V2_Data.C_True -> FStar_Const.Const_bool true
    | FStar_Reflection_V2_Data.C_False -> FStar_Const.Const_bool false
    | FStar_Reflection_V2_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Compiler_Range_Type.dummyRange)
    | FStar_Reflection_V2_Data.C_Range r -> FStar_Const.Const_range r
    | FStar_Reflection_V2_Data.C_Reify ->
        FStar_Const.Const_reify FStar_Pervasives_Native.None
    | FStar_Reflection_V2_Data.C_Reflect ns ->
        let uu___ =
          FStar_Ident.lid_of_path ns FStar_Compiler_Range_Type.dummyRange in
        FStar_Const.Const_reflect uu___
let rec (pack_pat :
  FStar_Reflection_V2_Data.pattern -> FStar_Syntax_Syntax.pat) =
  fun p ->
    let wrap v =
      {
        FStar_Syntax_Syntax.v = v;
        FStar_Syntax_Syntax.p = FStar_Compiler_Range_Type.dummyRange
      } in
    match p with
    | FStar_Reflection_V2_Data.Pat_Constant c ->
        let uu___ =
          let uu___1 = pack_const c in
          FStar_Syntax_Syntax.Pat_constant uu___1 in
        FStar_Compiler_Effect.op_Less_Bar wrap uu___
    | FStar_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              FStar_Compiler_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | (p1, b) -> let uu___4 = pack_pat p1 in (uu___4, b))
                subpats in
            (head, univs, uu___2) in
          FStar_Syntax_Syntax.Pat_cons uu___1 in
        FStar_Compiler_Effect.op_Less_Bar wrap uu___
    | FStar_Reflection_V2_Data.Pat_Var (sort, ppname) ->
        let bv =
          FStar_Syntax_Syntax.gen_bv ppname FStar_Pervasives_Native.None sort in
        FStar_Compiler_Effect.op_Less_Bar wrap
          (FStar_Syntax_Syntax.Pat_var bv)
    | FStar_Reflection_V2_Data.Pat_Dot_Term eopt ->
        FStar_Compiler_Effect.op_Less_Bar wrap
          (FStar_Syntax_Syntax.Pat_dot_term eopt)
let (pack_ln :
  FStar_Reflection_V2_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv ->
    match tv with
    | FStar_Reflection_V2_Data.Tv_Var bv ->
        FStar_Syntax_Syntax.bv_to_name
          {
            FStar_Syntax_Syntax.ppname = (bv.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
          }
    | FStar_Reflection_V2_Data.Tv_BVar bv ->
        FStar_Syntax_Syntax.bv_to_tm
          {
            FStar_Syntax_Syntax.ppname = (bv.FStar_Syntax_Syntax.ppname);
            FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort = FStar_Syntax_Syntax.tun
          }
    | FStar_Reflection_V2_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_V2_Data.Tv_UInst (fv, us) ->
        let uu___ = FStar_Syntax_Syntax.fv_to_tm fv in
        FStar_Syntax_Syntax.mk_Tm_uinst uu___ us
    | FStar_Reflection_V2_Data.Tv_App (l, (r, q)) ->
        let q' = pack_aqual q in FStar_Syntax_Util.mk_app l [(r, q')]
    | FStar_Reflection_V2_Data.Tv_Abs (b, t) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_abs
             {
               FStar_Syntax_Syntax.bs = [b];
               FStar_Syntax_Syntax.body = t;
               FStar_Syntax_Syntax.rc_opt = FStar_Pervasives_Native.None
             }) t.FStar_Syntax_Syntax.pos
    | FStar_Reflection_V2_Data.Tv_Arrow (b, c) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_arrow
             { FStar_Syntax_Syntax.bs1 = [b]; FStar_Syntax_Syntax.comp = c })
          c.FStar_Syntax_Syntax.pos
    | FStar_Reflection_V2_Data.Tv_Type u ->
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
          FStar_Compiler_Range_Type.dummyRange
    | FStar_Reflection_V2_Data.Tv_Refine (b, t) ->
        let bv = b.FStar_Syntax_Syntax.binder_bv in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_refine
             { FStar_Syntax_Syntax.b = bv; FStar_Syntax_Syntax.phi = t })
          t.FStar_Syntax_Syntax.pos
    | FStar_Reflection_V2_Data.Tv_Const c ->
        let uu___ =
          let uu___1 = pack_const c in FStar_Syntax_Syntax.Tm_constant uu___1 in
        FStar_Syntax_Syntax.mk uu___ FStar_Compiler_Range_Type.dummyRange
    | FStar_Reflection_V2_Data.Tv_Uvar (u, ctx_u_s) ->
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
          FStar_Compiler_Range_Type.dummyRange
    | FStar_Reflection_V2_Data.Tv_Let (isrec, attrs, b, t1, t2) ->
        let bv = b.FStar_Syntax_Syntax.binder_bv in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Compiler_Range_Type.dummyRange in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let
             {
               FStar_Syntax_Syntax.lbs = (isrec, [lb]);
               FStar_Syntax_Syntax.body1 = t2
             }) FStar_Compiler_Range_Type.dummyRange
    | FStar_Reflection_V2_Data.Tv_Match (t, ret_opt, brs) ->
        let brs1 =
          FStar_Compiler_List.map
            (fun uu___ ->
               match uu___ with
               | (pat, t1) ->
                   let uu___1 = pack_pat pat in
                   (uu___1, FStar_Pervasives_Native.None, t1)) brs in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match
             {
               FStar_Syntax_Syntax.scrutinee = t;
               FStar_Syntax_Syntax.ret_opt = ret_opt;
               FStar_Syntax_Syntax.brs = brs1;
               FStar_Syntax_Syntax.rc_opt1 = FStar_Pervasives_Native.None
             }) FStar_Compiler_Range_Type.dummyRange
    | FStar_Reflection_V2_Data.Tv_AscribedT (e, t, tacopt, use_eq) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             {
               FStar_Syntax_Syntax.tm = e;
               FStar_Syntax_Syntax.asc =
                 ((FStar_Pervasives.Inl t), tacopt, use_eq);
               FStar_Syntax_Syntax.eff_opt = FStar_Pervasives_Native.None
             }) FStar_Compiler_Range_Type.dummyRange
    | FStar_Reflection_V2_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             {
               FStar_Syntax_Syntax.tm = e;
               FStar_Syntax_Syntax.asc =
                 ((FStar_Pervasives.Inr c), tacopt, use_eq);
               FStar_Syntax_Syntax.eff_opt = FStar_Pervasives_Native.None
             }) FStar_Compiler_Range_Type.dummyRange
    | FStar_Reflection_V2_Data.Tv_Unknown ->
        FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
          FStar_Compiler_Range_Type.dummyRange
    | FStar_Reflection_V2_Data.Tv_Unsupp ->
        (FStar_Errors.log_issue FStar_Compiler_Range_Type.dummyRange
           (FStar_Errors_Codes.Warning_CantInspect,
             "packing a Tv_Unsupp into Tm_unknown");
         FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
           FStar_Compiler_Range_Type.dummyRange)
let (compare_bv :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv -> FStar_Order.order) =
  fun x ->
    fun y ->
      let n = FStar_Syntax_Syntax.order_bv x y in
      if n < Prims.int_zero
      then FStar_Order.Lt
      else if n = Prims.int_zero then FStar_Order.Eq else FStar_Order.Gt
let (compare_namedv :
  FStar_Reflection_V2_Data.namedv ->
    FStar_Reflection_V2_Data.namedv -> FStar_Order.order)
  =
  fun x ->
    fun y ->
      let n = FStar_Syntax_Syntax.order_bv x y in
      if n < Prims.int_zero
      then FStar_Order.Lt
      else if n = Prims.int_zero then FStar_Order.Eq else FStar_Order.Gt
let (lookup_attr :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv Prims.list)
  =
  fun attr ->
    fun env ->
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress_subst attr in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let ses =
            let uu___1 =
              let uu___2 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_Ident.string_of_lid uu___2 in
            FStar_TypeChecker_Env.lookup_attr env uu___1 in
          FStar_Compiler_List.concatMap
            (fun se ->
               let uu___1 = FStar_Syntax_Util.lid_of_sigelt se in
               match uu___1 with
               | FStar_Pervasives_Native.None -> []
               | FStar_Pervasives_Native.Some l ->
                   let uu___2 =
                     FStar_Syntax_Syntax.lid_as_fv l
                       FStar_Pervasives_Native.None in
                   [uu___2]) ses
      | uu___1 -> []
let (all_defs_in_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv Prims.list) =
  fun env ->
    let uu___ = FStar_TypeChecker_Env.lidents env in
    FStar_Compiler_List.map
      (fun l -> FStar_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None)
      uu___
let (defs_in_module :
  FStar_TypeChecker_Env.env ->
    FStar_Reflection_V2_Data.name -> FStar_Syntax_Syntax.fv Prims.list)
  =
  fun env ->
    fun modul ->
      let uu___ = FStar_TypeChecker_Env.lidents env in
      FStar_Compiler_List.concatMap
        (fun l ->
           let ns =
             let uu___1 =
               let uu___2 = FStar_Ident.ids_of_lid l in
               FStar_Compiler_Effect.op_Bar_Greater uu___2 init in
             FStar_Compiler_Effect.op_Bar_Greater uu___1
               (FStar_Compiler_List.map FStar_Ident.string_of_id) in
           if ns = modul
           then
             let uu___1 =
               FStar_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
             [uu___1]
           else []) uu___
let (lookup_typ :
  FStar_TypeChecker_Env.env ->
    Prims.string Prims.list ->
      FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option)
  =
  fun env ->
    fun ns ->
      let lid = FStar_Parser_Const.p2l ns in
      FStar_TypeChecker_Env.lookup_sigelt env lid
let (sigelt_attrs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.attribute Prims.list) =
  fun se -> se.FStar_Syntax_Syntax.sigattrs
let (set_sigelt_attrs :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun attrs ->
    fun se ->
      {
        FStar_Syntax_Syntax.sigel = (se.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng = (se.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals = (se.FStar_Syntax_Syntax.sigquals);
        FStar_Syntax_Syntax.sigmeta = (se.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = attrs;
        FStar_Syntax_Syntax.sigopts = (se.FStar_Syntax_Syntax.sigopts)
      }
let (rd_to_syntax_qual :
  FStar_Reflection_V2_Data.qualifier -> FStar_Syntax_Syntax.qualifier) =
  fun uu___ ->
    match uu___ with
    | FStar_Reflection_V2_Data.Assumption -> FStar_Syntax_Syntax.Assumption
    | FStar_Reflection_V2_Data.New -> FStar_Syntax_Syntax.New
    | FStar_Reflection_V2_Data.Private -> FStar_Syntax_Syntax.Private
    | FStar_Reflection_V2_Data.Unfold_for_unification_and_vcgen ->
        FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
    | FStar_Reflection_V2_Data.Visible_default ->
        FStar_Syntax_Syntax.Visible_default
    | FStar_Reflection_V2_Data.Irreducible -> FStar_Syntax_Syntax.Irreducible
    | FStar_Reflection_V2_Data.Inline_for_extraction ->
        FStar_Syntax_Syntax.Inline_for_extraction
    | FStar_Reflection_V2_Data.NoExtract -> FStar_Syntax_Syntax.NoExtract
    | FStar_Reflection_V2_Data.Noeq -> FStar_Syntax_Syntax.Noeq
    | FStar_Reflection_V2_Data.Unopteq -> FStar_Syntax_Syntax.Unopteq
    | FStar_Reflection_V2_Data.TotalEffect -> FStar_Syntax_Syntax.TotalEffect
    | FStar_Reflection_V2_Data.Logic -> FStar_Syntax_Syntax.Logic
    | FStar_Reflection_V2_Data.Reifiable -> FStar_Syntax_Syntax.Reifiable
    | FStar_Reflection_V2_Data.Reflectable l ->
        FStar_Syntax_Syntax.Reflectable l
    | FStar_Reflection_V2_Data.Discriminator l ->
        FStar_Syntax_Syntax.Discriminator l
    | FStar_Reflection_V2_Data.Projector (l, i) ->
        FStar_Syntax_Syntax.Projector (l, i)
    | FStar_Reflection_V2_Data.RecordType (l1, l2) ->
        FStar_Syntax_Syntax.RecordType (l1, l2)
    | FStar_Reflection_V2_Data.RecordConstructor (l1, l2) ->
        FStar_Syntax_Syntax.RecordConstructor (l1, l2)
    | FStar_Reflection_V2_Data.Action l -> FStar_Syntax_Syntax.Action l
    | FStar_Reflection_V2_Data.ExceptionConstructor ->
        FStar_Syntax_Syntax.ExceptionConstructor
    | FStar_Reflection_V2_Data.HasMaskedEffect ->
        FStar_Syntax_Syntax.HasMaskedEffect
    | FStar_Reflection_V2_Data.Effect -> FStar_Syntax_Syntax.Effect
    | FStar_Reflection_V2_Data.OnlyName -> FStar_Syntax_Syntax.OnlyName
let (syntax_to_rd_qual :
  FStar_Syntax_Syntax.qualifier -> FStar_Reflection_V2_Data.qualifier) =
  fun uu___ ->
    match uu___ with
    | FStar_Syntax_Syntax.Assumption -> FStar_Reflection_V2_Data.Assumption
    | FStar_Syntax_Syntax.New -> FStar_Reflection_V2_Data.New
    | FStar_Syntax_Syntax.Private -> FStar_Reflection_V2_Data.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ->
        FStar_Reflection_V2_Data.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default ->
        FStar_Reflection_V2_Data.Visible_default
    | FStar_Syntax_Syntax.Irreducible -> FStar_Reflection_V2_Data.Irreducible
    | FStar_Syntax_Syntax.Inline_for_extraction ->
        FStar_Reflection_V2_Data.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract -> FStar_Reflection_V2_Data.NoExtract
    | FStar_Syntax_Syntax.Noeq -> FStar_Reflection_V2_Data.Noeq
    | FStar_Syntax_Syntax.Unopteq -> FStar_Reflection_V2_Data.Unopteq
    | FStar_Syntax_Syntax.TotalEffect -> FStar_Reflection_V2_Data.TotalEffect
    | FStar_Syntax_Syntax.Logic -> FStar_Reflection_V2_Data.Logic
    | FStar_Syntax_Syntax.Reifiable -> FStar_Reflection_V2_Data.Reifiable
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Reflection_V2_Data.Reflectable l
    | FStar_Syntax_Syntax.Discriminator l ->
        FStar_Reflection_V2_Data.Discriminator l
    | FStar_Syntax_Syntax.Projector (l, i) ->
        FStar_Reflection_V2_Data.Projector (l, i)
    | FStar_Syntax_Syntax.RecordType (l1, l2) ->
        FStar_Reflection_V2_Data.RecordType (l1, l2)
    | FStar_Syntax_Syntax.RecordConstructor (l1, l2) ->
        FStar_Reflection_V2_Data.RecordConstructor (l1, l2)
    | FStar_Syntax_Syntax.Action l -> FStar_Reflection_V2_Data.Action l
    | FStar_Syntax_Syntax.ExceptionConstructor ->
        FStar_Reflection_V2_Data.ExceptionConstructor
    | FStar_Syntax_Syntax.HasMaskedEffect ->
        FStar_Reflection_V2_Data.HasMaskedEffect
    | FStar_Syntax_Syntax.Effect -> FStar_Reflection_V2_Data.Effect
    | FStar_Syntax_Syntax.OnlyName -> FStar_Reflection_V2_Data.OnlyName
let (inspect_ident :
  FStar_Ident.ident -> (Prims.string * FStar_Compiler_Range_Type.range)) =
  fun i ->
    let uu___ = FStar_Ident.string_of_id i in
    let uu___1 = FStar_Ident.range_of_id i in (uu___, uu___1)
let (pack_ident :
  (Prims.string * FStar_Compiler_Range_Type.range) -> FStar_Ident.ident) =
  fun i -> FStar_Ident.mk_ident i
let (sigelt_quals :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_V2_Data.qualifier Prims.list)
  =
  fun se ->
    FStar_Compiler_Effect.op_Bar_Greater se.FStar_Syntax_Syntax.sigquals
      (FStar_Compiler_List.map syntax_to_rd_qual)
let (set_sigelt_quals :
  FStar_Reflection_V2_Data.qualifier Prims.list ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun quals ->
    fun se ->
      let uu___ = FStar_Compiler_List.map rd_to_syntax_qual quals in
      {
        FStar_Syntax_Syntax.sigel = (se.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng = (se.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals = uu___;
        FStar_Syntax_Syntax.sigmeta = (se.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = (se.FStar_Syntax_Syntax.sigattrs);
        FStar_Syntax_Syntax.sigopts = (se.FStar_Syntax_Syntax.sigopts)
      }
let (sigelt_opts :
  FStar_Syntax_Syntax.sigelt ->
    FStar_VConfig.vconfig FStar_Pervasives_Native.option)
  = fun se -> se.FStar_Syntax_Syntax.sigopts
let (embed_vconfig : FStar_VConfig.vconfig -> FStar_Syntax_Syntax.term) =
  fun vcfg ->
    let uu___ =
      FStar_Syntax_Embeddings_Base.embed FStar_Syntax_Embeddings.e_vconfig
        vcfg in
    uu___ FStar_Compiler_Range_Type.dummyRange FStar_Pervasives_Native.None
      FStar_Syntax_Embeddings_Base.id_norm_cb
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_V2_Data.sigelt_view) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let
        { FStar_Syntax_Syntax.lbs1 = (r, lbs);
          FStar_Syntax_Syntax.lids1 = uu___;_}
        -> FStar_Reflection_V2_Data.Sg_Let (r, lbs)
    | FStar_Syntax_Syntax.Sig_inductive_typ
        { FStar_Syntax_Syntax.lid = lid; FStar_Syntax_Syntax.us = us;
          FStar_Syntax_Syntax.params = param_bs;
          FStar_Syntax_Syntax.num_uniform_params = uu___;
          FStar_Syntax_Syntax.t = ty; FStar_Syntax_Syntax.mutuals = uu___1;
          FStar_Syntax_Syntax.ds = c_lids;_}
        ->
        let nm = FStar_Ident.path_of_lid lid in
        let inspect_ctor c_lid =
          let uu___2 =
            let uu___3 = get_env () in
            FStar_TypeChecker_Env.lookup_sigelt uu___3 c_lid in
          match uu___2 with
          | FStar_Pervasives_Native.Some
              {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
                  { FStar_Syntax_Syntax.lid1 = lid1;
                    FStar_Syntax_Syntax.us1 = us1;
                    FStar_Syntax_Syntax.t1 = cty;
                    FStar_Syntax_Syntax.ty_lid = uu___3;
                    FStar_Syntax_Syntax.num_ty_params = nparam;
                    FStar_Syntax_Syntax.mutuals1 = uu___4;_};
                FStar_Syntax_Syntax.sigrng = uu___5;
                FStar_Syntax_Syntax.sigquals = uu___6;
                FStar_Syntax_Syntax.sigmeta = uu___7;
                FStar_Syntax_Syntax.sigattrs = uu___8;
                FStar_Syntax_Syntax.sigopts = uu___9;_}
              -> let uu___10 = FStar_Ident.path_of_lid lid1 in (uu___10, cty)
          | uu___3 ->
              failwith "impossible: inspect_sigelt: did not find ctor" in
        let uu___2 =
          let uu___3 = FStar_Compiler_List.map inspect_ctor c_lids in
          (nm, us, param_bs, ty, uu___3) in
        FStar_Reflection_V2_Data.Sg_Inductive uu___2
    | FStar_Syntax_Syntax.Sig_declare_typ
        { FStar_Syntax_Syntax.lid2 = lid; FStar_Syntax_Syntax.us2 = us;
          FStar_Syntax_Syntax.t2 = ty;_}
        ->
        let nm = FStar_Ident.path_of_lid lid in
        FStar_Reflection_V2_Data.Sg_Val (nm, us, ty)
    | uu___ -> FStar_Reflection_V2_Data.Unk
let (pack_sigelt :
  FStar_Reflection_V2_Data.sigelt_view -> FStar_Syntax_Syntax.sigelt) =
  fun sv ->
    let check_lid lid =
      let uu___ =
        let uu___1 =
          let uu___2 = FStar_Ident.path_of_lid lid in
          FStar_Compiler_List.length uu___2 in
        uu___1 <= Prims.int_one in
      if uu___
      then
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Ident.string_of_lid lid in
            Prims.op_Hat uu___3 "\" (did you forget a module path?)" in
          Prims.op_Hat "pack_sigelt: invalid long identifier \"" uu___2 in
        failwith uu___1
      else () in
    match sv with
    | FStar_Reflection_V2_Data.Sg_Let (r, lbs) ->
        let pack_letbinding lb =
          let uu___ = lb in
          match uu___ with
          | { FStar_Syntax_Syntax.lbname = nm;
              FStar_Syntax_Syntax.lbunivs = uu___1;
              FStar_Syntax_Syntax.lbtyp = uu___2;
              FStar_Syntax_Syntax.lbeff = uu___3;
              FStar_Syntax_Syntax.lbdef = uu___4;
              FStar_Syntax_Syntax.lbattrs = uu___5;
              FStar_Syntax_Syntax.lbpos = uu___6;_} ->
              let lid =
                match nm with
                | FStar_Pervasives.Inr fv -> FStar_Syntax_Syntax.lid_of_fv fv
                | uu___7 ->
                    failwith
                      "impossible: pack_sigelt: bv in toplevel let binding" in
              (check_lid lid; (lid, lb)) in
        let packed = FStar_Compiler_List.map pack_letbinding lbs in
        let lbs1 = FStar_Compiler_List.map FStar_Pervasives_Native.snd packed in
        let lids = FStar_Compiler_List.map FStar_Pervasives_Native.fst packed in
        FStar_Compiler_Effect.op_Less_Bar FStar_Syntax_Syntax.mk_sigelt
          (FStar_Syntax_Syntax.Sig_let
             {
               FStar_Syntax_Syntax.lbs1 = (r, lbs1);
               FStar_Syntax_Syntax.lids1 = lids
             })
    | FStar_Reflection_V2_Data.Sg_Inductive
        (nm, us_names, param_bs, ty, ctors) ->
        let ind_lid =
          FStar_Ident.lid_of_path nm FStar_Compiler_Range_Type.dummyRange in
        (check_lid ind_lid;
         (let nparam = FStar_Compiler_List.length param_bs in
          let pack_ctor c =
            let uu___1 = c in
            match uu___1 with
            | (nm1, ty1) ->
                let lid =
                  FStar_Ident.lid_of_path nm1
                    FStar_Compiler_Range_Type.dummyRange in
                FStar_Compiler_Effect.op_Less_Bar
                  FStar_Syntax_Syntax.mk_sigelt
                  (FStar_Syntax_Syntax.Sig_datacon
                     {
                       FStar_Syntax_Syntax.lid1 = lid;
                       FStar_Syntax_Syntax.us1 = us_names;
                       FStar_Syntax_Syntax.t1 = ty1;
                       FStar_Syntax_Syntax.ty_lid = ind_lid;
                       FStar_Syntax_Syntax.num_ty_params = nparam;
                       FStar_Syntax_Syntax.mutuals1 = []
                     }) in
          let ctor_ses = FStar_Compiler_List.map pack_ctor ctors in
          let c_lids =
            FStar_Compiler_List.map
              (fun se ->
                 let uu___1 = FStar_Syntax_Util.lid_of_sigelt se in
                 FStar_Compiler_Util.must uu___1) ctor_ses in
          let ind_se =
            FStar_Compiler_Effect.op_Less_Bar FStar_Syntax_Syntax.mk_sigelt
              (FStar_Syntax_Syntax.Sig_inductive_typ
                 {
                   FStar_Syntax_Syntax.lid = ind_lid;
                   FStar_Syntax_Syntax.us = us_names;
                   FStar_Syntax_Syntax.params = param_bs;
                   FStar_Syntax_Syntax.num_uniform_params =
                     FStar_Pervasives_Native.None;
                   FStar_Syntax_Syntax.t = ty;
                   FStar_Syntax_Syntax.mutuals = [];
                   FStar_Syntax_Syntax.ds = c_lids
                 }) in
          let se =
            FStar_Compiler_Effect.op_Less_Bar FStar_Syntax_Syntax.mk_sigelt
              (FStar_Syntax_Syntax.Sig_bundle
                 {
                   FStar_Syntax_Syntax.ses = (ind_se :: ctor_ses);
                   FStar_Syntax_Syntax.lids = (ind_lid :: c_lids)
                 }) in
          {
            FStar_Syntax_Syntax.sigel = (se.FStar_Syntax_Syntax.sigel);
            FStar_Syntax_Syntax.sigrng = (se.FStar_Syntax_Syntax.sigrng);
            FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Noeq ::
              (se.FStar_Syntax_Syntax.sigquals));
            FStar_Syntax_Syntax.sigmeta = (se.FStar_Syntax_Syntax.sigmeta);
            FStar_Syntax_Syntax.sigattrs = (se.FStar_Syntax_Syntax.sigattrs);
            FStar_Syntax_Syntax.sigopts = (se.FStar_Syntax_Syntax.sigopts)
          }))
    | FStar_Reflection_V2_Data.Sg_Val (nm, us_names, ty) ->
        let val_lid =
          FStar_Ident.lid_of_path nm FStar_Compiler_Range_Type.dummyRange in
        (check_lid val_lid;
         FStar_Compiler_Effect.op_Less_Bar FStar_Syntax_Syntax.mk_sigelt
           (FStar_Syntax_Syntax.Sig_declare_typ
              {
                FStar_Syntax_Syntax.lid2 = val_lid;
                FStar_Syntax_Syntax.us2 = us_names;
                FStar_Syntax_Syntax.t2 = ty
              }))
    | FStar_Reflection_V2_Data.Unk ->
        failwith "packing Unk, this should never happen"
let (inspect_lb :
  FStar_Syntax_Syntax.letbinding -> FStar_Reflection_V2_Data.lb_view) =
  fun lb ->
    let uu___ = lb in
    match uu___ with
    | { FStar_Syntax_Syntax.lbname = nm; FStar_Syntax_Syntax.lbunivs = us;
        FStar_Syntax_Syntax.lbtyp = typ; FStar_Syntax_Syntax.lbeff = uu___1;
        FStar_Syntax_Syntax.lbdef = def;
        FStar_Syntax_Syntax.lbattrs = uu___2;
        FStar_Syntax_Syntax.lbpos = uu___3;_} ->
        (match nm with
         | FStar_Pervasives.Inr fv ->
             {
               FStar_Reflection_V2_Data.lb_fv = fv;
               FStar_Reflection_V2_Data.lb_us = us;
               FStar_Reflection_V2_Data.lb_typ = typ;
               FStar_Reflection_V2_Data.lb_def = def
             }
         | uu___4 -> failwith "Impossible: bv in top-level let binding")
let (pack_lb :
  FStar_Reflection_V2_Data.lb_view -> FStar_Syntax_Syntax.letbinding) =
  fun lbv ->
    let uu___ = lbv in
    match uu___ with
    | { FStar_Reflection_V2_Data.lb_fv = fv;
        FStar_Reflection_V2_Data.lb_us = us;
        FStar_Reflection_V2_Data.lb_typ = typ;
        FStar_Reflection_V2_Data.lb_def = def;_} ->
        FStar_Syntax_Util.mk_letbinding (FStar_Pervasives.Inr fv) us typ
          FStar_Parser_Const.effect_Tot_lid def []
          FStar_Compiler_Range_Type.dummyRange
let (inspect_namedv :
  FStar_Reflection_V2_Data.namedv -> FStar_Reflection_V2_Data.namedv_view) =
  fun v ->
    if v.FStar_Syntax_Syntax.index < Prims.int_zero
    then
      (let uu___1 =
         let uu___2 =
           let uu___3 = FStar_Ident.string_of_id v.FStar_Syntax_Syntax.ppname in
           let uu___4 =
             FStar_Syntax_Print.term_to_string v.FStar_Syntax_Syntax.sort in
           FStar_Compiler_Util.format3
             "inspect_namedv: uniq is negative (%s : %s), uniq = %s" uu___3
             uu___4 (Prims.string_of_int v.FStar_Syntax_Syntax.index) in
         (FStar_Errors_Codes.Warning_CantInspect, uu___2) in
       FStar_Errors.log_issue FStar_Compiler_Range_Type.dummyRange uu___1)
    else ();
    (let uu___1 = FStar_BigInt.of_int_fs v.FStar_Syntax_Syntax.index in
     let uu___2 = FStar_Ident.string_of_id v.FStar_Syntax_Syntax.ppname in
     {
       FStar_Reflection_V2_Data.uniq = uu___1;
       FStar_Reflection_V2_Data.sort = (v.FStar_Syntax_Syntax.sort);
       FStar_Reflection_V2_Data.ppname = uu___2
     })
let (pack_namedv :
  FStar_Reflection_V2_Data.namedv_view -> FStar_Reflection_V2_Data.namedv) =
  fun vv ->
    (let uu___1 =
       let uu___2 = FStar_BigInt.to_int_fs vv.FStar_Reflection_V2_Data.uniq in
       uu___2 < Prims.int_zero in
     if uu___1
     then
       let uu___2 =
         let uu___3 =
           let uu___4 =
             let uu___5 =
               FStar_BigInt.to_int_fs vv.FStar_Reflection_V2_Data.uniq in
             Prims.string_of_int uu___5 in
           FStar_Compiler_Util.format2
             "pack_namedv: uniq is negative (%s), uniq = %s"
             vv.FStar_Reflection_V2_Data.ppname uu___4 in
         (FStar_Errors_Codes.Warning_CantInspect, uu___3) in
       FStar_Errors.log_issue FStar_Compiler_Range_Type.dummyRange uu___2
     else ());
    (let uu___1 =
       FStar_Ident.mk_ident
         ((vv.FStar_Reflection_V2_Data.ppname),
           FStar_Compiler_Range_Type.dummyRange) in
     let uu___2 = FStar_BigInt.to_int_fs vv.FStar_Reflection_V2_Data.uniq in
     {
       FStar_Syntax_Syntax.ppname = uu___1;
       FStar_Syntax_Syntax.index = uu___2;
       FStar_Syntax_Syntax.sort = (vv.FStar_Reflection_V2_Data.sort)
     })
let (inspect_bv : FStar_Syntax_Syntax.bv -> FStar_Reflection_V2_Data.bv_view)
  =
  fun bv ->
    if bv.FStar_Syntax_Syntax.index < Prims.int_zero
    then
      (let uu___1 =
         let uu___2 =
           let uu___3 =
             FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
           let uu___4 =
             FStar_Syntax_Print.term_to_string bv.FStar_Syntax_Syntax.sort in
           FStar_Compiler_Util.format3
             "inspect_bv: index is negative (%s : %s), index = %s" uu___3
             uu___4 (Prims.string_of_int bv.FStar_Syntax_Syntax.index) in
         (FStar_Errors_Codes.Warning_CantInspect, uu___2) in
       FStar_Errors.log_issue FStar_Compiler_Range_Type.dummyRange uu___1)
    else ();
    (let uu___1 = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index in
     let uu___2 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
     {
       FStar_Reflection_V2_Data.index = uu___1;
       FStar_Reflection_V2_Data.sort1 = (bv.FStar_Syntax_Syntax.sort);
       FStar_Reflection_V2_Data.ppname1 = uu___2
     })
let (pack_bv : FStar_Reflection_V2_Data.bv_view -> FStar_Syntax_Syntax.bv) =
  fun bvv ->
    (let uu___1 =
       let uu___2 = FStar_BigInt.to_int_fs bvv.FStar_Reflection_V2_Data.index in
       uu___2 < Prims.int_zero in
     if uu___1
     then
       let uu___2 =
         let uu___3 =
           let uu___4 =
             let uu___5 =
               FStar_BigInt.to_int_fs bvv.FStar_Reflection_V2_Data.index in
             Prims.string_of_int uu___5 in
           FStar_Compiler_Util.format2
             "pack_bv: index is negative (%s), index = %s"
             bvv.FStar_Reflection_V2_Data.ppname1 uu___4 in
         (FStar_Errors_Codes.Warning_CantInspect, uu___3) in
       FStar_Errors.log_issue FStar_Compiler_Range_Type.dummyRange uu___2
     else ());
    (let uu___1 =
       FStar_Ident.mk_ident
         ((bvv.FStar_Reflection_V2_Data.ppname1),
           FStar_Compiler_Range_Type.dummyRange) in
     let uu___2 = FStar_BigInt.to_int_fs bvv.FStar_Reflection_V2_Data.index in
     {
       FStar_Syntax_Syntax.ppname = uu___1;
       FStar_Syntax_Syntax.index = uu___2;
       FStar_Syntax_Syntax.sort = (bvv.FStar_Reflection_V2_Data.sort1)
     })
let (inspect_binder :
  FStar_Syntax_Syntax.binder -> FStar_Reflection_V2_Data.binder_view) =
  fun b ->
    let attrs =
      FStar_Syntax_Util.encode_positivity_attributes
        b.FStar_Syntax_Syntax.binder_positivity
        b.FStar_Syntax_Syntax.binder_attrs in
    let uu___ = inspect_bqual b.FStar_Syntax_Syntax.binder_qual in
    let uu___1 =
      FStar_Ident.string_of_id
        (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname in
    {
      FStar_Reflection_V2_Data.sort2 =
        ((b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort);
      FStar_Reflection_V2_Data.qual = uu___;
      FStar_Reflection_V2_Data.attrs = attrs;
      FStar_Reflection_V2_Data.ppname2 = uu___1
    }
let (pack_binder :
  FStar_Reflection_V2_Data.binder_view -> FStar_Syntax_Syntax.binder) =
  fun bview ->
    let uu___ =
      FStar_Syntax_Util.parse_positivity_attributes
        bview.FStar_Reflection_V2_Data.attrs in
    match uu___ with
    | (pqual, attrs) ->
        let uu___1 =
          let uu___2 =
            FStar_Ident.mk_ident
              ((bview.FStar_Reflection_V2_Data.ppname2),
                FStar_Compiler_Range_Type.dummyRange) in
          {
            FStar_Syntax_Syntax.ppname = uu___2;
            FStar_Syntax_Syntax.index = Prims.int_zero;
            FStar_Syntax_Syntax.sort = (bview.FStar_Reflection_V2_Data.sort2)
          } in
        let uu___2 = pack_bqual bview.FStar_Reflection_V2_Data.qual in
        {
          FStar_Syntax_Syntax.binder_bv = uu___1;
          FStar_Syntax_Syntax.binder_qual = uu___2;
          FStar_Syntax_Syntax.binder_positivity = pqual;
          FStar_Syntax_Syntax.binder_attrs = attrs
        }
let (moduleof : FStar_TypeChecker_Env.env -> Prims.string Prims.list) =
  fun e -> FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule
let (env_open_modules :
  FStar_TypeChecker_Env.env -> FStar_Reflection_V2_Data.name Prims.list) =
  fun e ->
    let uu___ = FStar_Syntax_DsEnv.open_modules e.FStar_TypeChecker_Env.dsenv in
    FStar_Compiler_List.map
      (fun uu___1 ->
         match uu___1 with
         | (l, m) ->
             let uu___2 = FStar_Ident.ids_of_lid l in
             FStar_Compiler_List.map FStar_Ident.string_of_id uu___2) uu___
let (bv_to_binding :
  FStar_Syntax_Syntax.bv -> FStar_Reflection_V2_Data.binding) =
  fun bv ->
    let uu___ = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index in
    let uu___1 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    {
      FStar_Reflection_V2_Data.uniq1 = uu___;
      FStar_Reflection_V2_Data.sort3 = (bv.FStar_Syntax_Syntax.sort);
      FStar_Reflection_V2_Data.ppname3 = uu___1
    }
let (vars_of_env :
  FStar_TypeChecker_Env.env -> FStar_Reflection_V2_Data.binding Prims.list) =
  fun e ->
    let uu___ = FStar_TypeChecker_Env.all_binders e in
    FStar_Compiler_Effect.op_Bar_Greater uu___
      (FStar_Compiler_List.map
         (fun b -> bv_to_binding b.FStar_Syntax_Syntax.binder_bv))
let eqopt :
  'uuuuu .
    unit ->
      ('uuuuu -> 'uuuuu -> Prims.bool) ->
        'uuuuu FStar_Pervasives_Native.option ->
          'uuuuu FStar_Pervasives_Native.option -> Prims.bool
  = fun uu___ -> FStar_Syntax_Util.eqopt
let eqlist :
  'uuuuu .
    unit ->
      ('uuuuu -> 'uuuuu -> Prims.bool) ->
        'uuuuu Prims.list -> 'uuuuu Prims.list -> Prims.bool
  = fun uu___ -> FStar_Syntax_Util.eqlist
let eqprod :
  'uuuuu 'uuuuu1 .
    unit ->
      ('uuuuu -> 'uuuuu -> Prims.bool) ->
        ('uuuuu1 -> 'uuuuu1 -> Prims.bool) ->
          ('uuuuu * 'uuuuu1) -> ('uuuuu * 'uuuuu1) -> Prims.bool
  = fun uu___ -> FStar_Syntax_Util.eqprod
let rec (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let uu___ =
        let uu___1 = inspect_ln t1 in
        let uu___2 = inspect_ln t2 in (uu___1, uu___2) in
      match uu___ with
      | (FStar_Reflection_V2_Data.Tv_Var bv1, FStar_Reflection_V2_Data.Tv_Var
         bv2) -> bv_eq bv1 bv2
      | (FStar_Reflection_V2_Data.Tv_BVar bv1,
         FStar_Reflection_V2_Data.Tv_BVar bv2) -> bv_eq bv1 bv2
      | (FStar_Reflection_V2_Data.Tv_FVar fv1,
         FStar_Reflection_V2_Data.Tv_FVar fv2) ->
          FStar_Syntax_Syntax.fv_eq fv1 fv2
      | (FStar_Reflection_V2_Data.Tv_UInst (fv1, us1),
         FStar_Reflection_V2_Data.Tv_UInst (fv2, us2)) ->
          (FStar_Syntax_Syntax.fv_eq fv1 fv2) && (univs_eq us1 us2)
      | (FStar_Reflection_V2_Data.Tv_App (h1, arg1),
         FStar_Reflection_V2_Data.Tv_App (h2, arg2)) ->
          (term_eq h1 h2) && (arg_eq arg1 arg2)
      | (FStar_Reflection_V2_Data.Tv_Abs (b1, t11),
         FStar_Reflection_V2_Data.Tv_Abs (b2, t21)) ->
          (binder_eq b1 b2) && (term_eq t11 t21)
      | (FStar_Reflection_V2_Data.Tv_Arrow (b1, c1),
         FStar_Reflection_V2_Data.Tv_Arrow (b2, c2)) ->
          (binder_eq b1 b2) && (comp_eq c1 c2)
      | (FStar_Reflection_V2_Data.Tv_Type u1,
         FStar_Reflection_V2_Data.Tv_Type u2) -> univ_eq u1 u2
      | (FStar_Reflection_V2_Data.Tv_Refine (b1, t11),
         FStar_Reflection_V2_Data.Tv_Refine (b2, t21)) ->
          (term_eq
             (b1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
             (b2.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort)
            && (term_eq t11 t21)
      | (FStar_Reflection_V2_Data.Tv_Const c1,
         FStar_Reflection_V2_Data.Tv_Const c2) -> const_eq c1 c2
      | (FStar_Reflection_V2_Data.Tv_Uvar (n1, uv1),
         FStar_Reflection_V2_Data.Tv_Uvar (n2, uv2)) -> n1 = n2
      | (FStar_Reflection_V2_Data.Tv_Let (r1, ats1, b1, m1, n1),
         FStar_Reflection_V2_Data.Tv_Let (r2, ats2, b2, m2, n2)) ->
          ((((r1 = r2) && ((eqlist ()) term_eq ats1 ats2)) &&
              (binder_eq b1 b2))
             && (term_eq m1 m2))
            && (term_eq n1 n2)
      | (FStar_Reflection_V2_Data.Tv_Match (h1, an1, brs1),
         FStar_Reflection_V2_Data.Tv_Match (h2, an2, brs2)) ->
          ((term_eq h1 h2) && ((eqopt ()) match_ret_asc_eq an1 an2)) &&
            ((eqlist ()) branch_eq brs1 brs2)
      | (FStar_Reflection_V2_Data.Tv_AscribedT (e1, t11, topt1, eq1),
         FStar_Reflection_V2_Data.Tv_AscribedT (e2, t21, topt2, eq2)) ->
          (((term_eq e1 e2) && (term_eq t11 t21)) &&
             ((eqopt ()) term_eq topt1 topt2))
            && (eq1 = eq2)
      | (FStar_Reflection_V2_Data.Tv_AscribedC (e1, c1, topt1, eq1),
         FStar_Reflection_V2_Data.Tv_AscribedC (e2, c2, topt2, eq2)) ->
          (((term_eq e1 e2) && (comp_eq c1 c2)) &&
             ((eqopt ()) term_eq topt1 topt2))
            && (eq1 = eq2)
      | (FStar_Reflection_V2_Data.Tv_Unknown,
         FStar_Reflection_V2_Data.Tv_Unknown) -> true
      | uu___1 -> false
and (arg_eq :
  FStar_Reflection_V2_Data.argv ->
    FStar_Reflection_V2_Data.argv -> Prims.bool)
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
  FStar_Reflection_V2_Data.aqualv ->
    FStar_Reflection_V2_Data.aqualv -> Prims.bool)
  =
  fun aq1 ->
    fun aq2 ->
      match (aq1, aq2) with
      | (FStar_Reflection_V2_Data.Q_Implicit,
         FStar_Reflection_V2_Data.Q_Implicit) -> true
      | (FStar_Reflection_V2_Data.Q_Explicit,
         FStar_Reflection_V2_Data.Q_Explicit) -> true
      | (FStar_Reflection_V2_Data.Q_Meta t1, FStar_Reflection_V2_Data.Q_Meta
         t2) -> term_eq t1 t2
      | uu___ -> false
and (binder_eq :
  FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      let bview1 = inspect_binder b1 in
      let bview2 = inspect_binder b2 in
      ((term_eq bview1.FStar_Reflection_V2_Data.sort2
          bview2.FStar_Reflection_V2_Data.sort2)
         &&
         (aqual_eq bview1.FStar_Reflection_V2_Data.qual
            bview2.FStar_Reflection_V2_Data.qual))
        &&
        ((eqlist ()) term_eq bview1.FStar_Reflection_V2_Data.attrs
           bview2.FStar_Reflection_V2_Data.attrs)
and (bv_eq : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv -> Prims.bool)
  =
  fun bv1 ->
    fun bv2 -> bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index
and (comp_eq :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      let uu___ =
        let uu___1 = inspect_comp c1 in
        let uu___2 = inspect_comp c2 in (uu___1, uu___2) in
      match uu___ with
      | (FStar_Reflection_V2_Data.C_Total t1,
         FStar_Reflection_V2_Data.C_Total t2) -> term_eq t1 t2
      | (FStar_Reflection_V2_Data.C_GTotal t1,
         FStar_Reflection_V2_Data.C_GTotal t2) -> term_eq t1 t2
      | (FStar_Reflection_V2_Data.C_Lemma (pre1, post1, pats1),
         FStar_Reflection_V2_Data.C_Lemma (pre2, post2, pats2)) ->
          ((term_eq pre1 pre2) && (term_eq post1 post2)) &&
            (term_eq pats1 pats2)
      | (FStar_Reflection_V2_Data.C_Eff (us1, name1, t1, args1, decrs1),
         FStar_Reflection_V2_Data.C_Eff (us2, name2, t2, args2, decrs2)) ->
          ((((univs_eq us1 us2) && (name1 = name2)) && (term_eq t1 t2)) &&
             ((eqlist ()) arg_eq args1 args2))
            && ((eqlist ()) term_eq decrs1 decrs2)
      | uu___1 -> false
and (match_ret_asc_eq :
  FStar_Syntax_Syntax.match_returns_ascription ->
    FStar_Syntax_Syntax.match_returns_ascription -> Prims.bool)
  = fun a1 -> fun a2 -> (eqprod ()) binder_eq ascription_eq a1 a2
and (ascription_eq :
  FStar_Syntax_Syntax.ascription ->
    FStar_Syntax_Syntax.ascription -> Prims.bool)
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
  FStar_Reflection_V2_Data.branch ->
    FStar_Reflection_V2_Data.branch -> Prims.bool)
  = fun c1 -> fun c2 -> (eqprod ()) pattern_eq term_eq c1 c2
and (pattern_eq :
  FStar_Reflection_V2_Data.pattern ->
    FStar_Reflection_V2_Data.pattern -> Prims.bool)
  =
  fun p1 ->
    fun p2 ->
      match (p1, p2) with
      | (FStar_Reflection_V2_Data.Pat_Constant c1,
         FStar_Reflection_V2_Data.Pat_Constant c2) -> const_eq c1 c2
      | (FStar_Reflection_V2_Data.Pat_Cons (fv1, us1, subpats1),
         FStar_Reflection_V2_Data.Pat_Cons (fv2, us2, subpats2)) ->
          ((FStar_Syntax_Syntax.fv_eq fv1 fv2) &&
             ((eqopt ()) ((eqlist ()) univ_eq) us1 us2))
            &&
            ((eqlist ())
               ((eqprod ()) pattern_eq (fun b1 -> fun b2 -> b1 = b2))
               subpats1 subpats2)
      | (FStar_Reflection_V2_Data.Pat_Var (uu___, uu___1),
         FStar_Reflection_V2_Data.Pat_Var (uu___2, uu___3)) -> true
      | (FStar_Reflection_V2_Data.Pat_Dot_Term topt1,
         FStar_Reflection_V2_Data.Pat_Dot_Term topt2) ->
          (eqopt ()) term_eq topt1 topt2
      | uu___ -> false
and (const_eq :
  FStar_Reflection_V2_Data.vconst ->
    FStar_Reflection_V2_Data.vconst -> Prims.bool)
  = fun c1 -> fun c2 -> c1 = c2
and (univ_eq :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  = fun u1 -> fun u2 -> FStar_Syntax_Util.eq_univs u1 u2
and (univs_eq :
  FStar_Syntax_Syntax.universe Prims.list ->
    FStar_Syntax_Syntax.universe Prims.list -> Prims.bool)
  = fun us1 -> fun us2 -> (eqlist ()) univ_eq us1 us2
let (implode_qn : Prims.string Prims.list -> Prims.string) =
  fun ns -> FStar_String.concat "." ns
let (explode_qn : Prims.string -> Prims.string Prims.list) =
  fun s -> FStar_String.split [46] s
let (compare_string : Prims.string -> Prims.string -> FStar_BigInt.t) =
  fun s1 -> fun s2 -> FStar_BigInt.of_int_fs (FStar_String.compare s1 s2)
let (push_binder :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.binder -> FStar_TypeChecker_Env.env)
  = fun e -> fun b -> FStar_TypeChecker_Env.push_binders e [b]
let (push_namedv :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.bv -> FStar_TypeChecker_Env.env)
  =
  fun e ->
    fun b ->
      let uu___ = let uu___1 = FStar_Syntax_Syntax.mk_binder b in [uu___1] in
      FStar_TypeChecker_Env.push_binders e uu___
let (subst_term :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun s -> fun t -> FStar_Syntax_Subst.subst s t
let (subst_comp :
  FStar_Syntax_Syntax.subst_elt Prims.list ->
    FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp)
  = fun s -> fun c -> FStar_Syntax_Subst.subst_comp s c
let (range_of_term :
  FStar_Syntax_Syntax.term -> FStar_Compiler_Range_Type.range) =
  fun t -> t.FStar_Syntax_Syntax.pos
let (range_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Compiler_Range_Type.range) =
  fun s -> s.FStar_Syntax_Syntax.sigrng