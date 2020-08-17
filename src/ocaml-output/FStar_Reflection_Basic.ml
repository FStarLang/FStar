open Prims
let (get_env : unit -> FStar_TypeChecker_Env.env) =
  fun uu____4 ->
    let uu____5 =
      FStar_ST.op_Bang FStar_TypeChecker_Normalize.reflection_env_hook in
    match uu____5 with
    | FStar_Pervasives_Native.None ->
        failwith "impossible: env_hook unset in reflection"
    | FStar_Pervasives_Native.Some e -> e
let (inspect_aqual :
  FStar_Syntax_Syntax.aqual -> FStar_Reflection_Data.aqualv) =
  fun aq ->
    match aq with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit uu____24) ->
        FStar_Reflection_Data.Q_Implicit
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
        (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t)) ->
        FStar_Reflection_Data.Q_Meta t
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
        (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t)) ->
        FStar_Reflection_Data.Q_Meta_attr t
    | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality) ->
        FStar_Reflection_Data.Q_Explicit
    | FStar_Pervasives_Native.None -> FStar_Reflection_Data.Q_Explicit
let (pack_aqual : FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.aqual)
  =
  fun aqv ->
    match aqv with
    | FStar_Reflection_Data.Q_Explicit -> FStar_Pervasives_Native.None
    | FStar_Reflection_Data.Q_Implicit ->
        FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit false)
    | FStar_Reflection_Data.Q_Meta t ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Meta
             (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t))
    | FStar_Reflection_Data.Q_Meta_attr t ->
        FStar_Pervasives_Native.Some
          (FStar_Syntax_Syntax.Meta
             (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t))
let (inspect_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv ->
    let uu____47 = FStar_Syntax_Syntax.lid_of_fv fv in
    FStar_Ident.path_of_lid uu____47
let (pack_fv : Prims.string Prims.list -> FStar_Syntax_Syntax.fv) =
  fun ns ->
    let lid = FStar_Parser_Const.p2l ns in
    let fallback uu____63 =
      let quals =
        let uu____67 = FStar_Ident.lid_equals lid FStar_Parser_Const.cons_lid in
        if uu____67
        then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
        else
          (let uu____71 =
             FStar_Ident.lid_equals lid FStar_Parser_Const.nil_lid in
           if uu____71
           then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
           else
             (let uu____75 =
                FStar_Ident.lid_equals lid FStar_Parser_Const.some_lid in
              if uu____75
              then FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
              else
                (let uu____79 =
                   FStar_Ident.lid_equals lid FStar_Parser_Const.none_lid in
                 if uu____79
                 then
                   FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor
                 else FStar_Pervasives_Native.None))) in
      let uu____83 = FStar_Parser_Const.p2l ns in
      FStar_Syntax_Syntax.lid_as_fv uu____83
        (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (999)))
        quals in
    let uu____84 =
      FStar_ST.op_Bang FStar_TypeChecker_Normalize.reflection_env_hook in
    match uu____84 with
    | FStar_Pervasives_Native.None -> fallback ()
    | FStar_Pervasives_Native.Some env ->
        let qninfo = FStar_TypeChecker_Env.lookup_qname env lid in
        (match qninfo with
         | FStar_Pervasives_Native.Some (FStar_Util.Inr (se, _us), _rng) ->
             let quals = FStar_Syntax_DsEnv.fv_qual_of_se se in
             let uu____151 = FStar_Parser_Const.p2l ns in
             FStar_Syntax_Syntax.lid_as_fv uu____151
               (FStar_Syntax_Syntax.Delta_constant_at_level
                  (Prims.of_int (999))) quals
         | uu____152 -> fallback ())
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu____169::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu____197 = init xs in x :: uu____197
let (inspect_const :
  FStar_Syntax_Syntax.sconst -> FStar_Reflection_Data.vconst) =
  fun c ->
    match c with
    | FStar_Const.Const_unit -> FStar_Reflection_Data.C_Unit
    | FStar_Const.Const_int (s, uu____206) ->
        let uu____219 = FStar_BigInt.big_int_of_string s in
        FStar_Reflection_Data.C_Int uu____219
    | FStar_Const.Const_bool (true) -> FStar_Reflection_Data.C_True
    | FStar_Const.Const_bool (false) -> FStar_Reflection_Data.C_False
    | FStar_Const.Const_string (s, uu____221) ->
        FStar_Reflection_Data.C_String s
    | FStar_Const.Const_range r -> FStar_Reflection_Data.C_Range r
    | FStar_Const.Const_reify -> FStar_Reflection_Data.C_Reify
    | FStar_Const.Const_reflect l ->
        let uu____224 = FStar_Ident.path_of_lid l in
        FStar_Reflection_Data.C_Reflect uu____224
    | uu____225 ->
        let uu____226 =
          let uu____227 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "unknown constant: %s" uu____227 in
        failwith uu____226
let rec (inspect_ln :
  FStar_Syntax_Syntax.term -> FStar_Reflection_Data.term_view) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let t2 = FStar_Syntax_Util.un_uinst t1 in
    let t3 = FStar_Syntax_Util.unlazy_emb t2 in
    match t3.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (t4, uu____237) -> inspect_ln t4
    | FStar_Syntax_Syntax.Tm_name bv -> FStar_Reflection_Data.Tv_Var bv
    | FStar_Syntax_Syntax.Tm_bvar bv -> FStar_Reflection_Data.Tv_BVar bv
    | FStar_Syntax_Syntax.Tm_fvar fv -> FStar_Reflection_Data.Tv_FVar fv
    | FStar_Syntax_Syntax.Tm_app (hd, []) ->
        failwith "inspect_ln: empty arguments on Tm_app"
    | FStar_Syntax_Syntax.Tm_app (hd, args) ->
        let uu____294 = last args in
        (match uu____294 with
         | (a, q) ->
             let q' = inspect_aqual q in
             let uu____322 =
               let uu____327 =
                 let uu____328 = init args in
                 FStar_Syntax_Util.mk_app hd uu____328 in
               (uu____327, (a, q')) in
             FStar_Reflection_Data.Tv_App uu____322)
    | FStar_Syntax_Syntax.Tm_abs ([], uu____347, uu____348) ->
        failwith "inspect_ln: empty arguments on Tm_abs"
    | FStar_Syntax_Syntax.Tm_abs (b::bs, t4, k) ->
        let body =
          match bs with
          | [] -> t4
          | bs1 ->
              FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_abs (bs1, t4, k))
                t4.FStar_Syntax_Syntax.pos in
        FStar_Reflection_Data.Tv_Abs (b, body)
    | FStar_Syntax_Syntax.Tm_type uu____439 ->
        FStar_Reflection_Data.Tv_Type ()
    | FStar_Syntax_Syntax.Tm_arrow ([], k) ->
        failwith "inspect_ln: empty binders on arrow"
    | FStar_Syntax_Syntax.Tm_arrow uu____459 ->
        let uu____474 = FStar_Syntax_Util.arrow_one_ln t3 in
        (match uu____474 with
         | FStar_Pervasives_Native.Some (b, c) ->
             FStar_Reflection_Data.Tv_Arrow (b, c)
         | FStar_Pervasives_Native.None -> failwith "impossible")
    | FStar_Syntax_Syntax.Tm_refine (bv, t4) ->
        FStar_Reflection_Data.Tv_Refine (bv, t4)
    | FStar_Syntax_Syntax.Tm_constant c ->
        let uu____498 = inspect_const c in
        FStar_Reflection_Data.Tv_Const uu____498
    | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
        let uu____517 =
          let uu____522 =
            let uu____523 =
              FStar_Syntax_Unionfind.uvar_id
                ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
            FStar_BigInt.of_int_fs uu____523 in
          (uu____522, (ctx_u, s)) in
        FStar_Reflection_Data.Tv_Uvar uu____517
    | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____549 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (false, (lb.FStar_Syntax_Syntax.lbattrs), bv,
                   (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_let ((true, lb::[]), t21) ->
        if lb.FStar_Syntax_Syntax.lbunivs <> []
        then FStar_Reflection_Data.Tv_Unknown
        else
          (match lb.FStar_Syntax_Syntax.lbname with
           | FStar_Util.Inr uu____570 -> FStar_Reflection_Data.Tv_Unknown
           | FStar_Util.Inl bv ->
               FStar_Reflection_Data.Tv_Let
                 (true, (lb.FStar_Syntax_Syntax.lbattrs), bv,
                   (lb.FStar_Syntax_Syntax.lbdef), t21))
    | FStar_Syntax_Syntax.Tm_match (t4, brs) ->
        let rec inspect_pat p =
          match p.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_constant c ->
              let uu____623 = inspect_const c in
              FStar_Reflection_Data.Pat_Constant uu____623
          | FStar_Syntax_Syntax.Pat_cons (fv, ps) ->
              let uu____642 =
                let uu____653 =
                  FStar_List.map
                    (fun uu____674 ->
                       match uu____674 with
                       | (p1, b) ->
                           let uu____691 = inspect_pat p1 in (uu____691, b))
                    ps in
                (fv, uu____653) in
              FStar_Reflection_Data.Pat_Cons uu____642
          | FStar_Syntax_Syntax.Pat_var bv ->
              FStar_Reflection_Data.Pat_Var bv
          | FStar_Syntax_Syntax.Pat_wild bv ->
              FStar_Reflection_Data.Pat_Wild bv
          | FStar_Syntax_Syntax.Pat_dot_term (bv, t5) ->
              FStar_Reflection_Data.Pat_Dot_Term (bv, t5) in
        let brs1 =
          FStar_List.map
            (fun uu___0_740 ->
               match uu___0_740 with
               | (pat, uu____762, t5) ->
                   let uu____780 = inspect_pat pat in (uu____780, t5)) brs in
        FStar_Reflection_Data.Tv_Match (t4, brs1)
    | FStar_Syntax_Syntax.Tm_unknown -> FStar_Reflection_Data.Tv_Unknown
    | uu____785 ->
        ((let uu____787 =
            let uu____792 =
              let uu____793 = FStar_Syntax_Print.tag_of_term t3 in
              let uu____794 = FStar_Syntax_Print.term_to_string t3 in
              FStar_Util.format2
                "inspect_ln: outside of expected syntax (%s, %s)\n" uu____793
                uu____794 in
            (FStar_Errors.Warning_CantInspect, uu____792) in
          FStar_Errors.log_issue t3.FStar_Syntax_Syntax.pos uu____787);
         FStar_Reflection_Data.Tv_Unknown)
let (inspect_comp :
  FStar_Syntax_Syntax.comp -> FStar_Reflection_Data.comp_view) =
  fun c ->
    let get_dec flags =
      let uu____814 =
        FStar_List.tryFind
          (fun uu___1_819 ->
             match uu___1_819 with
             | FStar_Syntax_Syntax.DECREASES uu____820 -> true
             | uu____823 -> false) flags in
      match uu____814 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES t) ->
          FStar_Pervasives_Native.Some t
      | uu____829 -> failwith "impossible" in
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu____835) ->
        FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.GTotal (t, uu____847) ->
        FStar_Reflection_Data.C_GTotal (t, FStar_Pervasives_Native.None)
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____859 =
          FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
            FStar_Parser_Const.effect_Lemma_lid in
        if uu____859
        then
          (match ct.FStar_Syntax_Syntax.effect_args with
           | (pre, uu____861)::(post, uu____863)::(pats, uu____865)::uu____866
               -> FStar_Reflection_Data.C_Lemma (pre, post, pats)
           | uu____925 ->
               failwith "inspect_comp: Lemma does not have enough arguments?")
        else
          (let uu____937 =
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Tot_lid in
           if uu____937
           then
             let md = get_dec ct.FStar_Syntax_Syntax.flags in
             FStar_Reflection_Data.C_Total
               ((ct.FStar_Syntax_Syntax.result_typ), md)
           else
             (let uu____944 =
                FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
                  FStar_Parser_Const.effect_GTot_lid in
              if uu____944
              then
                let md = get_dec ct.FStar_Syntax_Syntax.flags in
                FStar_Reflection_Data.C_GTotal
                  ((ct.FStar_Syntax_Syntax.result_typ), md)
              else
                (let inspect_arg uu____968 =
                   match uu____968 with
                   | (a, q) ->
                       let uu____987 = inspect_aqual q in (a, uu____987) in
                 let uu____990 =
                   let uu____1003 =
                     FStar_Ident.path_of_lid
                       ct.FStar_Syntax_Syntax.effect_name in
                   let uu____1004 =
                     FStar_List.map inspect_arg
                       ct.FStar_Syntax_Syntax.effect_args in
                   ([], uu____1003, (ct.FStar_Syntax_Syntax.result_typ),
                     uu____1004) in
                 FStar_Reflection_Data.C_Eff uu____990)))
let (pack_comp : FStar_Reflection_Data.comp_view -> FStar_Syntax_Syntax.comp)
  =
  fun cv ->
    match cv with
    | FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.None) ->
        FStar_Syntax_Syntax.mk_Total t
    | FStar_Reflection_Data.C_Total (t, FStar_Pervasives_Native.Some d) ->
        let ct =
          {
            FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
            FStar_Syntax_Syntax.effect_name =
              FStar_Parser_Const.effect_Tot_lid;
            FStar_Syntax_Syntax.result_typ = t;
            FStar_Syntax_Syntax.effect_args = [];
            FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.DECREASES d]
          } in
        FStar_Syntax_Syntax.mk_Comp ct
    | FStar_Reflection_Data.C_GTotal (t, FStar_Pervasives_Native.None) ->
        FStar_Syntax_Syntax.mk_GTotal t
    | FStar_Reflection_Data.C_GTotal (t, FStar_Pervasives_Native.Some d) ->
        let ct =
          {
            FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
            FStar_Syntax_Syntax.effect_name =
              FStar_Parser_Const.effect_GTot_lid;
            FStar_Syntax_Syntax.result_typ = t;
            FStar_Syntax_Syntax.effect_args = [];
            FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.DECREASES d]
          } in
        FStar_Syntax_Syntax.mk_Comp ct
    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
        let ct =
          let uu____1060 =
            let uu____1071 = FStar_Syntax_Syntax.as_arg pre in
            let uu____1080 =
              let uu____1091 = FStar_Syntax_Syntax.as_arg post in
              let uu____1100 =
                let uu____1111 = FStar_Syntax_Syntax.as_arg pats in
                [uu____1111] in
              uu____1091 :: uu____1100 in
            uu____1071 :: uu____1080 in
          {
            FStar_Syntax_Syntax.comp_univs = [];
            FStar_Syntax_Syntax.effect_name =
              FStar_Parser_Const.effect_Lemma_lid;
            FStar_Syntax_Syntax.result_typ = FStar_Syntax_Syntax.t_unit;
            FStar_Syntax_Syntax.effect_args = uu____1060;
            FStar_Syntax_Syntax.flags = []
          } in
        FStar_Syntax_Syntax.mk_Comp ct
    | FStar_Reflection_Data.C_Eff (us, ef, res, args) ->
        let pack_arg uu____1181 =
          match uu____1181 with
          | (a, q) -> let uu____1200 = pack_aqual q in (a, uu____1200) in
        let ct =
          let uu____1204 = FStar_Ident.lid_of_path ef FStar_Range.dummyRange in
          let uu____1205 = FStar_List.map pack_arg args in
          {
            FStar_Syntax_Syntax.comp_univs = [];
            FStar_Syntax_Syntax.effect_name = uu____1204;
            FStar_Syntax_Syntax.result_typ = res;
            FStar_Syntax_Syntax.effect_args = uu____1205;
            FStar_Syntax_Syntax.flags = []
          } in
        FStar_Syntax_Syntax.mk_Comp ct
let (pack_const : FStar_Reflection_Data.vconst -> FStar_Syntax_Syntax.sconst)
  =
  fun c ->
    match c with
    | FStar_Reflection_Data.C_Unit -> FStar_Const.Const_unit
    | FStar_Reflection_Data.C_Int i ->
        let uu____1230 =
          let uu____1241 = FStar_BigInt.string_of_big_int i in
          (uu____1241, FStar_Pervasives_Native.None) in
        FStar_Const.Const_int uu____1230
    | FStar_Reflection_Data.C_True -> FStar_Const.Const_bool true
    | FStar_Reflection_Data.C_False -> FStar_Const.Const_bool false
    | FStar_Reflection_Data.C_String s ->
        FStar_Const.Const_string (s, FStar_Range.dummyRange)
    | FStar_Reflection_Data.C_Range r -> FStar_Const.Const_range r
    | FStar_Reflection_Data.C_Reify -> FStar_Const.Const_reify
    | FStar_Reflection_Data.C_Reflect ns ->
        let uu____1255 = FStar_Ident.lid_of_path ns FStar_Range.dummyRange in
        FStar_Const.Const_reflect uu____1255
let (pack_ln : FStar_Reflection_Data.term_view -> FStar_Syntax_Syntax.term) =
  fun tv ->
    match tv with
    | FStar_Reflection_Data.Tv_Var bv -> FStar_Syntax_Syntax.bv_to_name bv
    | FStar_Reflection_Data.Tv_BVar bv -> FStar_Syntax_Syntax.bv_to_tm bv
    | FStar_Reflection_Data.Tv_FVar fv -> FStar_Syntax_Syntax.fv_to_tm fv
    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
        let q' = pack_aqual q in FStar_Syntax_Util.mk_app l [(r, q')]
    | FStar_Reflection_Data.Tv_Abs (b, t) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_abs ([b], t, FStar_Pervasives_Native.None))
          t.FStar_Syntax_Syntax.pos
    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ([b], c))
          c.FStar_Syntax_Syntax.pos
    | FStar_Reflection_Data.Tv_Type () -> FStar_Syntax_Util.ktype
    | FStar_Reflection_Data.Tv_Refine (bv, t) ->
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine (bv, t))
          t.FStar_Syntax_Syntax.pos
    | FStar_Reflection_Data.Tv_Const c ->
        let uu____1343 =
          let uu____1344 = pack_const c in
          FStar_Syntax_Syntax.Tm_constant uu____1344 in
        FStar_Syntax_Syntax.mk uu____1343 FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Uvar (u, ctx_u_s) ->
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
          FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (false, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((false, [lb]), t2))
          FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Let (true, attrs, bv, t1, t2) ->
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl bv) []
            bv.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid t1
            attrs FStar_Range.dummyRange in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_let ((true, [lb]), t2))
          FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Match (t, brs) ->
        let wrap v =
          {
            FStar_Syntax_Syntax.v = v;
            FStar_Syntax_Syntax.p = FStar_Range.dummyRange
          } in
        let rec pack_pat p =
          match p with
          | FStar_Reflection_Data.Pat_Constant c ->
              let uu____1406 =
                let uu____1407 = pack_const c in
                FStar_Syntax_Syntax.Pat_constant uu____1407 in
              FStar_All.pipe_left wrap uu____1406
          | FStar_Reflection_Data.Pat_Cons (fv, ps) ->
              let uu____1422 =
                let uu____1423 =
                  let uu____1436 =
                    FStar_List.map
                      (fun uu____1457 ->
                         match uu____1457 with
                         | (p1, b) ->
                             let uu____1468 = pack_pat p1 in (uu____1468, b))
                      ps in
                  (fv, uu____1436) in
                FStar_Syntax_Syntax.Pat_cons uu____1423 in
              FStar_All.pipe_left wrap uu____1422
          | FStar_Reflection_Data.Pat_Var bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_var bv)
          | FStar_Reflection_Data.Pat_Wild bv ->
              FStar_All.pipe_left wrap (FStar_Syntax_Syntax.Pat_wild bv)
          | FStar_Reflection_Data.Pat_Dot_Term (bv, t1) ->
              FStar_All.pipe_left wrap
                (FStar_Syntax_Syntax.Pat_dot_term (bv, t1)) in
        let brs1 =
          FStar_List.map
            (fun uu___2_1514 ->
               match uu___2_1514 with
               | (pat, t1) ->
                   let uu____1531 = pack_pat pat in
                   (uu____1531, FStar_Pervasives_Native.None, t1)) brs in
        FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (t, brs1))
          FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedT (e, t, tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inl t), tacopt), FStar_Pervasives_Native.None))
          FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_AscribedC (e, c, tacopt) ->
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_ascribed
             (e, ((FStar_Util.Inr c), tacopt), FStar_Pervasives_Native.None))
          FStar_Range.dummyRange
    | FStar_Reflection_Data.Tv_Unknown ->
        FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
          FStar_Range.dummyRange
let (compare_bv :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv -> FStar_Order.order) =
  fun x ->
    fun y ->
      let n = FStar_Syntax_Syntax.order_bv x y in
      if n < Prims.int_zero
      then FStar_Order.Lt
      else if n = Prims.int_zero then FStar_Order.Eq else FStar_Order.Gt
let (is_free :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun x -> fun t -> FStar_Syntax_Util.is_free_in x t
let (free_bvs :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv Prims.list) =
  fun t ->
    let uu____1674 = FStar_Syntax_Free.names t in
    FStar_All.pipe_right uu____1674 FStar_Util.set_elements
let (free_uvars : FStar_Syntax_Syntax.term -> FStar_BigInt.t Prims.list) =
  fun t ->
    let uu____1690 =
      let uu____1693 = FStar_Syntax_Free.uvars_uncached t in
      FStar_All.pipe_right uu____1693 FStar_Util.set_elements in
    FStar_All.pipe_right uu____1690
      (FStar_List.map
         (fun u ->
            let uu____1707 =
              FStar_Syntax_Unionfind.uvar_id
                u.FStar_Syntax_Syntax.ctx_uvar_head in
            FStar_BigInt.of_int_fs uu____1707))
let (lookup_attr :
  FStar_Syntax_Syntax.term ->
    FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv Prims.list)
  =
  fun attr ->
    fun env ->
      let uu____1722 =
        let uu____1723 = FStar_Syntax_Subst.compress attr in
        uu____1723.FStar_Syntax_Syntax.n in
      match uu____1722 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let ses =
            let uu____1732 =
              let uu____1733 = FStar_Syntax_Syntax.lid_of_fv fv in
              FStar_Ident.string_of_lid uu____1733 in
            FStar_TypeChecker_Env.lookup_attr env uu____1732 in
          FStar_List.concatMap
            (fun se ->
               let uu____1737 = FStar_Syntax_Util.lid_of_sigelt se in
               match uu____1737 with
               | FStar_Pervasives_Native.None -> []
               | FStar_Pervasives_Native.Some l ->
                   let uu____1743 =
                     FStar_Syntax_Syntax.lid_as_fv l
                       (FStar_Syntax_Syntax.Delta_constant_at_level
                          (Prims.of_int (999))) FStar_Pervasives_Native.None in
                   [uu____1743]) ses
      | uu____1744 -> []
let (all_defs_in_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.fv Prims.list) =
  fun env ->
    let uu____1754 = FStar_TypeChecker_Env.lidents env in
    FStar_List.map
      (fun l ->
         FStar_Syntax_Syntax.lid_as_fv l
           (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (999)))
           FStar_Pervasives_Native.None) uu____1754
let (defs_in_module :
  FStar_TypeChecker_Env.env ->
    FStar_Reflection_Data.name -> FStar_Syntax_Syntax.fv Prims.list)
  =
  fun env ->
    fun modul ->
      let uu____1773 = FStar_TypeChecker_Env.lidents env in
      FStar_List.concatMap
        (fun l ->
           let ns =
             let uu____1781 =
               let uu____1784 = FStar_Ident.ids_of_lid l in
               FStar_All.pipe_right uu____1784 init in
             FStar_All.pipe_right uu____1781
               (FStar_List.map FStar_Ident.string_of_id) in
           if ns = modul
           then
             let uu____1795 =
               FStar_Syntax_Syntax.lid_as_fv l
                 (FStar_Syntax_Syntax.Delta_constant_at_level
                    (Prims.of_int (999))) FStar_Pervasives_Native.None in
             [uu____1795]
           else []) uu____1773
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
      let uu___430_1839 = se in
      {
        FStar_Syntax_Syntax.sigel = (uu___430_1839.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng =
          (uu___430_1839.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals =
          (uu___430_1839.FStar_Syntax_Syntax.sigquals);
        FStar_Syntax_Syntax.sigmeta =
          (uu___430_1839.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = attrs;
        FStar_Syntax_Syntax.sigopts =
          (uu___430_1839.FStar_Syntax_Syntax.sigopts)
      }
let (rd_to_syntax_qual :
  FStar_Reflection_Data.qualifier -> FStar_Syntax_Syntax.qualifier) =
  fun uu___3_1844 ->
    match uu___3_1844 with
    | FStar_Reflection_Data.Assumption -> FStar_Syntax_Syntax.Assumption
    | FStar_Reflection_Data.New -> FStar_Syntax_Syntax.New
    | FStar_Reflection_Data.Private -> FStar_Syntax_Syntax.Private
    | FStar_Reflection_Data.Unfold_for_unification_and_vcgen ->
        FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
    | FStar_Reflection_Data.Visible_default ->
        FStar_Syntax_Syntax.Visible_default
    | FStar_Reflection_Data.Irreducible -> FStar_Syntax_Syntax.Irreducible
    | FStar_Reflection_Data.Inline_for_extraction ->
        FStar_Syntax_Syntax.Inline_for_extraction
    | FStar_Reflection_Data.NoExtract -> FStar_Syntax_Syntax.NoExtract
    | FStar_Reflection_Data.Noeq -> FStar_Syntax_Syntax.Noeq
    | FStar_Reflection_Data.Unopteq -> FStar_Syntax_Syntax.Unopteq
    | FStar_Reflection_Data.TotalEffect -> FStar_Syntax_Syntax.TotalEffect
    | FStar_Reflection_Data.Logic -> FStar_Syntax_Syntax.Logic
    | FStar_Reflection_Data.Reifiable -> FStar_Syntax_Syntax.Reifiable
    | FStar_Reflection_Data.Reflectable l ->
        FStar_Syntax_Syntax.Reflectable l
    | FStar_Reflection_Data.Discriminator l ->
        FStar_Syntax_Syntax.Discriminator l
    | FStar_Reflection_Data.Projector (l, i) ->
        FStar_Syntax_Syntax.Projector (l, i)
    | FStar_Reflection_Data.RecordType (l1, l2) ->
        FStar_Syntax_Syntax.RecordType (l1, l2)
    | FStar_Reflection_Data.RecordConstructor (l1, l2) ->
        FStar_Syntax_Syntax.RecordConstructor (l1, l2)
    | FStar_Reflection_Data.Action l -> FStar_Syntax_Syntax.Action l
    | FStar_Reflection_Data.ExceptionConstructor ->
        FStar_Syntax_Syntax.ExceptionConstructor
    | FStar_Reflection_Data.HasMaskedEffect ->
        FStar_Syntax_Syntax.HasMaskedEffect
    | FStar_Reflection_Data.Effect -> FStar_Syntax_Syntax.Effect
    | FStar_Reflection_Data.OnlyName -> FStar_Syntax_Syntax.OnlyName
let (syntax_to_rd_qual :
  FStar_Syntax_Syntax.qualifier -> FStar_Reflection_Data.qualifier) =
  fun uu___4_1882 ->
    match uu___4_1882 with
    | FStar_Syntax_Syntax.Assumption -> FStar_Reflection_Data.Assumption
    | FStar_Syntax_Syntax.New -> FStar_Reflection_Data.New
    | FStar_Syntax_Syntax.Private -> FStar_Reflection_Data.Private
    | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen ->
        FStar_Reflection_Data.Unfold_for_unification_and_vcgen
    | FStar_Syntax_Syntax.Visible_default ->
        FStar_Reflection_Data.Visible_default
    | FStar_Syntax_Syntax.Irreducible -> FStar_Reflection_Data.Irreducible
    | FStar_Syntax_Syntax.Inline_for_extraction ->
        FStar_Reflection_Data.Inline_for_extraction
    | FStar_Syntax_Syntax.NoExtract -> FStar_Reflection_Data.NoExtract
    | FStar_Syntax_Syntax.Noeq -> FStar_Reflection_Data.Noeq
    | FStar_Syntax_Syntax.Unopteq -> FStar_Reflection_Data.Unopteq
    | FStar_Syntax_Syntax.TotalEffect -> FStar_Reflection_Data.TotalEffect
    | FStar_Syntax_Syntax.Logic -> FStar_Reflection_Data.Logic
    | FStar_Syntax_Syntax.Reifiable -> FStar_Reflection_Data.Reifiable
    | FStar_Syntax_Syntax.Reflectable l ->
        FStar_Reflection_Data.Reflectable l
    | FStar_Syntax_Syntax.Discriminator l ->
        FStar_Reflection_Data.Discriminator l
    | FStar_Syntax_Syntax.Projector (l, i) ->
        FStar_Reflection_Data.Projector (l, i)
    | FStar_Syntax_Syntax.RecordType (l1, l2) ->
        FStar_Reflection_Data.RecordType (l1, l2)
    | FStar_Syntax_Syntax.RecordConstructor (l1, l2) ->
        FStar_Reflection_Data.RecordConstructor (l1, l2)
    | FStar_Syntax_Syntax.Action l -> FStar_Reflection_Data.Action l
    | FStar_Syntax_Syntax.ExceptionConstructor ->
        FStar_Reflection_Data.ExceptionConstructor
    | FStar_Syntax_Syntax.HasMaskedEffect ->
        FStar_Reflection_Data.HasMaskedEffect
    | FStar_Syntax_Syntax.Effect -> FStar_Reflection_Data.Effect
    | FStar_Syntax_Syntax.OnlyName -> FStar_Reflection_Data.OnlyName
let (sigelt_quals :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.qualifier Prims.list) =
  fun se ->
    FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
      (FStar_List.map syntax_to_rd_qual)
let (set_sigelt_quals :
  FStar_Reflection_Data.qualifier Prims.list ->
    FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun quals ->
    fun se ->
      let uu___507_1943 = se in
      let uu____1944 = FStar_List.map rd_to_syntax_qual quals in
      {
        FStar_Syntax_Syntax.sigel = (uu___507_1943.FStar_Syntax_Syntax.sigel);
        FStar_Syntax_Syntax.sigrng =
          (uu___507_1943.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals = uu____1944;
        FStar_Syntax_Syntax.sigmeta =
          (uu___507_1943.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs =
          (uu___507_1943.FStar_Syntax_Syntax.sigattrs);
        FStar_Syntax_Syntax.sigopts =
          (uu___507_1943.FStar_Syntax_Syntax.sigopts)
      }
let (e_optionstate_hook :
  FStar_Options.optionstate FStar_Syntax_Embeddings.embedding
    FStar_Pervasives_Native.option FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (sigelt_opts :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun se ->
    match se.FStar_Syntax_Syntax.sigopts with
    | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
    | FStar_Pervasives_Native.Some o ->
        let uu____1975 =
          let uu____1976 =
            let uu____1983 =
              let uu____1986 = FStar_ST.op_Bang e_optionstate_hook in
              FStar_All.pipe_right uu____1986 FStar_Util.must in
            FStar_Syntax_Embeddings.embed uu____1983 o in
          uu____1976 FStar_Range.dummyRange FStar_Pervasives_Native.None
            FStar_Syntax_Embeddings.id_norm_cb in
        FStar_Pervasives_Native.Some uu____1975
let (inspect_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Reflection_Data.sigelt_view) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let ((r, lb::[]), uu____2022) ->
        let fv =
          match lb.FStar_Syntax_Syntax.lbname with
          | FStar_Util.Inr fv -> fv
          | FStar_Util.Inl uu____2031 ->
              failwith "impossible: global Sig_let has bv" in
        let uu____2032 =
          FStar_Syntax_Subst.univ_var_opening lb.FStar_Syntax_Syntax.lbunivs in
        (match uu____2032 with
         | (s, us) ->
             let typ =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbtyp in
             let def =
               FStar_Syntax_Subst.subst s lb.FStar_Syntax_Syntax.lbdef in
             FStar_Reflection_Data.Sg_Let (r, fv, us, typ, def))
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid, us, param_bs, ty, _mutual, c_lids) ->
        let nm = FStar_Ident.path_of_lid lid in
        let uu____2070 = FStar_Syntax_Subst.univ_var_opening us in
        (match uu____2070 with
         | (s, us1) ->
             let param_bs1 = FStar_Syntax_Subst.subst_binders s param_bs in
             let ty1 = FStar_Syntax_Subst.subst s ty in
             let uu____2091 = FStar_Syntax_Subst.open_term param_bs1 ty1 in
             (match uu____2091 with
              | (param_bs2, ty2) ->
                  let inspect_ctor c_lid =
                    let uu____2104 =
                      let uu____2107 = get_env () in
                      FStar_TypeChecker_Env.lookup_sigelt uu____2107 c_lid in
                    match uu____2104 with
                    | FStar_Pervasives_Native.Some
                        {
                          FStar_Syntax_Syntax.sigel =
                            FStar_Syntax_Syntax.Sig_datacon
                            (lid1, us2, cty, _ty_lid_, nparam, _mutual1);
                          FStar_Syntax_Syntax.sigrng = uu____2114;
                          FStar_Syntax_Syntax.sigquals = uu____2115;
                          FStar_Syntax_Syntax.sigmeta = uu____2116;
                          FStar_Syntax_Syntax.sigattrs = uu____2117;
                          FStar_Syntax_Syntax.sigopts = uu____2118;_}
                        ->
                        let cty1 = FStar_Syntax_Subst.subst s cty in
                        let uu____2130 =
                          let uu____2137 = get_env () in
                          FStar_TypeChecker_Normalize.get_n_binders
                            uu____2137 nparam cty1 in
                        (match uu____2130 with
                         | (param_ctor_bs, c) ->
                             (if (FStar_List.length param_ctor_bs) <> nparam
                              then
                                failwith
                                  "impossible: inspect_sigelt: could not obtain sufficient ctor param binders"
                              else ();
                              (let uu____2147 =
                                 let uu____2148 =
                                   FStar_Syntax_Util.is_total_comp c in
                                 Prims.op_Negation uu____2148 in
                               if uu____2147
                               then
                                 failwith
                                   "impossible: inspect_sigelt: removed parameters and got an effectful comp"
                               else ());
                              (let cty2 = FStar_Syntax_Util.comp_result c in
                               let s' =
                                 FStar_List.map2
                                   (fun b1 ->
                                      fun b2 ->
                                        let uu____2185 =
                                          let uu____2192 =
                                            FStar_Syntax_Syntax.bv_to_name
                                              (FStar_Pervasives_Native.fst b2) in
                                          ((FStar_Pervasives_Native.fst b1),
                                            uu____2192) in
                                        FStar_Syntax_Syntax.NT uu____2185)
                                   param_ctor_bs param_bs2 in
                               let cty3 = FStar_Syntax_Subst.subst s' cty2 in
                               let cty4 = FStar_Syntax_Util.remove_inacc cty3 in
                               let uu____2203 = FStar_Ident.path_of_lid lid1 in
                               (uu____2203, cty4))))
                    | uu____2204 ->
                        failwith
                          "impossible: inspect_sigelt: did not find ctor" in
                  let uu____2207 =
                    let uu____2224 = FStar_List.map inspect_ctor c_lids in
                    (nm, us1, param_bs2, ty2, uu____2224) in
                  FStar_Reflection_Data.Sg_Inductive uu____2207))
    | uu____2233 -> FStar_Reflection_Data.Unk
let (pack_sigelt :
  FStar_Reflection_Data.sigelt_view -> FStar_Syntax_Syntax.sigelt) =
  fun sv ->
    match sv with
    | FStar_Reflection_Data.Sg_Let (r, fv, univs, typ, def) ->
        let s = FStar_Syntax_Subst.univ_var_closing univs in
        let typ1 = FStar_Syntax_Subst.subst s typ in
        let def1 = FStar_Syntax_Subst.subst s def in
        let lb =
          FStar_Syntax_Util.mk_letbinding (FStar_Util.Inr fv) univs typ1
            FStar_Parser_Const.effect_Tot_lid def1 []
            def1.FStar_Syntax_Syntax.pos in
        let uu____2256 =
          let uu____2257 =
            let uu____2264 =
              let uu____2267 = FStar_Syntax_Syntax.lid_of_fv fv in
              [uu____2267] in
            ((r, [lb]), uu____2264) in
          FStar_Syntax_Syntax.Sig_let uu____2257 in
        FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt uu____2256
    | FStar_Reflection_Data.Sg_Inductive (nm, us_names, param_bs, ty, ctors)
        ->
        let ind_lid = FStar_Ident.lid_of_path nm FStar_Range.dummyRange in
        let s = FStar_Syntax_Subst.univ_var_closing us_names in
        let nparam = FStar_List.length param_bs in
        let pack_ctor c =
          let uu____2300 = c in
          match uu____2300 with
          | (nm1, ty1) ->
              let lid = FStar_Ident.lid_of_path nm1 FStar_Range.dummyRange in
              let ty2 =
                let uu____2307 = FStar_Syntax_Syntax.mk_Total ty1 in
                FStar_Syntax_Util.arrow param_bs uu____2307 in
              let ty3 = FStar_Syntax_Subst.subst s ty2 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt
                (FStar_Syntax_Syntax.Sig_datacon
                   (lid, us_names, ty3, ind_lid, nparam, [])) in
        let ctor_ses = FStar_List.map pack_ctor ctors in
        let c_lids =
          FStar_List.map
            (fun se ->
               let uu____2322 = FStar_Syntax_Util.lid_of_sigelt se in
               FStar_Util.must uu____2322) ctor_ses in
        let ind_se =
          let param_bs1 = FStar_Syntax_Subst.close_binders param_bs in
          let ty1 = FStar_Syntax_Subst.close param_bs1 ty in
          let param_bs2 = FStar_Syntax_Subst.subst_binders s param_bs1 in
          let ty2 = FStar_Syntax_Subst.subst s ty1 in
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt
            (FStar_Syntax_Syntax.Sig_inductive_typ
               (ind_lid, us_names, param_bs2, ty2, [], c_lids)) in
        let se =
          FStar_All.pipe_left FStar_Syntax_Syntax.mk_sigelt
            (FStar_Syntax_Syntax.Sig_bundle
               ((ind_se :: ctor_ses), (ind_lid :: c_lids))) in
        let uu___620_2339 = se in
        {
          FStar_Syntax_Syntax.sigel =
            (uu___620_2339.FStar_Syntax_Syntax.sigel);
          FStar_Syntax_Syntax.sigrng =
            (uu___620_2339.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Noeq ::
            (se.FStar_Syntax_Syntax.sigquals));
          FStar_Syntax_Syntax.sigmeta =
            (uu___620_2339.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___620_2339.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___620_2339.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Reflection_Data.Unk -> failwith "packing Unk, sorry"
let (inspect_bv : FStar_Syntax_Syntax.bv -> FStar_Reflection_Data.bv_view) =
  fun bv ->
    let uu____2345 = FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
    let uu____2346 = FStar_BigInt.of_int_fs bv.FStar_Syntax_Syntax.index in
    {
      FStar_Reflection_Data.bv_ppname = uu____2345;
      FStar_Reflection_Data.bv_index = uu____2346;
      FStar_Reflection_Data.bv_sort = (bv.FStar_Syntax_Syntax.sort)
    }
let (pack_bv : FStar_Reflection_Data.bv_view -> FStar_Syntax_Syntax.bv) =
  fun bvv ->
    let uu____2352 =
      FStar_Ident.mk_ident
        ((bvv.FStar_Reflection_Data.bv_ppname), FStar_Range.dummyRange) in
    let uu____2353 =
      FStar_BigInt.to_int_fs bvv.FStar_Reflection_Data.bv_index in
    {
      FStar_Syntax_Syntax.ppname = uu____2352;
      FStar_Syntax_Syntax.index = uu____2353;
      FStar_Syntax_Syntax.sort = (bvv.FStar_Reflection_Data.bv_sort)
    }
let (inspect_binder :
  FStar_Syntax_Syntax.binder ->
    (FStar_Syntax_Syntax.bv * FStar_Reflection_Data.aqualv))
  =
  fun b ->
    let uu____2367 = b in
    match uu____2367 with
    | (bv, aq) -> let uu____2378 = inspect_aqual aq in (bv, uu____2378)
let (pack_binder :
  FStar_Syntax_Syntax.bv ->
    FStar_Reflection_Data.aqualv -> FStar_Syntax_Syntax.binder)
  = fun bv -> fun aqv -> let uu____2389 = pack_aqual aqv in (bv, uu____2389)
let (moduleof : FStar_TypeChecker_Env.env -> Prims.string Prims.list) =
  fun e -> FStar_Ident.path_of_lid e.FStar_TypeChecker_Env.curmodule
let (env_open_modules :
  FStar_TypeChecker_Env.env -> FStar_Reflection_Data.name Prims.list) =
  fun e ->
    let uu____2412 =
      FStar_Syntax_DsEnv.open_modules e.FStar_TypeChecker_Env.dsenv in
    FStar_List.map
      (fun uu____2429 ->
         match uu____2429 with
         | (l, m) ->
             let uu____2438 = FStar_Ident.ids_of_lid l in
             FStar_List.map FStar_Ident.string_of_id uu____2438) uu____2412
let (binders_of_env :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.binders) =
  fun e -> FStar_TypeChecker_Env.all_binders e
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let uu____2456 = FStar_Syntax_Util.un_uinst t1 in
      let uu____2457 = FStar_Syntax_Util.un_uinst t2 in
      FStar_Syntax_Util.term_eq uu____2456 uu____2457
let (term_to_string : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t -> FStar_Syntax_Print.term_to_string t
let (comp_to_string : FStar_Syntax_Syntax.comp -> Prims.string) =
  fun c -> FStar_Syntax_Print.comp_to_string c
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