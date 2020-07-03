open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let uu____26 = FStar_ST.op_Bang tts_f in
    match uu____26 with
    | FStar_Pervasives_Native.None -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid ->
    let uu____85 =
      let uu____86 = FStar_Ident.ns_of_lid lid in
      let uu____89 =
        let uu____92 =
          let uu____93 =
            let uu____99 =
              let uu____101 =
                let uu____103 =
                  let uu____105 = FStar_Ident.ident_of_lid lid in
                  FStar_Ident.string_of_id uu____105 in
                Prims.op_Hat "is_" uu____103 in
              Prims.op_Hat FStar_Ident.reserved_prefix uu____101 in
            let uu____107 = FStar_Ident.range_of_lid lid in
            (uu____99, uu____107) in
          FStar_Ident.mk_ident uu____93 in
        [uu____92] in
      FStar_List.append uu____86 uu____89 in
    FStar_Ident.lid_of_ids uu____85
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    let c =
      let uu____118 =
        let uu____120 = FStar_Ident.ident_of_lid lid in
        FStar_Ident.string_of_id uu____120 in
      FStar_Util.char_at uu____118 Prims.int_zero in
    FStar_Util.is_upper c
let arg_of_non_null_binder :
  'uuuuuu127 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu127) ->
      (FStar_Syntax_Syntax.term * 'uuuuuu127)
  =
  fun uu____140 ->
    match uu____140 with
    | (b, imp) ->
        let uu____147 = FStar_Syntax_Syntax.bv_to_name b in (uu____147, imp)
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b ->
            let uu____199 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____199
            then []
            else (let uu____218 = arg_of_non_null_binder b in [uu____218])))
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders ->
    let uu____253 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b ->
              let uu____335 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____335
              then
                let b1 =
                  let uu____361 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  (uu____361, (FStar_Pervasives_Native.snd b)) in
                let uu____368 = arg_of_non_null_binder b1 in (b1, uu____368)
              else
                (let uu____391 = arg_of_non_null_binder b in (b, uu____391)))) in
    FStar_All.pipe_right uu____253 FStar_List.unzip
let (name_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i ->
            fun b ->
              let uu____525 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____525
              then
                let uu____534 = b in
                match uu____534 with
                | (a, imp) ->
                    let b1 =
                      let uu____554 =
                        let uu____556 = FStar_Util.string_of_int i in
                        Prims.op_Hat "_" uu____556 in
                      FStar_Ident.id_of_text uu____554 in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = Prims.int_zero;
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      } in
                    (b2, imp)
              else b))
let (name_function_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (binders, comp) ->
        let uu____601 =
          let uu____602 =
            let uu____617 = name_binders binders in (uu____617, comp) in
          FStar_Syntax_Syntax.Tm_arrow uu____602 in
        FStar_Syntax_Syntax.mk uu____601 t.FStar_Syntax_Syntax.pos
    | uu____636 -> t
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____673 ->
            match uu____673 with
            | (t, imp) ->
                let uu____684 =
                  let uu____685 = FStar_Syntax_Syntax.null_binder t in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____685 in
                (uu____684, imp)))
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____740 ->
            match uu____740 with
            | (t, imp) ->
                let uu____757 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t in
                (uu____757, imp)))
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs ->
    let uu____770 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____770
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
let mk_subst : 'uuuuuu782 . 'uuuuuu782 -> 'uuuuuu782 Prims.list =
  fun s -> [s]
let (subst_of_list :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.subst_t)
  =
  fun formals ->
    fun actuals ->
      if (FStar_List.length formals) = (FStar_List.length actuals)
      then
        FStar_List.fold_right2
          (fun f ->
             fun a ->
               fun out ->
                 (FStar_Syntax_Syntax.NT
                    ((FStar_Pervasives_Native.fst f),
                      (FStar_Pervasives_Native.fst a)))
                 :: out) formals actuals []
      else failwith "Ill-formed substitution"
let (rename_binders :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t)
  =
  fun replace_xs ->
    fun with_ys ->
      if (FStar_List.length replace_xs) = (FStar_List.length with_ys)
      then
        FStar_List.map2
          (fun uu____908 ->
             fun uu____909 ->
               match (uu____908, uu____909) with
               | ((x, uu____935), (y, uu____937)) ->
                   let uu____958 =
                     let uu____965 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu____965) in
                   FStar_Syntax_Syntax.NT uu____958) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2, uu____981) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2, uu____987, uu____988) -> unmeta e2
    | uu____1029 -> e1
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e', m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____1043 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____1050 -> e1
         | uu____1059 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2, uu____1061, uu____1062) ->
        unmeta_safe e2
    | uu____1103 -> e1
let (unmeta_lift : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____1110 =
      let uu____1111 = FStar_Syntax_Subst.compress t in
      uu____1111.FStar_Syntax_Syntax.n in
    match uu____1110 with
    | FStar_Syntax_Syntax.Tm_meta
        (t1, FStar_Syntax_Syntax.Meta_monadic_lift uu____1115) -> t1
    | uu____1128 -> t
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u ->
    match u with
    | FStar_Syntax_Syntax.U_unknown -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_name uu____1147 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_unif uu____1150 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_max uu____1163 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_zero -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1171 = univ_kernel u1 in
        (match uu____1171 with | (k, n) -> (k, (n + Prims.int_one)))
    | FStar_Syntax_Syntax.U_bvar uu____1188 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u ->
    let uu____1203 = univ_kernel u in FStar_Pervasives_Native.snd uu____1203
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1 ->
    fun u2 ->
      let rec compare_kernel uk1 uk2 =
        match (uk1, uk2) with
        | (FStar_Syntax_Syntax.U_bvar uu____1236, uu____1237) ->
            failwith "Impossible: compare_kernel bvar"
        | (uu____1241, FStar_Syntax_Syntax.U_bvar uu____1242) ->
            failwith "Impossible: compare_kernel bvar"
        | (FStar_Syntax_Syntax.U_succ uu____1246, uu____1247) ->
            failwith "Impossible: compare_kernel succ"
        | (uu____1250, FStar_Syntax_Syntax.U_succ uu____1251) ->
            failwith "Impossible: compare_kernel succ"
        | (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_unknown, uu____1255) -> ~- Prims.int_one
        | (uu____1257, FStar_Syntax_Syntax.U_unknown) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_zero, uu____1260) -> ~- Prims.int_one
        | (uu____1262, FStar_Syntax_Syntax.U_zero) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_name u11, FStar_Syntax_Syntax.U_name u21) ->
            let uu____1266 = FStar_Ident.string_of_id u11 in
            let uu____1268 = FStar_Ident.string_of_id u21 in
            FStar_String.compare uu____1266 uu____1268
        | (FStar_Syntax_Syntax.U_name uu____1270, uu____1271) ->
            ~- Prims.int_one
        | (uu____1273, FStar_Syntax_Syntax.U_name uu____1274) ->
            Prims.int_one
        | (FStar_Syntax_Syntax.U_unif u11, FStar_Syntax_Syntax.U_unif u21) ->
            let uu____1298 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
            let uu____1300 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
            uu____1298 - uu____1300
        | (FStar_Syntax_Syntax.U_unif uu____1302, uu____1303) ->
            ~- Prims.int_one
        | (uu____1315, FStar_Syntax_Syntax.U_unif uu____1316) ->
            Prims.int_one
        | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max us2) ->
            let n1 = FStar_List.length us1 in
            let n2 = FStar_List.length us2 in
            if n1 <> n2
            then n1 - n2
            else
              (let copt =
                 let uu____1344 = FStar_List.zip us1 us2 in
                 FStar_Util.find_map uu____1344
                   (fun uu____1360 ->
                      match uu____1360 with
                      | (u11, u21) ->
                          let c = compare_univs u11 u21 in
                          if c <> Prims.int_zero
                          then FStar_Pervasives_Native.Some c
                          else FStar_Pervasives_Native.None) in
               match copt with
               | FStar_Pervasives_Native.None -> Prims.int_zero
               | FStar_Pervasives_Native.Some c -> c) in
      let uu____1388 = univ_kernel u1 in
      match uu____1388 with
      | (uk1, n1) ->
          let uu____1399 = univ_kernel u2 in
          (match uu____1399 with
           | (uk2, n2) ->
               let uu____1410 = compare_kernel uk1 uk2 in
               (match uu____1410 with
                | uu____1413 when uu____1413 = Prims.int_zero -> n1 - n2
                | n -> n))
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1 ->
    fun u2 ->
      let uu____1428 = compare_univs u1 u2 in uu____1428 = Prims.int_zero
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t ->
    fun r ->
      let uu____1447 =
        let uu____1448 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1448;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        } in
      FStar_Syntax_Syntax.mk_Comp uu____1447
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1468 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1477 ->
        FStar_Parser_Const.effect_GTot_lid
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1500 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1509 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t, u_opt) ->
        let uu____1536 =
          let uu____1537 = FStar_Util.map_opt u_opt (fun x -> [x]) in
          FStar_Util.dflt [] uu____1537 in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1536;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t, u_opt) ->
        let uu____1566 =
          let uu____1567 = FStar_Util.map_opt u_opt (fun x -> [x]) in
          FStar_Util.dflt [] uu____1567 in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1566;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
let (comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflag Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun c ->
    fun f ->
      let uu___239_1603 = c in
      let uu____1604 =
        let uu____1605 =
          let uu___241_1606 = comp_to_comp_typ_nouniv c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___241_1606.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___241_1606.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___241_1606.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___241_1606.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____1605 in
      {
        FStar_Syntax_Syntax.n = uu____1604;
        FStar_Syntax_Syntax.pos = (uu___239_1603.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___239_1603.FStar_Syntax_Syntax.vars)
      }
let (comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu____1646 ->
        failwith "Assertion failed: Computation type without universe"
let (effect_indices_from_repr :
  FStar_Syntax_Syntax.term ->
    Prims.bool ->
      FStar_Range.range ->
        Prims.string -> FStar_Syntax_Syntax.term Prims.list)
  =
  fun repr ->
    fun is_layered ->
      fun r ->
        fun err ->
          let err1 uu____1684 =
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEffect, err) r in
          let repr1 = FStar_Syntax_Subst.compress repr in
          if is_layered
          then
            match repr1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_app (uu____1694, uu____1695::is) ->
                FStar_All.pipe_right is
                  (FStar_List.map FStar_Pervasives_Native.fst)
            | uu____1763 -> err1 ()
          else
            (match repr1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_arrow (uu____1768, c) ->
                 let uu____1790 = FStar_All.pipe_right c comp_to_comp_typ in
                 FStar_All.pipe_right uu____1790
                   (fun ct ->
                      FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                        (FStar_List.map FStar_Pervasives_Native.fst))
             | uu____1825 -> err1 ())
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp, uu____1846)::[] -> wp
      | uu____1871 ->
          let uu____1882 =
            let uu____1884 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name in
            let uu____1886 =
              let uu____1888 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length in
              FStar_All.pipe_right uu____1888 FStar_Util.string_of_int in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              uu____1884 uu____1886 in
          failwith uu____1882 in
    let uu____1912 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____1912, (c.FStar_Syntax_Syntax.result_typ), wp)
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1926 -> true
    | FStar_Syntax_Syntax.GTotal uu____1936 -> false
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1961 ->
               match uu___0_1961 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____1965 -> false)))
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1982 ->
            match uu___1_1982 with
            | FStar_Syntax_Syntax.RETURN -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN -> true
            | uu____1986 -> false))
let (is_tot_or_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
let (is_pure_effect : FStar_Ident.lident -> Prims.bool) =
  fun l ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
let (is_pure_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2018 -> true
    | FStar_Syntax_Syntax.GTotal uu____2028 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_2043 ->
                   match uu___2_2043 with
                   | FStar_Syntax_Syntax.LEMMA -> true
                   | uu____2046 -> false)))
let (is_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
let (is_div_effect : FStar_Ident.lident -> Prims.bool) =
  fun l ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)
let (is_pure_or_ghost_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c))
let (is_pure_or_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l -> (is_pure_effect l) || (is_ghost_effect l)
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____2087 =
      let uu____2088 = FStar_Syntax_Subst.compress t in
      uu____2088.FStar_Syntax_Syntax.n in
    match uu____2087 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2092, c) -> is_pure_or_ghost_comp c
    | uu____2114 -> true
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____2129 -> false
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____2138 =
      let uu____2139 = FStar_Syntax_Subst.compress t in
      uu____2139.FStar_Syntax_Syntax.n in
    match uu____2138 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____2143, c) -> is_lemma_comp c
    | uu____2165 -> false
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____2173 =
      let uu____2174 = FStar_Syntax_Subst.compress t in
      uu____2174.FStar_Syntax_Syntax.n in
    match uu____2173 with
    | FStar_Syntax_Syntax.Tm_app (t1, uu____2178) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1, uu____2204) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2241, t1, uu____2243) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____2269, uu____2270) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____2312) -> head_of t1
    | uu____2317 -> t
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list))
  =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head, args) -> (head, args)
    | uu____2395 -> (t1, [])
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head, args) ->
        let uu____2477 = head_and_args' head in
        (match uu____2477 with
         | (head1, args') -> (head1, (FStar_List.append args' args)))
    | uu____2546 -> (t1, [])
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2, uu____2573) ->
        FStar_Syntax_Subst.compress t2
    | uu____2578 -> t1
let (is_ml_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
           FStar_Parser_Const.effect_ML_lid)
          ||
          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___3_2596 ->
                   match uu___3_2596 with
                   | FStar_Syntax_Syntax.MLEFFECT -> true
                   | uu____2599 -> false)))
    | uu____2601 -> false
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu____2618) -> t
    | FStar_Syntax_Syntax.GTotal (t, uu____2628) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c ->
    fun t ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2657 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2666 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___401_2678 = ct in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___401_2678.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___401_2678.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___401_2678.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___401_2678.FStar_Syntax_Syntax.flags)
             })
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2694 ->
            match uu___4_2694 with
            | FStar_Syntax_Syntax.TOTAL -> true
            | FStar_Syntax_Syntax.RETURN -> true
            | uu____2698 -> false))
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2706 -> []
    | FStar_Syntax_Syntax.GTotal uu____2723 -> []
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.effect_args
let (primops : FStar_Ident.lident Prims.list) =
  [FStar_Parser_Const.op_Eq;
  FStar_Parser_Const.op_notEq;
  FStar_Parser_Const.op_LT;
  FStar_Parser_Const.op_LTE;
  FStar_Parser_Const.op_GT;
  FStar_Parser_Const.op_GTE;
  FStar_Parser_Const.op_Subtraction;
  FStar_Parser_Const.op_Minus;
  FStar_Parser_Const.op_Addition;
  FStar_Parser_Const.op_Multiply;
  FStar_Parser_Const.op_Division;
  FStar_Parser_Const.op_Modulus;
  FStar_Parser_Const.op_And;
  FStar_Parser_Const.op_Or;
  FStar_Parser_Const.op_Negation]
let (is_primop_lid : FStar_Ident.lident -> Prims.bool) =
  fun l ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
let (is_primop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun f ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____2767 -> false
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2, uu____2777, uu____2778) ->
        unascribe e2
    | uu____2819 -> e1
let rec (ascribe :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax) FStar_Util.either
      * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    fun k ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t', uu____2872, uu____2873) ->
          ascribe t' k
      | uu____2914 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            t.FStar_Syntax_Syntax.pos
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i ->
    let uu____2941 =
      let uu____2950 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
      FStar_Util.must uu____2950 in
    uu____2941 i.FStar_Syntax_Syntax.lkind i
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____3006 =
      let uu____3007 = FStar_Syntax_Subst.compress t in
      uu____3007.FStar_Syntax_Syntax.n in
    match uu____3006 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____3011 = unfold_lazy i in
        FStar_All.pipe_left unlazy uu____3011
    | uu____3012 -> t
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____3019 =
      let uu____3020 = FStar_Syntax_Subst.compress t in
      uu____3020.FStar_Syntax_Syntax.n in
    match uu____3019 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____3024 ->
             let uu____3033 = unfold_lazy i in
             FStar_All.pipe_left unlazy uu____3033
         | uu____3034 -> t)
    | uu____3035 -> t
let (eq_lazy_kind :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazy_kind -> Prims.bool)
  =
  fun k ->
    fun k' ->
      match (k, k') with
      | (FStar_Syntax_Syntax.BadLazy, FStar_Syntax_Syntax.BadLazy) -> true
      | (FStar_Syntax_Syntax.Lazy_bv, FStar_Syntax_Syntax.Lazy_bv) -> true
      | (FStar_Syntax_Syntax.Lazy_binder, FStar_Syntax_Syntax.Lazy_binder) ->
          true
      | (FStar_Syntax_Syntax.Lazy_optionstate,
         FStar_Syntax_Syntax.Lazy_optionstate) -> true
      | (FStar_Syntax_Syntax.Lazy_fvar, FStar_Syntax_Syntax.Lazy_fvar) ->
          true
      | (FStar_Syntax_Syntax.Lazy_comp, FStar_Syntax_Syntax.Lazy_comp) ->
          true
      | (FStar_Syntax_Syntax.Lazy_env, FStar_Syntax_Syntax.Lazy_env) -> true
      | (FStar_Syntax_Syntax.Lazy_proofstate,
         FStar_Syntax_Syntax.Lazy_proofstate) -> true
      | (FStar_Syntax_Syntax.Lazy_goal, FStar_Syntax_Syntax.Lazy_goal) ->
          true
      | (FStar_Syntax_Syntax.Lazy_sigelt, FStar_Syntax_Syntax.Lazy_sigelt) ->
          true
      | (FStar_Syntax_Syntax.Lazy_uvar, FStar_Syntax_Syntax.Lazy_uvar) ->
          true
      | uu____3060 -> false
let unlazy_as_t :
  'uuuuuu3073 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuuu3073
  =
  fun k ->
    fun t ->
      let uu____3084 =
        let uu____3085 = FStar_Syntax_Subst.compress t in
        uu____3085.FStar_Syntax_Syntax.n in
      match uu____3084 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____3090;
            FStar_Syntax_Syntax.rng = uu____3091;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____3094 -> failwith "Not a Tm_lazy of the expected kind"
let mk_lazy :
  'a .
    'a ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.lazy_kind ->
          FStar_Range.range FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.term
  =
  fun t ->
    fun typ ->
      fun k ->
        fun r ->
          let rng =
            match r with
            | FStar_Pervasives_Native.Some r1 -> r1
            | FStar_Pervasives_Native.None -> FStar_Range.dummyRange in
          let i =
            let uu____3135 = FStar_Dyn.mkdyn t in
            {
              FStar_Syntax_Syntax.blob = uu____3135;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.ltyp = typ;
              FStar_Syntax_Syntax.rng = rng
            } in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i) rng
let (canon_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term)
  =
  fun t ->
    let uu____3146 =
      let uu____3161 = unascribe t in head_and_args' uu____3161 in
    match uu____3146 with
    | (hd, args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee -> match projectee with | Equal -> true | uu____3193 -> false
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee ->
    match projectee with | NotEqual -> true | uu____3204 -> false
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee ->
    match projectee with | Unknown -> true | uu____3215 -> false
let (injectives : Prims.string Prims.list) =
  ["FStar.Int8.int_to_t";
  "FStar.Int16.int_to_t";
  "FStar.Int32.int_to_t";
  "FStar.Int64.int_to_t";
  "FStar.UInt8.uint_to_t";
  "FStar.UInt16.uint_to_t";
  "FStar.UInt32.uint_to_t";
  "FStar.UInt64.uint_to_t";
  "FStar.Int8.__int_to_t";
  "FStar.Int16.__int_to_t";
  "FStar.Int32.__int_to_t";
  "FStar.Int64.__int_to_t";
  "FStar.UInt8.__uint_to_t";
  "FStar.UInt16.__uint_to_t";
  "FStar.UInt32.__uint_to_t";
  "FStar.UInt64.__uint_to_t"]
let (eq_inj : eq_result -> eq_result -> eq_result) =
  fun f ->
    fun g ->
      match (f, g) with
      | (Equal, Equal) -> Equal
      | (NotEqual, uu____3265) -> NotEqual
      | (uu____3266, NotEqual) -> NotEqual
      | (Unknown, uu____3267) -> Unknown
      | (uu____3268, Unknown) -> Unknown
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1 ->
    fun t2 ->
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      let equal_if uu___5_3373 = if uu___5_3373 then Equal else Unknown in
      let equal_iff uu___6_3384 = if uu___6_3384 then Equal else NotEqual in
      let eq_and f g = match f with | Equal -> g () | uu____3405 -> Unknown in
      let equal_data f1 args1 f2 args2 =
        let uu____3427 = FStar_Syntax_Syntax.fv_eq f1 f2 in
        if uu____3427
        then
          let uu____3431 = FStar_List.zip args1 args2 in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc ->
                  fun uu____3508 ->
                    match uu____3508 with
                    | ((a1, q1), (a2, q2)) ->
                        let uu____3549 = eq_tm a1 a2 in eq_inj acc uu____3549)
               Equal) uu____3431
        else NotEqual in
      let heads_and_args_in_case_both_data =
        let uu____3563 =
          let uu____3580 = FStar_All.pipe_right t11 unmeta in
          FStar_All.pipe_right uu____3580 head_and_args in
        match uu____3563 with
        | (head1, args1) ->
            let uu____3633 =
              let uu____3650 = FStar_All.pipe_right t21 unmeta in
              FStar_All.pipe_right uu____3650 head_and_args in
            (match uu____3633 with
             | (head2, args2) ->
                 let uu____3703 =
                   let uu____3708 =
                     let uu____3709 = un_uinst head1 in
                     uu____3709.FStar_Syntax_Syntax.n in
                   let uu____3712 =
                     let uu____3713 = un_uinst head2 in
                     uu____3713.FStar_Syntax_Syntax.n in
                   (uu____3708, uu____3712) in
                 (match uu____3703 with
                  | (FStar_Syntax_Syntax.Tm_fvar f,
                     FStar_Syntax_Syntax.Tm_fvar g) when
                      (f.FStar_Syntax_Syntax.fv_qual =
                         (FStar_Pervasives_Native.Some
                            FStar_Syntax_Syntax.Data_ctor))
                        &&
                        (g.FStar_Syntax_Syntax.fv_qual =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Data_ctor))
                      -> FStar_Pervasives_Native.Some (f, args1, g, args2)
                  | uu____3740 -> FStar_Pervasives_Native.None)) in
      let t12 = unmeta t11 in
      let t22 = unmeta t21 in
      match ((t12.FStar_Syntax_Syntax.n), (t22.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1, FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3758, uu____3759) ->
          let uu____3760 = unlazy t12 in eq_tm uu____3760 t22
      | (uu____3761, FStar_Syntax_Syntax.Tm_lazy uu____3762) ->
          let uu____3763 = unlazy t22 in eq_tm t12 uu____3763
      | (FStar_Syntax_Syntax.Tm_name a, FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3766 = FStar_Syntax_Syntax.bv_eq a b in
          equal_if uu____3766
      | uu____3768 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3792 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must in
          FStar_All.pipe_right uu____3792
            (fun uu____3840 ->
               match uu____3840 with
               | (f, args1, g, args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3855 = FStar_Syntax_Syntax.fv_eq f g in
          equal_if uu____3855
      | (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst
         (g, vs)) ->
          let uu____3869 = eq_tm f g in
          eq_and uu____3869
            (fun uu____3872 ->
               let uu____3873 = eq_univs_list us vs in equal_if uu____3873)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3875), uu____3876) -> Unknown
      | (uu____3877, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3878)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
         d) ->
          let uu____3881 = FStar_Const.eq_const c d in equal_iff uu____3881
      | (FStar_Syntax_Syntax.Tm_uvar (u1, ([], uu____3884)),
         FStar_Syntax_Syntax.Tm_uvar (u2, ([], uu____3886))) ->
          let uu____3915 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head in
          equal_if uu____3915
      | (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app
         (h2, args2)) ->
          let uu____3969 =
            let uu____3974 =
              let uu____3975 = un_uinst h1 in
              uu____3975.FStar_Syntax_Syntax.n in
            let uu____3978 =
              let uu____3979 = un_uinst h2 in
              uu____3979.FStar_Syntax_Syntax.n in
            (uu____3974, uu____3978) in
          (match uu____3969 with
           | (FStar_Syntax_Syntax.Tm_fvar f1, FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3985 =
                    let uu____3987 = FStar_Syntax_Syntax.lid_of_fv f1 in
                    FStar_Ident.string_of_lid uu____3987 in
                  FStar_List.mem uu____3985 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3989 ->
               let uu____3994 = eq_tm h1 h2 in
               eq_and uu____3994 (fun uu____3996 -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t13, bs1),
         FStar_Syntax_Syntax.Tm_match (t23, bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____4102 = FStar_List.zip bs1 bs2 in
            let uu____4165 = eq_tm t13 t23 in
            FStar_List.fold_right
              (fun uu____4202 ->
                 fun a ->
                   match uu____4202 with
                   | (b1, b2) ->
                       eq_and a (fun uu____4295 -> branch_matches b1 b2))
              uu____4102 uu____4165
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u, FStar_Syntax_Syntax.Tm_type v) ->
          let uu____4300 = eq_univs u v in equal_if uu____4300
      | (FStar_Syntax_Syntax.Tm_quoted (t13, q1),
         FStar_Syntax_Syntax.Tm_quoted (t23, q2)) ->
          let uu____4314 = eq_quoteinfo q1 q2 in
          eq_and uu____4314 (fun uu____4316 -> eq_tm t13 t23)
      | (FStar_Syntax_Syntax.Tm_refine (t13, phi1),
         FStar_Syntax_Syntax.Tm_refine (t23, phi2)) ->
          let uu____4329 =
            eq_tm t13.FStar_Syntax_Syntax.sort t23.FStar_Syntax_Syntax.sort in
          eq_and uu____4329 (fun uu____4331 -> eq_tm phi1 phi2)
      | uu____4332 -> Unknown
and (eq_quoteinfo :
  FStar_Syntax_Syntax.quoteinfo -> FStar_Syntax_Syntax.quoteinfo -> eq_result)
  =
  fun q1 ->
    fun q2 ->
      if q1.FStar_Syntax_Syntax.qkind <> q2.FStar_Syntax_Syntax.qkind
      then NotEqual
      else
        eq_antiquotes q1.FStar_Syntax_Syntax.antiquotes
          q2.FStar_Syntax_Syntax.antiquotes
and (eq_antiquotes :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) Prims.list -> eq_result)
  =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | ([], []) -> Equal
      | ([], uu____4404) -> NotEqual
      | (uu____4435, []) -> NotEqual
      | ((x1, t1)::a11, (x2, t2)::a21) ->
          let uu____4524 =
            let uu____4526 = FStar_Syntax_Syntax.bv_eq x1 x2 in
            Prims.op_Negation uu____4526 in
          if uu____4524
          then NotEqual
          else
            (let uu____4531 = eq_tm t1 t2 in
             match uu____4531 with
             | NotEqual -> NotEqual
             | Unknown ->
                 let uu____4532 = eq_antiquotes a11 a21 in
                 (match uu____4532 with
                  | NotEqual -> NotEqual
                  | uu____4533 -> Unknown)
             | Equal -> eq_antiquotes a11 a21)
and (branch_matches :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) -> eq_result)
  =
  fun b1 ->
    fun b2 ->
      let related_by f o1 o2 =
        match (o1, o2) with
        | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
            true
        | (FStar_Pervasives_Native.Some x, FStar_Pervasives_Native.Some y) ->
            f x y
        | (uu____4617, uu____4618) -> false in
      let uu____4628 = b1 in
      match uu____4628 with
      | (p1, w1, t1) ->
          let uu____4662 = b2 in
          (match uu____4662 with
           | (p2, w2, t2) ->
               let uu____4696 = FStar_Syntax_Syntax.eq_pat p1 p2 in
               if uu____4696
               then
                 let uu____4699 =
                   (let uu____4703 = eq_tm t1 t2 in uu____4703 = Equal) &&
                     (related_by
                        (fun t11 ->
                           fun t21 ->
                             let uu____4712 = eq_tm t11 t21 in
                             uu____4712 = Equal) w1 w2) in
                 (if uu____4699 then Equal else Unknown)
               else Unknown)
and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | ([], []) -> Equal
      | ((a, uu____4777)::a11, (b, uu____4780)::b1) ->
          let uu____4854 = eq_tm a b in
          (match uu____4854 with
           | Equal -> eq_args a11 b1
           | uu____4855 -> Unknown)
      | uu____4856 -> Unknown
and (eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool)
  =
  fun us ->
    fun vs ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)
let (eq_aqual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      eq_result)
  =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) -> Equal
      | (FStar_Pervasives_Native.None, uu____4911) -> NotEqual
      | (uu____4918, FStar_Pervasives_Native.None) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b1),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2)) when
          b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t1)),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_tac t2))) -> eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t1)),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         (FStar_Syntax_Syntax.Arg_qualifier_meta_attr t2))) -> eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality),
         FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)) ->
          Equal
      | uu____4958 -> NotEqual
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x, uu____4975) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____4981, uu____4982) ->
        unrefine t2
    | uu____5023 -> t1
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____5031 =
      let uu____5032 = FStar_Syntax_Subst.compress t in
      uu____5032.FStar_Syntax_Syntax.n in
    match uu____5031 with
    | FStar_Syntax_Syntax.Tm_uvar uu____5036 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu____5051) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____5056 ->
        let uu____5073 =
          let uu____5074 = FStar_All.pipe_right t head_and_args in
          FStar_All.pipe_right uu____5074 FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____5073 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____5137, uu____5138) ->
        is_uvar t1
    | uu____5179 -> false
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____5188 =
      let uu____5189 = unrefine t in uu____5189.FStar_Syntax_Syntax.n in
    match uu____5188 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head, uu____5195) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu____5221) -> is_unit t1
    | uu____5226 -> false
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____5235 =
      let uu____5236 = FStar_Syntax_Subst.compress t in
      uu____5236.FStar_Syntax_Syntax.n in
    match uu____5235 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____5241 -> false
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    let uu____5250 =
      let uu____5251 = FStar_Syntax_Subst.compress e in
      uu____5251.FStar_Syntax_Syntax.n in
    match uu____5250 with
    | FStar_Syntax_Syntax.Tm_abs uu____5255 -> true
    | uu____5275 -> false
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____5284 =
      let uu____5285 = FStar_Syntax_Subst.compress t in
      uu____5285.FStar_Syntax_Syntax.n in
    match uu____5284 with
    | FStar_Syntax_Syntax.Tm_arrow uu____5289 -> true
    | uu____5305 -> false
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x, uu____5315) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____5321, uu____5322) ->
        pre_typ t2
    | uu____5363 -> t1
let (destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list FStar_Pervasives_Native.option)
  =
  fun typ ->
    fun lid ->
      let typ1 = FStar_Syntax_Subst.compress typ in
      let uu____5388 =
        let uu____5389 = un_uinst typ1 in uu____5389.FStar_Syntax_Syntax.n in
      match uu____5388 with
      | FStar_Syntax_Syntax.Tm_app (head, args) ->
          let head1 = un_uinst head in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5454 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5484 -> FStar_Pervasives_Native.None
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5505, lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids, uu____5512) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5517, lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid, uu____5528, uu____5529, uu____5530, uu____5531, uu____5532) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid, uu____5542, uu____5543, uu____5544, uu____5545) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid, uu____5551, uu____5552, uu____5553, uu____5554, uu____5555) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____5563, uu____5564) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid, uu____5566, uu____5567) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5569 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5570 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5571 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5584 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____5595 -> []
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5617 -> FStar_Pervasives_Native.None
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x -> x.FStar_Syntax_Syntax.sigquals
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x -> x.FStar_Syntax_Syntax.sigrng
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5643 ->
    match uu___7_5643 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let range_of_arg :
  'uuuuuu5657 'uuuuuu5658 .
    ('uuuuuu5657 FStar_Syntax_Syntax.syntax * 'uuuuuu5658) ->
      FStar_Range.range
  =
  fun uu____5669 ->
    match uu____5669 with | (hd, uu____5677) -> hd.FStar_Syntax_Syntax.pos
let range_of_args :
  'uuuuuu5691 'uuuuuu5692 .
    ('uuuuuu5691 FStar_Syntax_Syntax.syntax * 'uuuuuu5692) Prims.list ->
      FStar_Range.range -> FStar_Range.range
  =
  fun args ->
    fun r ->
      FStar_All.pipe_right args
        (FStar_List.fold_left
           (fun r1 -> fun a -> FStar_Range.union_ranges r1 (range_of_arg a))
           r)
let (mk_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f ->
    fun args ->
      match args with
      | [] -> f
      | uu____5790 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args)) r
let (mk_app_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f ->
    fun bs ->
      let uu____5849 =
        FStar_List.map
          (fun uu____5876 ->
             match uu____5876 with
             | (bv, aq) ->
                 let uu____5895 = FStar_Syntax_Syntax.bv_to_name bv in
                 (uu____5895, aq)) bs in
      mk_app f uu____5849
let (field_projector_prefix : Prims.string) = "__proj__"
let (field_projector_sep : Prims.string) = "__item__"
let (field_projector_contains_constructor : Prims.string -> Prims.bool) =
  fun s -> FStar_Util.starts_with s field_projector_prefix
let (mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string) =
  fun constr ->
    fun field ->
      Prims.op_Hat field_projector_prefix
        (Prims.op_Hat constr (Prims.op_Hat field_projector_sep field))
let (mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun lid ->
    fun i ->
      let itext = FStar_Ident.string_of_id i in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          (let uu____5946 =
             let uu____5952 =
               let uu____5954 =
                 let uu____5956 = FStar_Ident.ident_of_lid lid in
                 FStar_Ident.string_of_id uu____5956 in
               mk_field_projector_name_from_string uu____5954 itext in
             let uu____5957 = FStar_Ident.range_of_id i in
             (uu____5952, uu____5957) in
           FStar_Ident.mk_ident uu____5946) in
      let uu____5959 =
        let uu____5960 = FStar_Ident.ns_of_lid lid in
        FStar_List.append uu____5960 [newi] in
      FStar_Ident.lid_of_ids uu____5959
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid ->
    fun x ->
      fun i ->
        let nm =
          let uu____5982 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____5982
          then
            let uu____5985 =
              let uu____5991 =
                let uu____5993 = FStar_Util.string_of_int i in
                Prims.op_Hat "_" uu____5993 in
              let uu____5996 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____5991, uu____5996) in
            FStar_Ident.mk_ident uu____5985
          else x.FStar_Syntax_Syntax.ppname in
        mk_field_projector_name_from_ident lid nm
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses, uu____6011) -> ses
    | uu____6020 -> failwith "ses_of_sigbundle: not a Sig_bundle"
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv ->
    fun t ->
      let uu____6035 = FStar_Syntax_Unionfind.find uv in
      match uu____6035 with
      | FStar_Pervasives_Native.Some uu____6038 ->
          let uu____6039 =
            let uu____6041 =
              let uu____6043 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____6043 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____6041 in
          failwith uu____6039
      | uu____6048 -> FStar_Syntax_Unionfind.change uv t
let (qualifier_equal :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun q1 ->
    fun q2 ->
      match (q1, q2) with
      | (FStar_Syntax_Syntax.Discriminator l1,
         FStar_Syntax_Syntax.Discriminator l2) ->
          FStar_Ident.lid_equals l1 l2
      | (FStar_Syntax_Syntax.Projector (l1a, l1b),
         FStar_Syntax_Syntax.Projector (l2a, l2b)) ->
          (FStar_Ident.lid_equals l1a l2a) &&
            (let uu____6072 = FStar_Ident.string_of_id l1b in
             let uu____6074 = FStar_Ident.string_of_id l2b in
             uu____6072 = uu____6074)
      | (FStar_Syntax_Syntax.RecordType (ns1, f1),
         FStar_Syntax_Syntax.RecordType (ns2, f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1 ->
                    fun x2 ->
                      let uu____6103 = FStar_Ident.string_of_id x1 in
                      let uu____6105 = FStar_Ident.string_of_id x2 in
                      uu____6103 = uu____6105) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1 ->
                  fun x2 ->
                    let uu____6114 = FStar_Ident.string_of_id x1 in
                    let uu____6116 = FStar_Ident.string_of_id x2 in
                    uu____6114 = uu____6116) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor (ns1, f1),
         FStar_Syntax_Syntax.RecordConstructor (ns2, f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1 ->
                    fun x2 ->
                      let uu____6145 = FStar_Ident.string_of_id x1 in
                      let uu____6147 = FStar_Ident.string_of_id x2 in
                      uu____6145 = uu____6147) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1 ->
                  fun x2 ->
                    let uu____6156 = FStar_Ident.string_of_id x1 in
                    let uu____6158 = FStar_Ident.string_of_id x2 in
                    uu____6156 = uu____6158) f1 f2)
      | uu____6161 -> q1 = q2
let (abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun t ->
      fun lopt ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu____6207 =
                let uu___1040_6208 = rc in
                let uu____6209 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs) in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1040_6208.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____6209;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1040_6208.FStar_Syntax_Syntax.residual_flags)
                } in
              FStar_Pervasives_Native.Some uu____6207 in
        match bs with
        | [] -> t
        | uu____6226 ->
            let body =
              let uu____6228 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____6228 in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt') ->
                 let uu____6258 =
                   let uu____6259 =
                     let uu____6278 =
                       let uu____6287 = FStar_Syntax_Subst.close_binders bs in
                       FStar_List.append uu____6287 bs' in
                     let uu____6302 = close_lopt lopt' in
                     (uu____6278, t1, uu____6302) in
                   FStar_Syntax_Syntax.Tm_abs uu____6259 in
                 FStar_Syntax_Syntax.mk uu____6258 t1.FStar_Syntax_Syntax.pos
             | uu____6317 ->
                 let uu____6318 =
                   let uu____6319 =
                     let uu____6338 = FStar_Syntax_Subst.close_binders bs in
                     let uu____6347 = close_lopt lopt in
                     (uu____6338, body, uu____6347) in
                   FStar_Syntax_Syntax.Tm_abs uu____6319 in
                 FStar_Syntax_Syntax.mk uu____6318 t.FStar_Syntax_Syntax.pos)
let (arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun c ->
      match bs with
      | [] -> comp_result c
      | uu____6403 ->
          let uu____6412 =
            let uu____6413 =
              let uu____6428 = FStar_Syntax_Subst.close_binders bs in
              let uu____6437 = FStar_Syntax_Subst.close_comp bs c in
              (uu____6428, uu____6437) in
            FStar_Syntax_Syntax.Tm_arrow uu____6413 in
          FStar_Syntax_Syntax.mk uu____6412 c.FStar_Syntax_Syntax.pos
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun c ->
      let t = arrow bs c in
      let uu____6486 =
        let uu____6487 = FStar_Syntax_Subst.compress t in
        uu____6487.FStar_Syntax_Syntax.n in
      match uu____6486 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1, c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres, uu____6517) ->
               let uu____6526 =
                 let uu____6527 = FStar_Syntax_Subst.compress tres in
                 uu____6527.FStar_Syntax_Syntax.n in
               (match uu____6526 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      t.FStar_Syntax_Syntax.pos
                | uu____6570 -> t)
           | uu____6571 -> t)
      | uu____6572 -> t
let rec (canon_arrow :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu____6585 =
      let uu____6586 = FStar_Syntax_Subst.compress t in
      uu____6586.FStar_Syntax_Syntax.n in
    match uu____6585 with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let cn =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Total (t1, u) ->
              let uu____6624 =
                let uu____6633 = canon_arrow t1 in (uu____6633, u) in
              FStar_Syntax_Syntax.Total uu____6624
          | uu____6640 -> c.FStar_Syntax_Syntax.n in
        let c1 =
          let uu___1084_6644 = c in
          {
            FStar_Syntax_Syntax.n = cn;
            FStar_Syntax_Syntax.pos =
              (uu___1084_6644.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1084_6644.FStar_Syntax_Syntax.vars)
          } in
        flat_arrow bs c1
    | uu____6647 -> t
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b ->
    fun t ->
      let uu____6665 =
        let uu____6666 =
          let uu____6673 =
            let uu____6676 =
              let uu____6677 = FStar_Syntax_Syntax.mk_binder b in
              [uu____6677] in
            FStar_Syntax_Subst.close uu____6676 t in
          (b, uu____6673) in
        FStar_Syntax_Syntax.Tm_refine uu____6666 in
      let uu____6698 =
        let uu____6699 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____6699 t.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk uu____6665 uu____6698
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b -> FStar_Syntax_Subst.close_branch b
let (has_decreases : FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____6715 =
          FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
            (FStar_Util.find_opt
               (fun uu___8_6724 ->
                  match uu___8_6724 with
                  | FStar_Syntax_Syntax.DECREASES uu____6726 -> true
                  | uu____6730 -> false)) in
        (match uu____6715 with
         | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES d) ->
             true
         | uu____6737 -> false)
    | uu____6741 -> false
let rec (arrow_formals_comp_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____6796 =
          (is_total_comp c) &&
            (let uu____6799 = has_decreases c in Prims.op_Negation uu____6799) in
        if uu____6796
        then
          let uu____6814 = arrow_formals_comp_ln (comp_result c) in
          (match uu____6814 with
           | (bs', k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6881;
           FStar_Syntax_Syntax.index = uu____6882;
           FStar_Syntax_Syntax.sort = s;_},
         uu____6884)
        ->
        let rec aux s1 k2 =
          let uu____6915 =
            let uu____6916 = FStar_Syntax_Subst.compress s1 in
            uu____6916.FStar_Syntax_Syntax.n in
          match uu____6915 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6931 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6946;
                 FStar_Syntax_Syntax.index = uu____6947;
                 FStar_Syntax_Syntax.sort = s2;_},
               uu____6949)
              -> aux s2 k2
          | uu____6957 ->
              let uu____6958 = FStar_Syntax_Syntax.mk_Total k2 in
              ([], uu____6958) in
        aux s k1
    | uu____6973 ->
        let uu____6974 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____6974)
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k ->
    let uu____6999 = arrow_formals_comp_ln k in
    match uu____6999 with | (bs, c) -> FStar_Syntax_Subst.open_comp bs c
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k ->
    let uu____7054 = arrow_formals_comp_ln k in
    match uu____7054 with | (bs, c) -> (bs, (comp_result c))
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k ->
    let uu____7121 = arrow_formals_comp k in
    match uu____7121 with | (bs, c) -> (bs, (comp_result c))
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____7223 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____7223 with
           | (bs1, c1) ->
               let ct = comp_to_comp_typ c1 in
               let uu____7247 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___9_7256 ->
                         match uu___9_7256 with
                         | FStar_Syntax_Syntax.DECREASES uu____7258 -> true
                         | uu____7262 -> false)) in
               (match uu____7247 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____7297 ->
                    let uu____7300 = is_total_comp c1 in
                    if uu____7300
                    then
                      let uu____7319 = arrow_until_decreases (comp_result c1) in
                      (match uu____7319 with
                       | (bs', d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____7412;
             FStar_Syntax_Syntax.index = uu____7413;
             FStar_Syntax_Syntax.sort = k2;_},
           uu____7415)
          -> arrow_until_decreases k2
      | uu____7423 -> ([], FStar_Pervasives_Native.None) in
    let uu____7444 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp in
    match uu____7444 with
    | (bs, dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs in
        let uu____7498 =
          FStar_Util.map_opt dopt
            (fun d ->
               let d_bvs = FStar_Syntax_Free.names d in
               let uu____7519 =
                 FStar_Common.tabulate n_univs (fun uu____7525 -> false) in
               let uu____7528 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____7553 ->
                         match uu____7553 with
                         | (x, uu____7562) -> FStar_Util.set_mem x d_bvs)) in
               FStar_List.append uu____7519 uu____7528) in
        ((n_univs + (FStar_List.length bs)), uu____7498)
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7618 =
            let uu___1194_7619 = rc in
            let uu____7620 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1194_7619.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7620;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1194_7619.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____7618
      | uu____7629 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____7663 =
        let uu____7664 =
          let uu____7667 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____7667 in
        uu____7664.FStar_Syntax_Syntax.n in
      match uu____7663 with
      | FStar_Syntax_Syntax.Tm_abs (bs, t2, what) ->
          let uu____7713 = aux t2 what in
          (match uu____7713 with
           | (bs', t3, what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7785 -> ([], t1, abs_body_lcomp) in
    let uu____7802 = aux t FStar_Pervasives_Native.None in
    match uu____7802 with
    | (bs, t1, abs_body_lcomp) ->
        let uu____7850 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____7850 with
         | (bs1, t2, opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp in
             (bs1, t2, abs_body_lcomp1))
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let no_acc uu____7884 =
      match uu____7884 with
      | (b, aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true)) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7898 -> aq in
          (b, aq1) in
    let uu____7903 = arrow_formals_comp_ln t in
    match uu____7903 with
    | (bs, c) ->
        (match bs with
         | [] -> t
         | uu____7940 ->
             let uu____7949 =
               let uu____7950 =
                 let uu____7965 = FStar_List.map no_acc bs in (uu____7965, c) in
               FStar_Syntax_Syntax.Tm_arrow uu____7950 in
             FStar_Syntax_Syntax.mk uu____7949 t.FStar_Syntax_Syntax.pos)
let (mk_letbinding :
  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
              -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun lbname ->
    fun univ_vars ->
      fun typ ->
        fun eff ->
          fun def ->
            fun lbattrs ->
              fun pos ->
                {
                  FStar_Syntax_Syntax.lbname = lbname;
                  FStar_Syntax_Syntax.lbunivs = univ_vars;
                  FStar_Syntax_Syntax.lbtyp = typ;
                  FStar_Syntax_Syntax.lbeff = eff;
                  FStar_Syntax_Syntax.lbdef = def;
                  FStar_Syntax_Syntax.lbattrs = lbattrs;
                  FStar_Syntax_Syntax.lbpos = pos
                }
let (close_univs_and_mk_letbinding :
  FStar_Syntax_Syntax.fv Prims.list FStar_Pervasives_Native.option ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun recs ->
    fun lbname ->
      fun univ_vars ->
        fun typ ->
          fun eff ->
            fun def ->
              fun attrs ->
                fun pos ->
                  let def1 =
                    match (recs, univ_vars) with
                    | (FStar_Pervasives_Native.None, uu____8136) -> def
                    | (uu____8147, []) -> def
                    | (FStar_Pervasives_Native.Some fvs, uu____8159) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____8175 ->
                                  FStar_Syntax_Syntax.U_name uu____8175)) in
                        let inst =
                          FStar_All.pipe_right fvs
                            (FStar_List.map
                               (fun fv ->
                                  (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                    universes))) in
                        FStar_Syntax_InstFV.instantiate inst def in
                  let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ in
                  let def2 =
                    FStar_Syntax_Subst.close_univ_vars univ_vars def1 in
                  mk_letbinding lbname univ_vars typ1 eff def2 attrs pos
let (open_univ_vars_binders_and_comp :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
        (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
          Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun uvs ->
    fun binders ->
      fun c ->
        match binders with
        | [] ->
            let uu____8257 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____8257 with | (uvs1, c1) -> (uvs1, [], c1))
        | uu____8292 ->
            let t' = arrow binders c in
            let uu____8304 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____8304 with
             | (uvs1, t'1) ->
                 let uu____8325 =
                   let uu____8326 = FStar_Syntax_Subst.compress t'1 in
                   uu____8326.FStar_Syntax_Syntax.n in
                 (match uu____8325 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                      (uvs1, binders1, c1)
                  | uu____8375 -> failwith "Impossible"))
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____8400 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        FStar_Parser_Const.is_tuple_constructor_string uu____8400
    | uu____8402 -> false
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____8413 -> false
let (is_lid_equality : FStar_Ident.lident -> Prims.bool) =
  fun x -> FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid
let (is_forall : FStar_Ident.lident -> Prims.bool) =
  fun lid -> FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid
let (is_exists : FStar_Ident.lident -> Prims.bool) =
  fun lid -> FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid
let (is_qlid : FStar_Ident.lident -> Prims.bool) =
  fun lid -> (is_forall lid) || (is_exists lid)
let (is_equality :
  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun x -> is_lid_equality x.FStar_Syntax_Syntax.v
let (lid_is_connective : FStar_Ident.lident -> Prims.bool) =
  let lst =
    [FStar_Parser_Const.and_lid;
    FStar_Parser_Const.or_lid;
    FStar_Parser_Const.not_lid;
    FStar_Parser_Const.iff_lid;
    FStar_Parser_Const.imp_lid] in
  fun lid -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst
let (is_constructor :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t ->
    fun lid ->
      let uu____8476 =
        let uu____8477 = pre_typ t in uu____8477.FStar_Syntax_Syntax.n in
      match uu____8476 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____8482 -> false
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t ->
    fun lid ->
      let uu____8496 =
        let uu____8497 = pre_typ t in uu____8497.FStar_Syntax_Syntax.n in
      match uu____8496 with
      | FStar_Syntax_Syntax.Tm_fvar uu____8501 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1, uu____8503) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1, uu____8529) ->
          is_constructed_typ t1 lid
      | uu____8534 -> false
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____8547 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____8548 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____8549 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2, uu____8551) -> get_tycon t2
    | uu____8576 -> FStar_Pervasives_Native.None
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____8584 =
      let uu____8585 = un_uinst t in uu____8585.FStar_Syntax_Syntax.n in
    match uu____8584 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____8590 -> false
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md ->
    let path = FStar_Ident.path_of_lid md in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____8604 =
        let uu____8608 = FStar_List.splitAt (Prims.of_int (2)) path in
        FStar_Pervasives_Native.fst uu____8608 in
      match uu____8604 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8640 -> false
    else false
let (ktype : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Range.dummyRange
let (ktype0 : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Range.dummyRange
let (type_u :
  unit -> (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe)) =
  fun uu____8659 ->
    let u =
      let uu____8665 =
        FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange in
      FStar_All.pipe_left
        (fun uu____8686 -> FStar_Syntax_Syntax.U_unif uu____8686) uu____8665 in
    let uu____8687 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Range.dummyRange in
    (uu____8687, u)
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a ->
    fun a' ->
      let uu____8700 = eq_tm a a' in
      match uu____8700 with | Equal -> true | uu____8703 -> false
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8708 =
    let uu____8709 =
      let uu____8710 =
        FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
          FStar_Range.dummyRange in
      FStar_Syntax_Syntax.lid_as_fv uu____8710
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Syntax.Tm_fvar uu____8709 in
  FStar_Syntax_Syntax.mk uu____8708 FStar_Range.dummyRange
let (exp_true_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Range.dummyRange
let (exp_false_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Range.dummyRange
let (exp_unit : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Range.dummyRange
let (exp_int : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Range.dummyRange
let (exp_char : FStar_BaseTypes.char -> FStar_Syntax_Syntax.term) =
  fun c ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c))
      FStar_Range.dummyRange
let (exp_string : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Range.dummyRange
let (fvar_const : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
      FStar_Pervasives_Native.None
let (tand : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.and_lid
let (tor : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.or_lid
let (timp : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
    FStar_Pervasives_Native.None
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (2)))
    FStar_Pervasives_Native.None
let (t_bool : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.bool_lid
let (b2t_v : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.b2t_lid
let (t_not : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.not_lid
let (t_false : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.false_lid
let (t_true : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.true_lid
let (tac_opaque_attr : FStar_Syntax_Syntax.term) = exp_string "tac_opaque"
let (dm4f_bind_range_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.dm4f_bind_range_attr
let (tcdecltime_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.tcdecltime_attr
let (inline_let_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.inline_let_attr
let (rename_let_attr : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.rename_let_attr
let (t_ctx_uvar_and_sust : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.ctx_uvar_and_subst_lid
let (mk_conj_opt :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun phi1 ->
    fun phi2 ->
      match phi1 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____8823 =
            let uu____8826 =
              let uu____8827 =
                let uu____8844 =
                  let uu____8855 = FStar_Syntax_Syntax.as_arg phi11 in
                  let uu____8864 =
                    let uu____8875 = FStar_Syntax_Syntax.as_arg phi2 in
                    [uu____8875] in
                  uu____8855 :: uu____8864 in
                (tand, uu____8844) in
              FStar_Syntax_Syntax.Tm_app uu____8827 in
            let uu____8920 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            FStar_Syntax_Syntax.mk uu____8826 uu____8920 in
          FStar_Pervasives_Native.Some uu____8823
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t ->
    fun phi1 ->
      fun phi2 ->
        let uu____8953 =
          let uu____8954 =
            let uu____8971 =
              let uu____8982 = FStar_Syntax_Syntax.as_arg phi1 in
              let uu____8991 =
                let uu____9002 = FStar_Syntax_Syntax.as_arg phi2 in
                [uu____9002] in
              uu____8982 :: uu____8991 in
            (op_t, uu____8971) in
          FStar_Syntax_Syntax.Tm_app uu____8954 in
        let uu____9047 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Syntax.mk uu____8953 uu____9047
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi ->
    let uu____9060 =
      let uu____9061 =
        let uu____9078 =
          let uu____9089 = FStar_Syntax_Syntax.as_arg phi in [uu____9089] in
        (t_not, uu____9078) in
      FStar_Syntax_Syntax.Tm_app uu____9061 in
    FStar_Syntax_Syntax.mk uu____9060 phi.FStar_Syntax_Syntax.pos
let (mk_conj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1 -> fun phi2 -> mk_binop tand phi1 phi2
let (mk_conj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
    | hd::tl -> FStar_List.fold_right mk_conj tl hd
let (mk_disj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1 -> fun phi2 -> mk_binop tor phi1 phi2
let (mk_disj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi ->
    match phi with
    | [] -> t_false
    | hd::tl -> FStar_List.fold_right mk_disj tl hd
let (mk_imp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1 -> fun phi2 -> mk_binop timp phi1 phi2
let (mk_iff :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1 -> fun phi2 -> mk_binop tiff phi1 phi2
let (b2t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e ->
    let uu____9286 =
      let uu____9287 =
        let uu____9304 =
          let uu____9315 = FStar_Syntax_Syntax.as_arg e in [uu____9315] in
        (b2t_v, uu____9304) in
      FStar_Syntax_Syntax.Tm_app uu____9287 in
    FStar_Syntax_Syntax.mk uu____9286 e.FStar_Syntax_Syntax.pos
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu____9362 = head_and_args e in
    match uu____9362 with
    | (hd, args) ->
        let uu____9407 =
          let uu____9422 =
            let uu____9423 = FStar_Syntax_Subst.compress hd in
            uu____9423.FStar_Syntax_Syntax.n in
          (uu____9422, args) in
        (match uu____9407 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, (e1, uu____9440)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____9475 -> FStar_Pervasives_Native.None)
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____9497 =
      let uu____9498 = unmeta t in uu____9498.FStar_Syntax_Syntax.n in
    match uu____9497 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____9503 -> false
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let uu____9526 = is_t_true t1 in
      if uu____9526
      then t2
      else
        (let uu____9533 = is_t_true t2 in
         if uu____9533 then t1 else mk_conj t1 t2)
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let uu____9561 = is_t_true t1 in
      if uu____9561
      then t_true
      else
        (let uu____9568 = is_t_true t2 in
         if uu____9568 then t_true else mk_disj t1 t2)
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1 ->
    fun e2 ->
      let uu____9597 =
        let uu____9598 =
          let uu____9615 =
            let uu____9626 = FStar_Syntax_Syntax.as_arg e1 in
            let uu____9635 =
              let uu____9646 = FStar_Syntax_Syntax.as_arg e2 in [uu____9646] in
            uu____9626 :: uu____9635 in
          (teq, uu____9615) in
        FStar_Syntax_Syntax.Tm_app uu____9598 in
      let uu____9691 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk uu____9597 uu____9691
let (mk_eq2 :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun u ->
    fun t ->
      fun e1 ->
        fun e2 ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u] in
          let uu____9714 =
            let uu____9715 =
              let uu____9732 =
                let uu____9743 = FStar_Syntax_Syntax.iarg t in
                let uu____9752 =
                  let uu____9763 = FStar_Syntax_Syntax.as_arg e1 in
                  let uu____9772 =
                    let uu____9783 = FStar_Syntax_Syntax.as_arg e2 in
                    [uu____9783] in
                  uu____9763 :: uu____9772 in
                uu____9743 :: uu____9752 in
              (eq_inst, uu____9732) in
            FStar_Syntax_Syntax.Tm_app uu____9715 in
          let uu____9836 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          FStar_Syntax_Syntax.mk uu____9714 uu____9836
let (mk_has_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    fun x ->
      fun t' ->
        let t_has_type = fvar_const FStar_Parser_Const.has_type_lid in
        let t_has_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst
               (t_has_type,
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]))
            FStar_Range.dummyRange in
        let uu____9861 =
          let uu____9862 =
            let uu____9879 =
              let uu____9890 = FStar_Syntax_Syntax.iarg t in
              let uu____9899 =
                let uu____9910 = FStar_Syntax_Syntax.as_arg x in
                let uu____9919 =
                  let uu____9930 = FStar_Syntax_Syntax.as_arg t' in
                  [uu____9930] in
                uu____9910 :: uu____9919 in
              uu____9890 :: uu____9899 in
            (t_has_type1, uu____9879) in
          FStar_Syntax_Syntax.Tm_app uu____9862 in
        FStar_Syntax_Syntax.mk uu____9861 FStar_Range.dummyRange
let (mk_with_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u ->
    fun t ->
      fun e ->
        let t_with_type =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
        let t_with_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst (t_with_type, [u]))
            FStar_Range.dummyRange in
        let uu____10007 =
          let uu____10008 =
            let uu____10025 =
              let uu____10036 = FStar_Syntax_Syntax.iarg t in
              let uu____10045 =
                let uu____10056 = FStar_Syntax_Syntax.as_arg e in
                [uu____10056] in
              uu____10036 :: uu____10045 in
            (t_with_type1, uu____10025) in
          FStar_Syntax_Syntax.Tm_app uu____10008 in
        FStar_Syntax_Syntax.mk uu____10007 FStar_Range.dummyRange
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____10103 =
    let uu____10104 =
      let uu____10111 =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
          FStar_Syntax_Syntax.delta_constant
          (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
      (uu____10111, [FStar_Syntax_Syntax.U_zero]) in
    FStar_Syntax_Syntax.Tm_uinst uu____10104 in
  FStar_Syntax_Syntax.mk uu____10103 FStar_Range.dummyRange
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
    FStar_Pervasives_Native.None
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
let (decidable_eq : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.op_Eq
let (mk_decidable_eq :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    fun e1 ->
      fun e2 ->
        let uu____10147 =
          let uu____10148 =
            let uu____10165 =
              let uu____10176 = FStar_Syntax_Syntax.iarg t in
              let uu____10185 =
                let uu____10196 = FStar_Syntax_Syntax.as_arg e1 in
                let uu____10205 =
                  let uu____10216 = FStar_Syntax_Syntax.as_arg e2 in
                  [uu____10216] in
                uu____10196 :: uu____10205 in
              uu____10176 :: uu____10185 in
            (decidable_eq, uu____10165) in
          FStar_Syntax_Syntax.Tm_app uu____10148 in
        let uu____10269 =
          FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
            e2.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Syntax.mk uu____10147 uu____10269
let (b_and : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.op_And
let (mk_and :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1 ->
    fun e2 ->
      let uu____10292 =
        let uu____10293 =
          let uu____10310 =
            let uu____10321 = FStar_Syntax_Syntax.as_arg e1 in
            let uu____10330 =
              let uu____10341 = FStar_Syntax_Syntax.as_arg e2 in
              [uu____10341] in
            uu____10321 :: uu____10330 in
          (b_and, uu____10310) in
        FStar_Syntax_Syntax.Tm_app uu____10293 in
      let uu____10386 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk uu____10292 uu____10386
let (mk_and_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun l ->
    match l with
    | [] -> exp_true_bool
    | hd::tl -> FStar_List.fold_left mk_and hd tl
let (mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        FStar_Syntax_Syntax.residual_comp)
  =
  fun l ->
    fun t ->
      fun f ->
        {
          FStar_Syntax_Syntax.residual_effect = l;
          FStar_Syntax_Syntax.residual_typ = t;
          FStar_Syntax_Syntax.residual_flags = f
        }
let (residual_tot :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.residual_comp)
  =
  fun t ->
    {
      FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid;
      FStar_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStar_Syntax_Syntax.residual_flags = [FStar_Syntax_Syntax.TOTAL]
    }
let (residual_comp_of_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.residual_comp) =
  fun c ->
    {
      FStar_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (comp_result c));
      FStar_Syntax_Syntax.residual_flags = (comp_flags c)
    }
let (mk_forall_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fa ->
    fun x ->
      fun body ->
        let uu____10495 =
          let uu____10496 =
            let uu____10513 =
              let uu____10524 =
                FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
              let uu____10533 =
                let uu____10544 =
                  let uu____10553 =
                    let uu____10554 =
                      let uu____10555 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____10555] in
                    abs uu____10554 body
                      (FStar_Pervasives_Native.Some (residual_tot ktype0)) in
                  FStar_Syntax_Syntax.as_arg uu____10553 in
                [uu____10544] in
              uu____10524 :: uu____10533 in
            (fa, uu____10513) in
          FStar_Syntax_Syntax.Tm_app uu____10496 in
        FStar_Syntax_Syntax.mk uu____10495 FStar_Range.dummyRange
let (mk_forall_no_univ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  = fun x -> fun body -> mk_forall_aux tforall x body
let (mk_forall :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun u ->
    fun x ->
      fun body ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u] in
        mk_forall_aux tforall1 x body
let (close_forall_no_univs :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs ->
    fun f ->
      FStar_List.fold_right
        (fun b ->
           fun f1 ->
             let uu____10682 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____10682
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____10701 -> true
    | uu____10703 -> false
let (if_then_else :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b ->
    fun t1 ->
      fun t2 ->
        let then_branch =
          let uu____10750 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos in
          (uu____10750, FStar_Pervasives_Native.None, t1) in
        let else_branch =
          let uu____10779 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos in
          (uu____10779, FStar_Pervasives_Native.None, t2) in
        let uu____10793 =
          let uu____10794 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10794 in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          uu____10793
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u ->
    fun p ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          FStar_Pervasives_Native.None in
      let uu____10870 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu____10873 =
        let uu____10884 = FStar_Syntax_Syntax.as_arg p in [uu____10884] in
      mk_app uu____10870 uu____10873
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u ->
    fun p ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.of_int (2)))
          FStar_Pervasives_Native.None in
      let uu____10924 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu____10927 =
        let uu____10938 = FStar_Syntax_Syntax.as_arg p in [uu____10938] in
      mk_app uu____10924 uu____10927
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____10973 = head_and_args t in
    match uu____10973 with
    | (head, args) ->
        let head1 = unascribe head in
        let head2 = un_uinst head1 in
        let uu____11022 =
          let uu____11037 =
            let uu____11038 = FStar_Syntax_Subst.compress head2 in
            uu____11038.FStar_Syntax_Syntax.n in
          (uu____11037, args) in
        (match uu____11022 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, (p, uu____11057)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b, p), []) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____11123 =
                    let uu____11128 =
                      let uu____11129 = FStar_Syntax_Syntax.mk_binder b in
                      [uu____11129] in
                    FStar_Syntax_Subst.open_term uu____11128 p in
                  (match uu____11123 with
                   | (bs, p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____11186 -> failwith "impossible" in
                       let uu____11194 =
                         let uu____11196 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____11196 in
                       if uu____11194
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____11212 -> FStar_Pervasives_Native.None)
         | uu____11215 -> FStar_Pervasives_Native.None)
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____11246 = head_and_args t in
    match uu____11246 with
    | (head, args) ->
        let uu____11297 =
          let uu____11312 =
            let uu____11313 = FStar_Syntax_Subst.compress head in
            uu____11313.FStar_Syntax_Syntax.n in
          (uu____11312, args) in
        (match uu____11297 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11335;
               FStar_Syntax_Syntax.vars = uu____11336;_},
             u::[]),
            (t1, uu____11339)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11386 -> FStar_Pervasives_Native.None)
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____11421 = head_and_args t in
    match uu____11421 with
    | (head, args) ->
        let uu____11472 =
          let uu____11487 =
            let uu____11488 = FStar_Syntax_Subst.compress head in
            uu____11488.FStar_Syntax_Syntax.n in
          (uu____11487, args) in
        (match uu____11472 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____11510;
               FStar_Syntax_Syntax.vars = uu____11511;_},
             u::[]),
            (t1, uu____11514)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____11561 -> FStar_Pervasives_Native.None)
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____11589 = let uu____11606 = unmeta t in head_and_args uu____11606 in
    match uu____11589 with
    | (head, uu____11609) ->
        let uu____11634 =
          let uu____11635 = un_uinst head in
          uu____11635.FStar_Syntax_Syntax.n in
        (match uu____11634 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             (((((((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.squash_lid)
                               ||
                               (FStar_Syntax_Syntax.fv_eq_lid fv
                                  FStar_Parser_Const.auto_squash_lid))
                              ||
                              (FStar_Syntax_Syntax.fv_eq_lid fv
                                 FStar_Parser_Const.and_lid))
                             ||
                             (FStar_Syntax_Syntax.fv_eq_lid fv
                                FStar_Parser_Const.or_lid))
                            ||
                            (FStar_Syntax_Syntax.fv_eq_lid fv
                               FStar_Parser_Const.not_lid))
                           ||
                           (FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.imp_lid))
                          ||
                          (FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.iff_lid))
                         ||
                         (FStar_Syntax_Syntax.fv_eq_lid fv
                            FStar_Parser_Const.ite_lid))
                        ||
                        (FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.exists_lid))
                       ||
                       (FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.forall_lid))
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.true_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.false_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.eq2_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.eq3_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.b2t_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.haseq_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.precedes_lid)
         | uu____11640 -> false)
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____11660 =
      let uu____11661 = FStar_Syntax_Subst.compress t in
      uu____11661.FStar_Syntax_Syntax.n in
    match uu____11660 with
    | FStar_Syntax_Syntax.Tm_arrow ([], c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[], c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs, c) ->
        let uu____11767 =
          let uu____11772 =
            let uu____11773 = arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____11773 in
          (b, uu____11772) in
        FStar_Pervasives_Native.Some uu____11767
    | uu____11778 -> FStar_Pervasives_Native.None
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____11801 = arrow_one_ln t in
    FStar_Util.bind_opt uu____11801
      (fun uu____11829 ->
         match uu____11829 with
         | (b, c) ->
             let uu____11848 = FStar_Syntax_Subst.open_comp [b] c in
             (match uu____11848 with
              | (bs, c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11911 ->
                        failwith
                          "impossible: open_comp returned different amount of binders" in
                  FStar_Pervasives_Native.Some (b1, c1)))
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu____11948 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____11948
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee ->
    match projectee with | QAll _0 -> true | uu____12000 -> false
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QAll _0 -> _0
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee ->
    match projectee with | QEx _0 -> true | uu____12043 -> false
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QEx _0 -> _0
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee ->
    match projectee with | BaseConn _0 -> true | uu____12084 -> false
let (__proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args)) =
  fun projectee -> match projectee with | BaseConn _0 -> _0
let (destruct_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  let f x = (x, x) in
  [(Prims.int_zero,
     [f FStar_Parser_Const.true_lid; f FStar_Parser_Const.false_lid]);
  ((Prims.of_int (2)),
    [f FStar_Parser_Const.and_lid;
    f FStar_Parser_Const.or_lid;
    f FStar_Parser_Const.imp_lid;
    f FStar_Parser_Const.iff_lid;
    f FStar_Parser_Const.eq2_lid;
    f FStar_Parser_Const.eq3_lid]);
  (Prims.int_one, [f FStar_Parser_Const.not_lid]);
  ((Prims.of_int (3)),
    [f FStar_Parser_Const.ite_lid; f FStar_Parser_Const.eq2_lid]);
  ((Prims.of_int (4)), [f FStar_Parser_Const.eq3_lid])]
let (destruct_sq_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  [((Prims.of_int (2)),
     [(FStar_Parser_Const.c_and_lid, FStar_Parser_Const.and_lid);
     (FStar_Parser_Const.c_or_lid, FStar_Parser_Const.or_lid);
     (FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.c_eq2_lid);
     (FStar_Parser_Const.c_eq3_lid, FStar_Parser_Const.c_eq3_lid)]);
  ((Prims.of_int (3)),
    [(FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.c_eq2_lid)]);
  ((Prims.of_int (4)),
    [(FStar_Parser_Const.c_eq3_lid, FStar_Parser_Const.c_eq3_lid)]);
  (Prims.int_zero,
    [(FStar_Parser_Const.c_true_lid, FStar_Parser_Const.true_lid);
    (FStar_Parser_Const.c_false_lid, FStar_Parser_Const.false_lid)])]
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1 in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t, FStar_Syntax_Syntax.Meta_monadic uu____12470) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t, FStar_Syntax_Syntax.Meta_monadic_lift uu____12482) ->
          unmeta_monadic t
      | uu____12495 -> f2 in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args in
      let aux uu____12564 =
        match uu____12564 with
        | (arity, lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____12602 ->
                   match uu____12602 with
                   | (lid, out_lid) ->
                       let uu____12611 =
                         FStar_Ident.lid_equals target_lid lid in
                       if uu____12611
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None in
      FStar_Util.find_map table aux in
    let destruct_base_conn t =
      let uu____12638 = head_and_args t in
      match uu____12638 with
      | (hd, args) ->
          let uu____12683 =
            let uu____12684 = un_uinst hd in
            uu____12684.FStar_Syntax_Syntax.n in
          (match uu____12683 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____12690 -> FStar_Pervasives_Native.None) in
    let destruct_sq_base_conn t =
      let uu____12699 = un_squash t in
      FStar_Util.bind_opt uu____12699
        (fun t1 ->
           let uu____12715 = head_and_args' t1 in
           match uu____12715 with
           | (hd, args) ->
               let uu____12754 =
                 let uu____12755 = un_uinst hd in
                 uu____12755.FStar_Syntax_Syntax.n in
               (match uu____12754 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____12761 -> FStar_Pervasives_Native.None)) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2, FStar_Syntax_Syntax.Meta_pattern (uu____12802, pats)) ->
          let uu____12840 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____12840)
      | uu____12853 -> ([], t1) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____12920 = head_and_args t1 in
        match uu____12920 with
        | (t2, args) ->
            let uu____12975 = un_uinst t2 in
            let uu____12976 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____13017 ->
                      match uu____13017 with
                      | (t3, imp) ->
                          let uu____13036 = unascribe t3 in
                          (uu____13036, imp))) in
            (uu____12975, uu____12976) in
      let rec aux qopt out t1 =
        let uu____13087 = let uu____13111 = flat t1 in (qopt, uu____13111) in
        match uu____13087 with
        | (FStar_Pervasives_Native.Some fa,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu____13151;
              FStar_Syntax_Syntax.vars = uu____13152;_},
            ({
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                 (b::[], t2, uu____13155);
               FStar_Syntax_Syntax.pos = uu____13156;
               FStar_Syntax_Syntax.vars = uu____13157;_},
             uu____13158)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some fa,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu____13260;
              FStar_Syntax_Syntax.vars = uu____13261;_},
            uu____13262::({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_abs
                              (b::[], t2, uu____13265);
                            FStar_Syntax_Syntax.pos = uu____13266;
                            FStar_Syntax_Syntax.vars = uu____13267;_},
                          uu____13268)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu____13385;
              FStar_Syntax_Syntax.vars = uu____13386;_},
            ({
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                 (b::[], t2, uu____13389);
               FStar_Syntax_Syntax.pos = uu____13390;
               FStar_Syntax_Syntax.vars = uu____13391;_},
             uu____13392)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13485 =
              let uu____13489 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              FStar_Pervasives_Native.Some uu____13489 in
            aux uu____13485 (b :: out) t2
        | (FStar_Pervasives_Native.None,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu____13499;
              FStar_Syntax_Syntax.vars = uu____13500;_},
            uu____13501::({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_abs
                              (b::[], t2, uu____13504);
                            FStar_Syntax_Syntax.pos = uu____13505;
                            FStar_Syntax_Syntax.vars = uu____13506;_},
                          uu____13507)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____13616 =
              let uu____13620 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              FStar_Pervasives_Native.Some uu____13620 in
            aux uu____13616 (b :: out) t2
        | (FStar_Pervasives_Native.Some b, uu____13630) ->
            let bs = FStar_List.rev out in
            let uu____13683 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____13683 with
             | (bs1, t2) ->
                 let uu____13692 = patterns t2 in
                 (match uu____13692 with
                  | (pats, body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____13742 -> FStar_Pervasives_Native.None in
      aux FStar_Pervasives_Native.None [] t in
    let rec destruct_sq_forall t =
      let uu____13797 = un_squash t in
      FStar_Util.bind_opt uu____13797
        (fun t1 ->
           let uu____13812 = arrow_one t1 in
           match uu____13812 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____13827 =
                 let uu____13829 = is_tot_or_gtot_comp c in
                 Prims.op_Negation uu____13829 in
               if uu____13827
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____13839 = comp_to_comp_typ_nouniv c in
                    uu____13839.FStar_Syntax_Syntax.result_typ in
                  let uu____13840 =
                    is_free_in (FStar_Pervasives_Native.fst b) q in
                  if uu____13840
                  then
                    let uu____13847 = patterns q in
                    match uu____13847 with
                    | (pats, q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13910 =
                       let uu____13911 =
                         let uu____13916 =
                           let uu____13917 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let uu____13928 =
                             let uu____13939 = FStar_Syntax_Syntax.as_arg q in
                             [uu____13939] in
                           uu____13917 :: uu____13928 in
                         (FStar_Parser_Const.imp_lid, uu____13916) in
                       BaseConn uu____13911 in
                     FStar_Pervasives_Native.Some uu____13910))
           | uu____13972 -> FStar_Pervasives_Native.None)
    and destruct_sq_exists t =
      let uu____13980 = un_squash t in
      FStar_Util.bind_opt uu____13980
        (fun t1 ->
           let uu____14011 = head_and_args' t1 in
           match uu____14011 with
           | (hd, args) ->
               let uu____14050 =
                 let uu____14065 =
                   let uu____14066 = un_uinst hd in
                   uu____14066.FStar_Syntax_Syntax.n in
                 (uu____14065, args) in
               (match uu____14050 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (a1, uu____14083)::(a2, uu____14085)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____14136 =
                      let uu____14137 = FStar_Syntax_Subst.compress a2 in
                      uu____14137.FStar_Syntax_Syntax.n in
                    (match uu____14136 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[], q, uu____14144) ->
                         let uu____14179 = FStar_Syntax_Subst.open_term [b] q in
                         (match uu____14179 with
                          | (bs, q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____14232 -> failwith "impossible" in
                              let uu____14240 = patterns q1 in
                              (match uu____14240 with
                               | (pats, q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____14301 -> FStar_Pervasives_Native.None)
                | uu____14302 -> FStar_Pervasives_Native.None))
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) ->
          let uu____14325 = destruct_sq_forall phi in
          (match uu____14325 with
           | FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) ->
               FStar_All.pipe_left
                 (fun uu____14335 -> FStar_Pervasives_Native.Some uu____14335)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____14342 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) ->
          let uu____14348 = destruct_sq_exists phi in
          (match uu____14348 with
           | FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) ->
               FStar_All.pipe_left
                 (fun uu____14358 -> FStar_Pervasives_Native.Some uu____14358)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____14365 -> f1)
      | uu____14368 -> f1 in
    let phi = unmeta_monadic f in
    let uu____14372 = destruct_base_conn phi in
    FStar_Util.catch_opt uu____14372
      (fun uu____14377 ->
         let uu____14378 = destruct_q_conn phi in
         FStar_Util.catch_opt uu____14378
           (fun uu____14383 ->
              let uu____14384 = destruct_sq_base_conn phi in
              FStar_Util.catch_opt uu____14384
                (fun uu____14389 ->
                   let uu____14390 = destruct_sq_forall phi in
                   FStar_Util.catch_opt uu____14390
                     (fun uu____14395 ->
                        let uu____14396 = destruct_sq_exists phi in
                        FStar_Util.catch_opt uu____14396
                          (fun uu____14400 -> FStar_Pervasives_Native.None)))))
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid ->
    fun a ->
      fun pos ->
        let lb =
          let uu____14418 =
            let uu____14423 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None in
            FStar_Util.Inr uu____14423 in
          let uu____14424 =
            let uu____14425 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
            arrow a.FStar_Syntax_Syntax.action_params uu____14425 in
          let uu____14428 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____14418 a.FStar_Syntax_Syntax.action_univs uu____14424
            FStar_Parser_Const.effect_Tot_lid uu____14428 [] pos in
        {
          FStar_Syntax_Syntax.sigel =
            (FStar_Syntax_Syntax.Sig_let
               ((false, [lb]), [a.FStar_Syntax_Syntax.action_name]));
          FStar_Syntax_Syntax.sigrng =
            ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos);
          FStar_Syntax_Syntax.sigquals =
            [FStar_Syntax_Syntax.Visible_default;
            FStar_Syntax_Syntax.Action eff_lid];
          FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta;
          FStar_Syntax_Syntax.sigattrs = [];
          FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
        }
let (mk_reify :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let reify_ =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        t.FStar_Syntax_Syntax.pos in
    let uu____14454 =
      let uu____14455 =
        let uu____14472 =
          let uu____14483 = FStar_Syntax_Syntax.as_arg t in [uu____14483] in
        (reify_, uu____14472) in
      FStar_Syntax_Syntax.Tm_app uu____14455 in
    FStar_Syntax_Syntax.mk uu____14454 t.FStar_Syntax_Syntax.pos
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let reflect_ =
      let uu____14535 =
        let uu____14536 =
          let uu____14537 = FStar_Ident.lid_of_str "Bogus.Effect" in
          FStar_Const.Const_reflect uu____14537 in
        FStar_Syntax_Syntax.Tm_constant uu____14536 in
      FStar_Syntax_Syntax.mk uu____14535 t.FStar_Syntax_Syntax.pos in
    let uu____14539 =
      let uu____14540 =
        let uu____14557 =
          let uu____14568 = FStar_Syntax_Syntax.as_arg t in [uu____14568] in
        (reflect_, uu____14557) in
      FStar_Syntax_Syntax.Tm_app uu____14540 in
    FStar_Syntax_Syntax.mk uu____14539 t.FStar_Syntax_Syntax.pos
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____14612 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____14629 = unfold_lazy i in delta_qualifier uu____14629
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____14631 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____14632 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____14633 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____14656 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____14669 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____14670 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____14677 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____14678 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2, uu____14694) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____14699;
           FStar_Syntax_Syntax.index = uu____14700;
           FStar_Syntax_Syntax.sort = t2;_},
         uu____14702)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2, uu____14711) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____14717, uu____14718) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2, uu____14760) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____14785, t2, uu____14787) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____14812, t2) -> delta_qualifier t2
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d ->
    match d with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Syntax_Syntax.Delta_constant_at_level (i + Prims.int_one)
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Syntax_Syntax.Delta_equational_at_level (i + Prims.int_one)
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t ->
    let uu____14851 = delta_qualifier t in incr_delta_depth uu____14851
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____14859 =
      let uu____14860 = FStar_Syntax_Subst.compress t in
      uu____14860.FStar_Syntax_Syntax.n in
    match uu____14859 with
    | FStar_Syntax_Syntax.Tm_unknown -> true
    | uu____14865 -> false
let rec apply_last :
  'uuuuuu14874 .
    ('uuuuuu14874 -> 'uuuuuu14874) ->
      'uuuuuu14874 Prims.list -> 'uuuuuu14874 Prims.list
  =
  fun f ->
    fun l ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14900 = f a in [uu____14900]
      | x::xs -> let uu____14905 = apply_last f xs in x :: uu____14905
let (dm4f_lid :
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident) =
  fun ed ->
    fun name ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname in
      let p' =
        apply_last
          (fun s ->
             Prims.op_Hat "_dm4f_" (Prims.op_Hat s (Prims.op_Hat "_" name)))
          p in
      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
let (mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun typ ->
    fun rng ->
      fun l ->
        let ctor l1 =
          let uu____14960 =
            let uu____14961 =
              FStar_Syntax_Syntax.lid_as_fv l1
                FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Syntax_Syntax.Tm_fvar uu____14961 in
          FStar_Syntax_Syntax.mk uu____14960 rng in
        let cons args pos =
          let uu____14973 =
            let uu____14974 = ctor FStar_Parser_Const.cons_lid in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14974
              [FStar_Syntax_Syntax.U_zero] in
          FStar_Syntax_Syntax.mk_Tm_app uu____14973 args pos in
        let nil args pos =
          let uu____14986 =
            let uu____14987 = ctor FStar_Parser_Const.nil_lid in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14987
              [FStar_Syntax_Syntax.U_zero] in
          FStar_Syntax_Syntax.mk_Tm_app uu____14986 args pos in
        let uu____14988 =
          let uu____14989 =
            let uu____14990 = FStar_Syntax_Syntax.iarg typ in [uu____14990] in
          nil uu____14989 rng in
        FStar_List.fold_right
          (fun t ->
             fun a ->
               let uu____15024 =
                 let uu____15025 = FStar_Syntax_Syntax.iarg typ in
                 let uu____15034 =
                   let uu____15045 = FStar_Syntax_Syntax.as_arg t in
                   let uu____15054 =
                     let uu____15065 = FStar_Syntax_Syntax.as_arg a in
                     [uu____15065] in
                   uu____15045 :: uu____15054 in
                 uu____15025 :: uu____15034 in
               cons uu____15024 t.FStar_Syntax_Syntax.pos) l uu____14988
let rec eqlist :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq ->
    fun xs ->
      fun ys ->
        match (xs, ys) with
        | ([], []) -> true
        | (x::xs1, y::ys1) -> (eq x y) && (eqlist eq xs1 ys1)
        | uu____15174 -> false
let eqsum :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) ->
        ('a, 'b) FStar_Util.either ->
          ('a, 'b) FStar_Util.either -> Prims.bool
  =
  fun e1 ->
    fun e2 ->
      fun x ->
        fun y ->
          match (x, y) with
          | (FStar_Util.Inl x1, FStar_Util.Inl y1) -> e1 x1 y1
          | (FStar_Util.Inr x1, FStar_Util.Inr y1) -> e2 x1 y1
          | uu____15288 -> false
let eqprod :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) -> ('a * 'b) -> ('a * 'b) -> Prims.bool
  =
  fun e1 ->
    fun e2 ->
      fun x ->
        fun y ->
          match (x, y) with
          | ((x1, x2), (y1, y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> Prims.bool
  =
  fun e ->
    fun x ->
      fun y ->
        match (x, y) with
        | (FStar_Pervasives_Native.Some x1, FStar_Pervasives_Native.Some y1)
            -> e x1 y1
        | uu____15454 -> false
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg ->
    fun cond ->
      if cond
      then true
      else
        ((let uu____15492 = FStar_ST.op_Bang debug_term_eq in
          if uu____15492
          then FStar_Util.print1 ">>> term_eq failing: %s\n" msg
          else ());
         false)
let (fail : Prims.string -> Prims.bool) = fun msg -> check msg false
let rec (term_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun dbg ->
    fun t1 ->
      fun t2 ->
        let t11 = let uu____15680 = unmeta_safe t1 in canon_app uu____15680 in
        let t21 = let uu____15684 = unmeta_safe t2 in canon_app uu____15684 in
        let uu____15687 =
          let uu____15692 =
            let uu____15693 =
              let uu____15696 = un_uinst t11 in
              FStar_Syntax_Subst.compress uu____15696 in
            uu____15693.FStar_Syntax_Syntax.n in
          let uu____15697 =
            let uu____15698 =
              let uu____15701 = un_uinst t21 in
              FStar_Syntax_Subst.compress uu____15701 in
            uu____15698.FStar_Syntax_Syntax.n in
          (uu____15692, uu____15697) in
        match uu____15687 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____15703, uu____15704) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15713, FStar_Syntax_Syntax.Tm_uinst uu____15714) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____15723, uu____15724) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15741, FStar_Syntax_Syntax.Tm_delayed uu____15742) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____15759, uu____15760) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____15789, FStar_Syntax_Syntax.Tm_ascribed uu____15790) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x, FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x, FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____15829 = FStar_Syntax_Syntax.fv_eq x y in
            check "fvar" uu____15829
        | (FStar_Syntax_Syntax.Tm_constant c1,
           FStar_Syntax_Syntax.Tm_constant c2) ->
            let uu____15834 = FStar_Const.eq_const c1 c2 in
            check "const" uu____15834
        | (FStar_Syntax_Syntax.Tm_type uu____15837,
           FStar_Syntax_Syntax.Tm_type uu____15838) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1),
           FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) ->
            (let uu____15896 = eqlist (binder_eq_dbg dbg) b1 b2 in
             check "abs binders" uu____15896) &&
              (let uu____15906 = term_eq_dbg dbg t12 t22 in
               check "abs bodies" uu____15906)
        | (FStar_Syntax_Syntax.Tm_arrow (b1, c1),
           FStar_Syntax_Syntax.Tm_arrow (b2, c2)) ->
            (let uu____15955 = eqlist (binder_eq_dbg dbg) b1 b2 in
             check "arrow binders" uu____15955) &&
              (let uu____15965 = comp_eq_dbg dbg c1 c2 in
               check "arrow comp" uu____15965)
        | (FStar_Syntax_Syntax.Tm_refine (b1, t12),
           FStar_Syntax_Syntax.Tm_refine (b2, t22)) ->
            (let uu____15982 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort in
             check "refine bv sort" uu____15982) &&
              (let uu____15986 = term_eq_dbg dbg t12 t22 in
               check "refine formula" uu____15986)
        | (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app
           (f2, a2)) ->
            (let uu____16043 = term_eq_dbg dbg f1 f2 in
             check "app head" uu____16043) &&
              (let uu____16047 = eqlist (arg_eq_dbg dbg) a1 a2 in
               check "app args" uu____16047)
        | (FStar_Syntax_Syntax.Tm_match (t12, bs1),
           FStar_Syntax_Syntax.Tm_match (t22, bs2)) ->
            (let uu____16136 = term_eq_dbg dbg t12 t22 in
             check "match head" uu____16136) &&
              (let uu____16140 = eqlist (branch_eq_dbg dbg) bs1 bs2 in
               check "match branches" uu____16140)
        | (FStar_Syntax_Syntax.Tm_lazy uu____16157, uu____16158) ->
            let uu____16159 =
              let uu____16161 = unlazy t11 in term_eq_dbg dbg uu____16161 t21 in
            check "lazy_l" uu____16159
        | (uu____16163, FStar_Syntax_Syntax.Tm_lazy uu____16164) ->
            let uu____16165 =
              let uu____16167 = unlazy t21 in term_eq_dbg dbg t11 uu____16167 in
            check "lazy_r" uu____16165
        | (FStar_Syntax_Syntax.Tm_let ((b1, lbs1), t12),
           FStar_Syntax_Syntax.Tm_let ((b2, lbs2), t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____16212 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2 in
                check "let lbs" uu____16212))
              &&
              (let uu____16216 = term_eq_dbg dbg t12 t22 in
               check "let body" uu____16216)
        | (FStar_Syntax_Syntax.Tm_uvar (u1, uu____16220),
           FStar_Syntax_Syntax.Tm_uvar (u2, uu____16222)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted (qt1, qi1),
           FStar_Syntax_Syntax.Tm_quoted (qt2, qi2)) ->
            (let uu____16282 =
               let uu____16284 = eq_quoteinfo qi1 qi2 in uu____16284 = Equal in
             check "tm_quoted qi" uu____16282) &&
              (let uu____16287 = term_eq_dbg dbg qt1 qt2 in
               check "tm_quoted payload" uu____16287)
        | (FStar_Syntax_Syntax.Tm_meta (t12, m1), FStar_Syntax_Syntax.Tm_meta
           (t22, m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic (n1, ty1),
                FStar_Syntax_Syntax.Meta_monadic (n2, ty2)) ->
                 (let uu____16317 = FStar_Ident.lid_equals n1 n2 in
                  check "meta_monadic lid" uu____16317) &&
                   (let uu____16321 = term_eq_dbg dbg ty1 ty2 in
                    check "meta_monadic type" uu____16321)
             | (FStar_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1),
                FStar_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) ->
                 ((let uu____16340 = FStar_Ident.lid_equals s1 s2 in
                   check "meta_monadic_lift src" uu____16340) &&
                    (let uu____16344 = FStar_Ident.lid_equals t13 t23 in
                     check "meta_monadic_lift tgt" uu____16344))
                   &&
                   (let uu____16348 = term_eq_dbg dbg ty1 ty2 in
                    check "meta_monadic_lift type" uu____16348)
             | uu____16351 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown, uu____16357) -> fail "unk"
        | (uu____16359, FStar_Syntax_Syntax.Tm_unknown) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____16361, uu____16362) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____16364, uu____16365) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____16367, uu____16368) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____16370, uu____16371) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____16373, uu____16374) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____16376, uu____16377) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____16397, uu____16398) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____16414, uu____16415) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____16423, uu____16424) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____16442, uu____16443) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____16467, uu____16468) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____16483, uu____16484) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____16498, uu____16499) ->
            fail "bottom"
        | (uu____16507, FStar_Syntax_Syntax.Tm_bvar uu____16508) ->
            fail "bottom"
        | (uu____16510, FStar_Syntax_Syntax.Tm_name uu____16511) ->
            fail "bottom"
        | (uu____16513, FStar_Syntax_Syntax.Tm_fvar uu____16514) ->
            fail "bottom"
        | (uu____16516, FStar_Syntax_Syntax.Tm_constant uu____16517) ->
            fail "bottom"
        | (uu____16519, FStar_Syntax_Syntax.Tm_type uu____16520) ->
            fail "bottom"
        | (uu____16522, FStar_Syntax_Syntax.Tm_abs uu____16523) ->
            fail "bottom"
        | (uu____16543, FStar_Syntax_Syntax.Tm_arrow uu____16544) ->
            fail "bottom"
        | (uu____16560, FStar_Syntax_Syntax.Tm_refine uu____16561) ->
            fail "bottom"
        | (uu____16569, FStar_Syntax_Syntax.Tm_app uu____16570) ->
            fail "bottom"
        | (uu____16588, FStar_Syntax_Syntax.Tm_match uu____16589) ->
            fail "bottom"
        | (uu____16613, FStar_Syntax_Syntax.Tm_let uu____16614) ->
            fail "bottom"
        | (uu____16629, FStar_Syntax_Syntax.Tm_uvar uu____16630) ->
            fail "bottom"
        | (uu____16644, FStar_Syntax_Syntax.Tm_meta uu____16645) ->
            fail "bottom"
and (arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
        Prims.bool)
  =
  fun dbg ->
    fun a1 ->
      fun a2 ->
        eqprod
          (fun t1 ->
             fun t2 ->
               let uu____16680 = term_eq_dbg dbg t1 t2 in
               check "arg tm" uu____16680)
          (fun q1 ->
             fun q2 ->
               let uu____16692 =
                 let uu____16694 = eq_aqual q1 q2 in uu____16694 = Equal in
               check "arg qual" uu____16692) a1 a2
and (binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) -> Prims.bool)
  =
  fun dbg ->
    fun b1 ->
      fun b2 ->
        eqprod
          (fun b11 ->
             fun b21 ->
               let uu____16719 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort in
               check "binder sort" uu____16719)
          (fun q1 ->
             fun q2 ->
               let uu____16731 =
                 let uu____16733 = eq_aqual q1 q2 in uu____16733 = Equal in
               check "binder qual" uu____16731) b1 b2
and (comp_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun dbg ->
    fun c1 ->
      fun c2 ->
        let c11 = comp_to_comp_typ_nouniv c1 in
        let c21 = comp_to_comp_typ_nouniv c2 in
        ((let uu____16747 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name in
          check "comp eff" uu____16747) &&
           (let uu____16751 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ in
            check "comp result typ" uu____16751))
          && true
and (branch_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) ->
      (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax) -> Prims.bool)
  =
  fun dbg ->
    fun uu____16756 ->
      fun uu____16757 ->
        match (uu____16756, uu____16757) with
        | ((p1, w1, t1), (p2, w2, t2)) ->
            ((let uu____16884 = FStar_Syntax_Syntax.eq_pat p1 p2 in
              check "branch pat" uu____16884) &&
               (let uu____16888 = term_eq_dbg dbg t1 t2 in
                check "branch body" uu____16888))
              &&
              (let uu____16892 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some x,
                    FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) -> true
                 | uu____16934 -> false in
               check "branch when" uu____16892)
and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg ->
    fun lb1 ->
      fun lb2 ->
        ((let uu____16955 =
            eqsum (fun bv1 -> fun bv2 -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname in
          check "lb bv" uu____16955) &&
           (let uu____16964 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp in
            check "lb typ" uu____16964))
          &&
          (let uu____16968 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef in
           check "lb def" uu____16968)
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let r =
        let uu____16985 = FStar_ST.op_Bang debug_term_eq in
        term_eq_dbg uu____16985 t1 t2 in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____17039 ->
        let uu____17054 =
          let uu____17056 = FStar_Syntax_Subst.compress t in
          sizeof uu____17056 in
        Prims.int_one + uu____17054
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____17059 = sizeof bv.FStar_Syntax_Syntax.sort in
        Prims.int_one + uu____17059
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____17063 = sizeof bv.FStar_Syntax_Syntax.sort in
        Prims.int_one + uu____17063
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu____17072 = sizeof t1 in (FStar_List.length us) + uu____17072
    | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____17076) ->
        let uu____17101 = sizeof t1 in
        let uu____17103 =
          FStar_List.fold_left
            (fun acc ->
               fun uu____17118 ->
                 match uu____17118 with
                 | (bv, uu____17128) ->
                     let uu____17133 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____17133) Prims.int_zero bs in
        uu____17101 + uu____17103
    | FStar_Syntax_Syntax.Tm_app (hd, args) ->
        let uu____17162 = sizeof hd in
        let uu____17164 =
          FStar_List.fold_left
            (fun acc ->
               fun uu____17179 ->
                 match uu____17179 with
                 | (arg, uu____17189) ->
                     let uu____17194 = sizeof arg in acc + uu____17194)
            Prims.int_zero args in
        uu____17162 + uu____17164
    | uu____17197 -> Prims.int_one
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid ->
    fun t ->
      let uu____17211 =
        let uu____17212 = un_uinst t in uu____17212.FStar_Syntax_Syntax.n in
      match uu____17211 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____17217 -> false
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t -> is_fvar FStar_Parser_Const.synth_lid t
let (has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool)
  = fun attrs -> fun attr -> FStar_Util.for_some (is_fvar attr) attrs
let (get_attribute :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.args FStar_Pervasives_Native.option)
  =
  fun attr ->
    fun attrs ->
      FStar_List.tryPick
        (fun t ->
           let uu____17278 = head_and_args t in
           match uu____17278 with
           | (head, args) ->
               let uu____17333 =
                 let uu____17334 = FStar_Syntax_Subst.compress head in
                 uu____17334.FStar_Syntax_Syntax.n in
               (match uu____17333 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____17360 -> FStar_Pervasives_Native.None)) attrs
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr ->
    fun attrs ->
      FStar_List.filter
        (fun a ->
           let uu____17393 = is_fvar attr a in Prims.op_Negation uu____17393)
        attrs
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p ->
    fun r ->
      FStar_Errors.set_option_warning_callback_range
        (FStar_Pervasives_Native.Some r);
      (let set_options s =
         let uu____17415 = FStar_Options.set_options s in
         match uu____17415 with
         | FStar_Getopt.Success -> ()
         | FStar_Getopt.Help ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_FailToProcessPragma,
                 "Failed to process pragma: use 'fstar --help' to see which options are available")
               r
         | FStar_Getopt.Error s1 ->
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_FailToProcessPragma,
                 (Prims.op_Hat "Failed to process pragma: " s1)) r in
       match p with
       | FStar_Syntax_Syntax.LightOff -> FStar_Options.set_ml_ish ()
       | FStar_Syntax_Syntax.SetOptions o -> set_options o
       | FStar_Syntax_Syntax.ResetOptions sopt ->
           ((let uu____17429 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____17429 (fun uu____17431 -> ()));
            (match sopt with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some s -> set_options s))
       | FStar_Syntax_Syntax.PushOptions sopt ->
           (FStar_Options.internal_push ();
            (match sopt with
             | FStar_Pervasives_Native.None -> ()
             | FStar_Pervasives_Native.Some s -> set_options s))
       | FStar_Syntax_Syntax.RestartSolver -> ()
       | FStar_Syntax_Syntax.PopOptions ->
           let uu____17445 = FStar_Options.internal_pop () in
           if uu____17445
           then ()
           else
             FStar_Errors.raise_error
               (FStar_Errors.Fatal_FailToProcessPragma,
                 "Cannot #pop-options, stack would become empty") r)
let rec (unbound_variables :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun tm ->
    let t = FStar_Syntax_Subst.compress tm in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____17477 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____17496 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____17511 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____17512 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____17513 -> []
    | FStar_Syntax_Syntax.Tm_unknown -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____17522) ->
        let uu____17547 = FStar_Syntax_Subst.open_term bs t1 in
        (match uu____17547 with
         | (bs1, t2) ->
             let uu____17556 =
               FStar_List.collect
                 (fun uu____17568 ->
                    match uu____17568 with
                    | (b, uu____17578) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1 in
             let uu____17583 = unbound_variables t2 in
             FStar_List.append uu____17556 uu____17583)
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____17608 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____17608 with
         | (bs1, c1) ->
             let uu____17617 =
               FStar_List.collect
                 (fun uu____17629 ->
                    match uu____17629 with
                    | (b, uu____17639) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1 in
             let uu____17644 = unbound_variables_comp c1 in
             FStar_List.append uu____17617 uu____17644)
    | FStar_Syntax_Syntax.Tm_refine (b, t1) ->
        let uu____17653 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1 in
        (match uu____17653 with
         | (bs, t2) ->
             let uu____17676 =
               FStar_List.collect
                 (fun uu____17688 ->
                    match uu____17688 with
                    | (b1, uu____17698) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs in
             let uu____17703 = unbound_variables t2 in
             FStar_List.append uu____17676 uu____17703)
    | FStar_Syntax_Syntax.Tm_app (t1, args) ->
        let uu____17732 =
          FStar_List.collect
            (fun uu____17746 ->
               match uu____17746 with
               | (x, uu____17758) -> unbound_variables x) args in
        let uu____17767 = unbound_variables t1 in
        FStar_List.append uu____17732 uu____17767
    | FStar_Syntax_Syntax.Tm_match (t1, pats) ->
        let uu____17808 = unbound_variables t1 in
        let uu____17811 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br ->
                  let uu____17826 = FStar_Syntax_Subst.open_branch br in
                  match uu____17826 with
                  | (p, wopt, t2) ->
                      let uu____17848 = unbound_variables t2 in
                      let uu____17851 =
                        match wopt with
                        | FStar_Pervasives_Native.None -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3 in
                      FStar_List.append uu____17848 uu____17851)) in
        FStar_List.append uu____17808 uu____17811
    | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____17865) ->
        let uu____17906 = unbound_variables t1 in
        let uu____17909 =
          let uu____17912 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2 in
          let uu____17943 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac in
          FStar_List.append uu____17912 uu____17943 in
        FStar_List.append uu____17906 uu____17909
    | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t1) ->
        let uu____17984 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp in
        let uu____17987 =
          let uu____17990 = unbound_variables lb.FStar_Syntax_Syntax.lbdef in
          let uu____17993 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____17998 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____18000 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1 in
                (match uu____18000 with
                 | (uu____18021, t2) -> unbound_variables t2) in
          FStar_List.append uu____17990 uu____17993 in
        FStar_List.append uu____17984 uu____17987
    | FStar_Syntax_Syntax.Tm_let ((uu____18023, lbs), t1) ->
        let uu____18043 = FStar_Syntax_Subst.open_let_rec lbs t1 in
        (match uu____18043 with
         | (lbs1, t2) ->
             let uu____18058 = unbound_variables t2 in
             let uu____18061 =
               FStar_List.collect
                 (fun lb ->
                    let uu____18068 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____18071 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef in
                    FStar_List.append uu____18068 uu____18071) lbs1 in
             FStar_List.append uu____18058 uu____18061)
    | FStar_Syntax_Syntax.Tm_quoted (tm1, qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static -> []
         | FStar_Syntax_Syntax.Quote_dynamic -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
        let uu____18088 = unbound_variables t1 in
        let uu____18091 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____18096, args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____18151 ->
                      match uu____18151 with
                      | (a, uu____18163) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____18172, uu____18173, t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____18179, t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____18185 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____18194 -> []
          | FStar_Syntax_Syntax.Meta_named uu____18195 -> [] in
        FStar_List.append uu____18088 uu____18091
and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t, uu____18202) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t, uu____18212) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____18222 = unbound_variables ct.FStar_Syntax_Syntax.result_typ in
        let uu____18225 =
          FStar_List.collect
            (fun uu____18239 ->
               match uu____18239 with
               | (a, uu____18251) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args in
        FStar_List.append uu____18222 uu____18225
let (extract_attr' :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.term Prims.list ->
      (FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid ->
    fun attrs ->
      let rec aux acc attrs1 =
        match attrs1 with
        | [] -> FStar_Pervasives_Native.None
        | h::t ->
            let uu____18366 = head_and_args h in
            (match uu____18366 with
             | (head, args) ->
                 let uu____18427 =
                   let uu____18428 = FStar_Syntax_Subst.compress head in
                   uu____18428.FStar_Syntax_Syntax.n in
                 (match uu____18427 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____18481 -> aux (h :: acc) t)) in
      aux [] attrs
let (extract_attr :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid ->
    fun se ->
      let uu____18505 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs in
      match uu____18505 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs', t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2557_18547 = se in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2557_18547.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2557_18547.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2557_18547.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2557_18547.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2557_18547.FStar_Syntax_Syntax.sigopts)
              }), t)
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____18555 =
      let uu____18556 = FStar_Syntax_Subst.compress t in
      uu____18556.FStar_Syntax_Syntax.n in
    match uu____18555 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____18560, c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats, uu____18588)::uu____18589 ->
                  let pats' = unmeta pats in
                  let uu____18649 = head_and_args pats' in
                  (match uu____18649 with
                   | (head, uu____18668) ->
                       let uu____18693 =
                         let uu____18694 = un_uinst head in
                         uu____18694.FStar_Syntax_Syntax.n in
                       (match uu____18693 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____18699 -> false))
              | uu____18701 -> false)
         | uu____18713 -> false)
    | uu____18715 -> false
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu____18731 = let uu____18748 = unmeta e in head_and_args uu____18748 in
    match uu____18731 with
    | (head, args) ->
        let uu____18779 =
          let uu____18794 =
            let uu____18795 = un_uinst head in
            uu____18795.FStar_Syntax_Syntax.n in
          (uu____18794, args) in
        (match uu____18779 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, uu____18813) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            uu____18837::(hd, uu____18839)::(tl, uu____18841)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____18908 =
               let uu____18911 =
                 let uu____18914 = list_elements tl in
                 FStar_Util.must uu____18914 in
               hd :: uu____18911 in
             FStar_Pervasives_Native.Some uu____18908
         | uu____18923 -> FStar_Pervasives_Native.None)
let (unthunk : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____18946 =
      let uu____18947 = FStar_Syntax_Subst.compress t in
      uu____18947.FStar_Syntax_Syntax.n in
    match uu____18946 with
    | FStar_Syntax_Syntax.Tm_abs (b::[], e, uu____18952) ->
        let uu____18987 = FStar_Syntax_Subst.open_term [b] e in
        (match uu____18987 with
         | (bs, e1) ->
             let b1 = FStar_List.hd bs in
             let uu____19019 = is_free_in (FStar_Pervasives_Native.fst b1) e1 in
             if uu____19019
             then
               let uu____19024 =
                 let uu____19035 = FStar_Syntax_Syntax.as_arg exp_unit in
                 [uu____19035] in
               mk_app t uu____19024
             else e1)
    | uu____19062 ->
        let uu____19063 =
          let uu____19074 = FStar_Syntax_Syntax.as_arg exp_unit in
          [uu____19074] in
        mk_app t uu____19063
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) = fun t -> unthunk t
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t ->
    fun universe_of_binders ->
      let list_elements1 e =
        let uu____19135 = list_elements e in
        match uu____19135 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____19170 =
          let uu____19187 = unmeta p in
          FStar_All.pipe_right uu____19187 head_and_args in
        match uu____19170 with
        | (head, args) ->
            let uu____19238 =
              let uu____19253 =
                let uu____19254 = un_uinst head in
                uu____19254.FStar_Syntax_Syntax.n in
              (uu____19253, args) in
            (match uu____19238 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____19276, uu____19277)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____19329 ->
                 let uu____19344 =
                   let uu____19350 =
                     let uu____19352 = tts p in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____19352 in
                   (FStar_Errors.Error_IllSMTPat, uu____19350) in
                 FStar_Errors.raise_error uu____19344
                   p.FStar_Syntax_Syntax.pos) in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____19395 =
            let uu____19412 = unmeta t1 in
            FStar_All.pipe_right uu____19412 head_and_args in
          match uu____19395 with
          | (head, args) ->
              let uu____19459 =
                let uu____19474 =
                  let uu____19475 = un_uinst head in
                  uu____19475.FStar_Syntax_Syntax.n in
                (uu____19474, args) in
              (match uu____19459 with
               | (FStar_Syntax_Syntax.Tm_fvar fv, (e, uu____19494)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____19531 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____19561 = smt_pat_or t1 in
            (match uu____19561 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____19583 = list_elements1 e in
                 FStar_All.pipe_right uu____19583
                   (FStar_List.map
                      (fun branch1 ->
                         let uu____19613 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____19613
                           (FStar_List.map one_pat)))
             | uu____19642 ->
                 let uu____19647 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____19647])
        | uu____19702 ->
            let uu____19705 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____19705] in
      let uu____19760 =
        let uu____19791 =
          let uu____19792 = FStar_Syntax_Subst.compress t in
          uu____19792.FStar_Syntax_Syntax.n in
        match uu____19791 with
        | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
            let uu____19847 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____19847 with
             | (binders1, c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____19914;
                        FStar_Syntax_Syntax.effect_name = uu____19915;
                        FStar_Syntax_Syntax.result_typ = uu____19916;
                        FStar_Syntax_Syntax.effect_args =
                          (pre, uu____19918)::(post, uu____19920)::(pats,
                                                                    uu____19922)::[];
                        FStar_Syntax_Syntax.flags = uu____19923;_}
                      ->
                      let uu____19984 = lemma_pats pats in
                      (binders1, pre, post, uu____19984)
                  | uu____20019 -> failwith "impos"))
        | uu____20051 -> failwith "Impos" in
      match uu____19760 with
      | (binders, pre, post, patterns) ->
          let post1 = unthunk_lemma_post post in
          let body =
            let uu____20135 =
              let uu____20136 =
                let uu____20143 = mk_imp pre post1 in
                let uu____20146 =
                  let uu____20147 =
                    let uu____20168 =
                      FStar_Syntax_Syntax.binders_to_names binders in
                    (uu____20168, patterns) in
                  FStar_Syntax_Syntax.Meta_pattern uu____20147 in
                (uu____20143, uu____20146) in
              FStar_Syntax_Syntax.Tm_meta uu____20136 in
            FStar_Syntax_Syntax.mk uu____20135 t.FStar_Syntax_Syntax.pos in
          let quant =
            let uu____20192 = universe_of_binders binders in
            FStar_List.fold_right2
              (fun b ->
                 fun u ->
                   fun out -> mk_forall u (FStar_Pervasives_Native.fst b) out)
              binders uu____20192 body in
          quant
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____20222 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____20233 -> true
    | uu____20235 -> false
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____20246 -> true
    | uu____20248 -> false
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f ->
    fun combs ->
      let uu____20266 = f combs.FStar_Syntax_Syntax.ret_wp in
      let uu____20267 = f combs.FStar_Syntax_Syntax.bind_wp in
      let uu____20268 = f combs.FStar_Syntax_Syntax.stronger in
      let uu____20269 = f combs.FStar_Syntax_Syntax.if_then_else in
      let uu____20270 = f combs.FStar_Syntax_Syntax.ite_wp in
      let uu____20271 = f combs.FStar_Syntax_Syntax.close_wp in
      let uu____20272 = f combs.FStar_Syntax_Syntax.trivial in
      let uu____20273 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr in
      let uu____20276 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr in
      let uu____20279 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr in
      {
        FStar_Syntax_Syntax.ret_wp = uu____20266;
        FStar_Syntax_Syntax.bind_wp = uu____20267;
        FStar_Syntax_Syntax.stronger = uu____20268;
        FStar_Syntax_Syntax.if_then_else = uu____20269;
        FStar_Syntax_Syntax.ite_wp = uu____20270;
        FStar_Syntax_Syntax.close_wp = uu____20271;
        FStar_Syntax_Syntax.trivial = uu____20272;
        FStar_Syntax_Syntax.repr = uu____20273;
        FStar_Syntax_Syntax.return_repr = uu____20276;
        FStar_Syntax_Syntax.bind_repr = uu____20279
      }
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f ->
    fun combs ->
      let map_tuple uu____20311 =
        match uu____20311 with
        | (ts1, ts2) ->
            let uu____20322 = f ts1 in
            let uu____20323 = f ts2 in (uu____20322, uu____20323) in
      let uu____20324 = map_tuple combs.FStar_Syntax_Syntax.l_repr in
      let uu____20329 = map_tuple combs.FStar_Syntax_Syntax.l_return in
      let uu____20334 = map_tuple combs.FStar_Syntax_Syntax.l_bind in
      let uu____20339 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp in
      let uu____20344 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else in
      {
        FStar_Syntax_Syntax.l_repr = uu____20324;
        FStar_Syntax_Syntax.l_return = uu____20329;
        FStar_Syntax_Syntax.l_bind = uu____20334;
        FStar_Syntax_Syntax.l_subcomp = uu____20339;
        FStar_Syntax_Syntax.l_if_then_else = uu____20344
      }
let (apply_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.eff_combinators ->
      FStar_Syntax_Syntax.eff_combinators)
  =
  fun f ->
    fun combs ->
      match combs with
      | FStar_Syntax_Syntax.Primitive_eff combs1 ->
          let uu____20366 = apply_wp_eff_combinators f combs1 in
          FStar_Syntax_Syntax.Primitive_eff uu____20366
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____20368 = apply_wp_eff_combinators f combs1 in
          FStar_Syntax_Syntax.DM4F_eff uu____20368
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____20370 = apply_layered_eff_combinators f combs1 in
          FStar_Syntax_Syntax.Layered_eff uu____20370
let (get_wp_close_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_Pervasives_Native.Some (combs.FStar_Syntax_Syntax.close_wp)
    | uu____20385 -> FStar_Pervasives_Native.None
let (get_eff_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.repr
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20399 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____20399
          (fun uu____20406 -> FStar_Pervasives_Native.Some uu____20406)
let (get_bind_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.bind_wp
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.bind_wp
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
          FStar_Pervasives_Native.snd
let (get_return_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.ret_wp
    | FStar_Syntax_Syntax.DM4F_eff combs -> combs.FStar_Syntax_Syntax.ret_wp
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
          FStar_Pervasives_Native.snd
let (get_bind_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.bind_repr
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.bind_repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20446 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____20446
          (fun uu____20453 -> FStar_Pervasives_Native.Some uu____20453)
let (get_return_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.return_repr
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.return_repr
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20467 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____20467
          (fun uu____20474 -> FStar_Pervasives_Native.Some uu____20474)
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20488 -> FStar_Pervasives_Native.Some uu____20488)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____20492 -> FStar_Pervasives_Native.Some uu____20492)
    | uu____20493 -> FStar_Pervasives_Native.None
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20505 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____20505
          (fun uu____20512 -> FStar_Pervasives_Native.Some uu____20512)
    | uu____20513 -> FStar_Pervasives_Native.None
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20527 -> FStar_Pervasives_Native.Some uu____20527)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____20531 -> FStar_Pervasives_Native.Some uu____20531)
    | uu____20532 -> FStar_Pervasives_Native.None
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20546 -> FStar_Pervasives_Native.Some uu____20546)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____20550 -> FStar_Pervasives_Native.Some uu____20550)
    | uu____20551 -> FStar_Pervasives_Native.None
let (get_stronger_vc_combinator :
  FStar_Syntax_Syntax.eff_decl -> FStar_Syntax_Syntax.tscheme) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        combs.FStar_Syntax_Syntax.stronger
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        combs.FStar_Syntax_Syntax.stronger
    | FStar_Syntax_Syntax.Layered_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
          FStar_Pervasives_Native.snd
let (get_stronger_repr :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff uu____20575 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____20576 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____20578 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____20578
          (fun uu____20585 -> FStar_Pervasives_Native.Some uu____20585)