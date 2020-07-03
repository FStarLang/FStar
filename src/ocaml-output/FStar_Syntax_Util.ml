open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t ->
    let uu____20 = FStar_ST.op_Bang tts_f in
    match uu____20 with
    | FStar_Pervasives_Native.None -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid ->
    let uu____57 =
      let uu____58 = FStar_Ident.ns_of_lid lid in
      let uu____61 =
        let uu____64 =
          let uu____65 =
            let uu____70 =
              let uu____71 =
                let uu____72 =
                  let uu____73 = FStar_Ident.ident_of_lid lid in
                  FStar_Ident.string_of_id uu____73 in
                Prims.op_Hat "is_" uu____72 in
              Prims.op_Hat FStar_Ident.reserved_prefix uu____71 in
            let uu____74 = FStar_Ident.range_of_lid lid in
            (uu____70, uu____74) in
          FStar_Ident.mk_ident uu____65 in
        [uu____64] in
      FStar_List.append uu____58 uu____61 in
    FStar_Ident.lid_of_ids uu____57
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid ->
    let c =
      let uu____81 =
        let uu____82 = FStar_Ident.ident_of_lid lid in
        FStar_Ident.string_of_id uu____82 in
      FStar_Util.char_at uu____81 Prims.int_zero in
    FStar_Util.is_upper c
let arg_of_non_null_binder :
  'uuuuuu87 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu87) ->
      (FStar_Syntax_Syntax.term * 'uuuuuu87)
  =
  fun uu____100 ->
    match uu____100 with
    | (b, imp) ->
        let uu____107 = FStar_Syntax_Syntax.bv_to_name b in (uu____107, imp)
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b ->
            let uu____158 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____158
            then []
            else (let uu____174 = arg_of_non_null_binder b in [uu____174])))
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders ->
    let uu____208 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b ->
              let uu____290 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____290
              then
                let b1 =
                  let uu____314 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                  (uu____314, (FStar_Pervasives_Native.snd b)) in
                let uu____321 = arg_of_non_null_binder b1 in (b1, uu____321)
              else
                (let uu____343 = arg_of_non_null_binder b in (b, uu____343)))) in
    FStar_All.pipe_right uu____208 FStar_List.unzip
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
              let uu____475 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____475
              then
                let uu____482 = b in
                match uu____482 with
                | (a, imp) ->
                    let b1 =
                      let uu____502 =
                        let uu____503 = FStar_Util.string_of_int i in
                        Prims.op_Hat "_" uu____503 in
                      FStar_Ident.id_of_text uu____502 in
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
        let uu____543 =
          let uu____544 =
            let uu____559 = name_binders binders in (uu____559, comp) in
          FStar_Syntax_Syntax.Tm_arrow uu____544 in
        FStar_Syntax_Syntax.mk uu____543 t.FStar_Syntax_Syntax.pos
    | uu____578 -> t
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____614 ->
            match uu____614 with
            | (t, imp) ->
                let uu____625 =
                  let uu____626 = FStar_Syntax_Syntax.null_binder t in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____626 in
                (uu____625, imp)))
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____680 ->
            match uu____680 with
            | (t, imp) ->
                let uu____697 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t in
                (uu____697, imp)))
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs ->
    let uu____709 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____709
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
let mk_subst : 'uuuuuu720 . 'uuuuuu720 -> 'uuuuuu720 Prims.list =
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
          (fun uu____840 ->
             fun uu____841 ->
               match (uu____840, uu____841) with
               | ((x, uu____867), (y, uu____869)) ->
                   let uu____890 =
                     let uu____897 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu____897) in
                   FStar_Syntax_Syntax.NT uu____890) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2, uu____910) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2, uu____916, uu____917) -> unmeta e2
    | uu____958 -> e1
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e', m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____971 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____978 -> e1
         | uu____987 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2, uu____989, uu____990) ->
        unmeta_safe e2
    | uu____1031 -> e1
let (unmeta_lift : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____1037 =
      let uu____1038 = FStar_Syntax_Subst.compress t in
      uu____1038.FStar_Syntax_Syntax.n in
    match uu____1037 with
    | FStar_Syntax_Syntax.Tm_meta
        (t1, FStar_Syntax_Syntax.Meta_monadic_lift uu____1042) -> t1
    | uu____1055 -> t
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u ->
    match u with
    | FStar_Syntax_Syntax.U_unknown -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_name uu____1069 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_unif uu____1070 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_max uu____1081 -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_zero -> (u, Prims.int_zero)
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____1085 = univ_kernel u1 in
        (match uu____1085 with | (k, n) -> (k, (n + Prims.int_one)))
    | FStar_Syntax_Syntax.U_bvar uu____1096 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u ->
    let uu____1106 = univ_kernel u in FStar_Pervasives_Native.snd uu____1106
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1 ->
    fun u2 ->
      let rec compare_kernel uk1 uk2 =
        match (uk1, uk2) with
        | (FStar_Syntax_Syntax.U_bvar uu____1132, uu____1133) ->
            failwith "Impossible: compare_kernel bvar"
        | (uu____1134, FStar_Syntax_Syntax.U_bvar uu____1135) ->
            failwith "Impossible: compare_kernel bvar"
        | (FStar_Syntax_Syntax.U_succ uu____1136, uu____1137) ->
            failwith "Impossible: compare_kernel succ"
        | (uu____1138, FStar_Syntax_Syntax.U_succ uu____1139) ->
            failwith "Impossible: compare_kernel succ"
        | (FStar_Syntax_Syntax.U_unknown, FStar_Syntax_Syntax.U_unknown) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_unknown, uu____1140) -> ~- Prims.int_one
        | (uu____1141, FStar_Syntax_Syntax.U_unknown) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) ->
            Prims.int_zero
        | (FStar_Syntax_Syntax.U_zero, uu____1142) -> ~- Prims.int_one
        | (uu____1143, FStar_Syntax_Syntax.U_zero) -> Prims.int_one
        | (FStar_Syntax_Syntax.U_name u11, FStar_Syntax_Syntax.U_name u21) ->
            let uu____1146 = FStar_Ident.string_of_id u11 in
            let uu____1147 = FStar_Ident.string_of_id u21 in
            FStar_String.compare uu____1146 uu____1147
        | (FStar_Syntax_Syntax.U_name uu____1148, uu____1149) ->
            ~- Prims.int_one
        | (uu____1150, FStar_Syntax_Syntax.U_name uu____1151) ->
            Prims.int_one
        | (FStar_Syntax_Syntax.U_unif u11, FStar_Syntax_Syntax.U_unif u21) ->
            let uu____1174 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
            let uu____1175 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
            uu____1174 - uu____1175
        | (FStar_Syntax_Syntax.U_unif uu____1176, uu____1177) ->
            ~- Prims.int_one
        | (uu____1188, FStar_Syntax_Syntax.U_unif uu____1189) ->
            Prims.int_one
        | (FStar_Syntax_Syntax.U_max us1, FStar_Syntax_Syntax.U_max us2) ->
            let n1 = FStar_List.length us1 in
            let n2 = FStar_List.length us2 in
            if n1 <> n2
            then n1 - n2
            else
              (let copt =
                 let uu____1212 = FStar_List.zip us1 us2 in
                 FStar_Util.find_map uu____1212
                   (fun uu____1227 ->
                      match uu____1227 with
                      | (u11, u21) ->
                          let c = compare_univs u11 u21 in
                          if c <> Prims.int_zero
                          then FStar_Pervasives_Native.Some c
                          else FStar_Pervasives_Native.None) in
               match copt with
               | FStar_Pervasives_Native.None -> Prims.int_zero
               | FStar_Pervasives_Native.Some c -> c) in
      let uu____1241 = univ_kernel u1 in
      match uu____1241 with
      | (uk1, n1) ->
          let uu____1248 = univ_kernel u2 in
          (match uu____1248 with
           | (uk2, n2) ->
               let uu____1255 = compare_kernel uk1 uk2 in
               (match uu____1255 with
                | uu____1256 when uu____1256 = Prims.int_zero -> n1 - n2
                | n -> n))
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1 ->
    fun u2 ->
      let uu____1268 = compare_univs u1 u2 in uu____1268 = Prims.int_zero
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t ->
    fun r ->
      let uu____1283 =
        let uu____1284 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____1284;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        } in
      FStar_Syntax_Syntax.mk_Comp uu____1283
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____1303 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____1312 ->
        FStar_Parser_Const.effect_GTot_lid
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____1334 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____1343 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t, u_opt) ->
        let uu____1369 =
          let uu____1370 = FStar_Util.map_opt u_opt (fun x -> [x]) in
          FStar_Util.dflt [] uu____1370 in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1369;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t, u_opt) ->
        let uu____1399 =
          let uu____1400 = FStar_Util.map_opt u_opt (fun x -> [x]) in
          FStar_Util.dflt [] uu____1400 in
        {
          FStar_Syntax_Syntax.comp_univs = uu____1399;
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
      let uu___239_1435 = c in
      let uu____1436 =
        let uu____1437 =
          let uu___241_1438 = comp_to_comp_typ_nouniv c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___241_1438.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___241_1438.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___241_1438.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___241_1438.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____1437 in
      {
        FStar_Syntax_Syntax.n = uu____1436;
        FStar_Syntax_Syntax.pos = (uu___239_1435.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___239_1435.FStar_Syntax_Syntax.vars)
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
    | uu____1477 ->
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
          let err1 uu____1509 =
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEffect, err) r in
          let repr1 = FStar_Syntax_Subst.compress repr in
          if is_layered
          then
            match repr1.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_app (uu____1517, uu____1518::is) ->
                FStar_All.pipe_right is
                  (FStar_List.map FStar_Pervasives_Native.fst)
            | uu____1586 -> err1 ()
          else
            (match repr1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_arrow (uu____1590, c) ->
                 let uu____1612 = FStar_All.pipe_right c comp_to_comp_typ in
                 FStar_All.pipe_right uu____1612
                   (fun ct ->
                      FStar_All.pipe_right ct.FStar_Syntax_Syntax.effect_args
                        (FStar_List.map FStar_Pervasives_Native.fst))
             | uu____1647 -> err1 ())
let (destruct_comp :
  FStar_Syntax_Syntax.comp_typ ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.typ *
      FStar_Syntax_Syntax.typ))
  =
  fun c ->
    let wp =
      match c.FStar_Syntax_Syntax.effect_args with
      | (wp, uu____1667)::[] -> wp
      | uu____1692 ->
          let uu____1703 =
            let uu____1704 =
              FStar_Ident.string_of_lid c.FStar_Syntax_Syntax.effect_name in
            let uu____1705 =
              let uu____1706 =
                FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args
                  FStar_List.length in
              FStar_All.pipe_right uu____1706 FStar_Util.string_of_int in
            FStar_Util.format2
              "Impossible: Got a computation %s with %s effect args"
              uu____1704 uu____1705 in
          failwith uu____1703 in
    let uu____1725 = FStar_List.hd c.FStar_Syntax_Syntax.comp_univs in
    (uu____1725, (c.FStar_Syntax_Syntax.result_typ), wp)
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____1736 -> true
    | FStar_Syntax_Syntax.GTotal uu____1745 -> false
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___0_1766 ->
               match uu___0_1766 with
               | FStar_Syntax_Syntax.TOTAL -> true
               | FStar_Syntax_Syntax.RETURN -> true
               | uu____1767 -> false)))
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___1_1780 ->
            match uu___1_1780 with
            | FStar_Syntax_Syntax.RETURN -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN -> true
            | uu____1781 -> false))
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
    | FStar_Syntax_Syntax.Total uu____1805 -> true
    | FStar_Syntax_Syntax.GTotal uu____1814 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___2_1827 ->
                   match uu___2_1827 with
                   | FStar_Syntax_Syntax.LEMMA -> true
                   | uu____1828 -> false)))
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
    let uu____1858 =
      let uu____1859 = FStar_Syntax_Subst.compress t in
      uu____1859.FStar_Syntax_Syntax.n in
    match uu____1858 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1862, c) -> is_pure_or_ghost_comp c
    | uu____1884 -> true
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____1895 -> false
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____1901 =
      let uu____1902 = FStar_Syntax_Subst.compress t in
      uu____1902.FStar_Syntax_Syntax.n in
    match uu____1901 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1905, c) -> is_lemma_comp c
    | uu____1927 -> false
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____1933 =
      let uu____1934 = FStar_Syntax_Subst.compress t in
      uu____1934.FStar_Syntax_Syntax.n in
    match uu____1933 with
    | FStar_Syntax_Syntax.Tm_app (t1, uu____1938) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1, uu____1964) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____2001, t1, uu____2003) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____2029, uu____2030) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1, uu____2072) -> head_of t1
    | uu____2077 -> t
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
    | uu____2154 -> (t1, [])
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
        let uu____2235 = head_and_args' head in
        (match uu____2235 with
         | (head1, args') -> (head1, (FStar_List.append args' args)))
    | uu____2304 -> (t1, [])
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2, uu____2330) ->
        FStar_Syntax_Subst.compress t2
    | uu____2335 -> t1
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
                (fun uu___3_2349 ->
                   match uu___3_2349 with
                   | FStar_Syntax_Syntax.MLEFFECT -> true
                   | uu____2350 -> false)))
    | uu____2351 -> false
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t, uu____2366) -> t
    | FStar_Syntax_Syntax.GTotal (t, uu____2376) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c ->
    fun t ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____2404 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____2413 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___401_2425 = ct in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___401_2425.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___401_2425.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___401_2425.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___401_2425.FStar_Syntax_Syntax.flags)
             })
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___4_2438 ->
            match uu___4_2438 with
            | FStar_Syntax_Syntax.TOTAL -> true
            | FStar_Syntax_Syntax.RETURN -> true
            | uu____2439 -> false))
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____2445 -> []
    | FStar_Syntax_Syntax.GTotal uu____2462 -> []
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
    | uu____2499 -> false
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2, uu____2507, uu____2508) ->
        unascribe e2
    | uu____2549 -> e1
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
      | FStar_Syntax_Syntax.Tm_ascribed (t', uu____2601, uu____2602) ->
          ascribe t' k
      | uu____2643 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            t.FStar_Syntax_Syntax.pos
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i ->
    let uu____2669 =
      let uu____2678 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser in
      FStar_Util.must uu____2678 in
    uu____2669 i.FStar_Syntax_Syntax.lkind i
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____2720 =
      let uu____2721 = FStar_Syntax_Subst.compress t in
      uu____2721.FStar_Syntax_Syntax.n in
    match uu____2720 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____2725 = unfold_lazy i in
        FStar_All.pipe_left unlazy uu____2725
    | uu____2726 -> t
let (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____2732 =
      let uu____2733 = FStar_Syntax_Subst.compress t in
      uu____2733.FStar_Syntax_Syntax.n in
    match uu____2732 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____2737 ->
             let uu____2746 = unfold_lazy i in
             FStar_All.pipe_left unlazy uu____2746
         | uu____2747 -> t)
    | uu____2748 -> t
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
      | uu____2759 -> false
let unlazy_as_t :
  'uuuuuu2770 .
    FStar_Syntax_Syntax.lazy_kind -> FStar_Syntax_Syntax.term -> 'uuuuuu2770
  =
  fun k ->
    fun t ->
      let uu____2781 =
        let uu____2782 = FStar_Syntax_Subst.compress t in
        uu____2782.FStar_Syntax_Syntax.n in
      match uu____2781 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____2787;
            FStar_Syntax_Syntax.rng = uu____2788;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v
      | uu____2791 -> failwith "Not a Tm_lazy of the expected kind"
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
            let uu____2830 = FStar_Dyn.mkdyn t in
            {
              FStar_Syntax_Syntax.blob = uu____2830;
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
    let uu____2840 =
      let uu____2855 = unascribe t in head_and_args' uu____2855 in
    match uu____2840 with
    | (hd, args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd args t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee -> match projectee with | Equal -> true | uu____2883 -> false
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee ->
    match projectee with | NotEqual -> true | uu____2889 -> false
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee ->
    match projectee with | Unknown -> true | uu____2895 -> false
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
      | (NotEqual, uu____2908) -> NotEqual
      | (uu____2909, NotEqual) -> NotEqual
      | (Unknown, uu____2910) -> Unknown
      | (uu____2911, Unknown) -> Unknown
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1 ->
    fun t2 ->
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      let equal_if uu___5_3013 = if uu___5_3013 then Equal else Unknown in
      let equal_iff uu___6_3020 = if uu___6_3020 then Equal else NotEqual in
      let eq_and f g = match f with | Equal -> g () | uu____3038 -> Unknown in
      let equal_data f1 args1 f2 args2 =
        let uu____3060 = FStar_Syntax_Syntax.fv_eq f1 f2 in
        if uu____3060
        then
          let uu____3062 = FStar_List.zip args1 args2 in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc ->
                  fun uu____3139 ->
                    match uu____3139 with
                    | ((a1, q1), (a2, q2)) ->
                        let uu____3180 = eq_tm a1 a2 in eq_inj acc uu____3180)
               Equal) uu____3062
        else NotEqual in
      let heads_and_args_in_case_both_data =
        let uu____3193 =
          let uu____3210 = FStar_All.pipe_right t11 unmeta in
          FStar_All.pipe_right uu____3210 head_and_args in
        match uu____3193 with
        | (head1, args1) ->
            let uu____3263 =
              let uu____3280 = FStar_All.pipe_right t21 unmeta in
              FStar_All.pipe_right uu____3280 head_and_args in
            (match uu____3263 with
             | (head2, args2) ->
                 let uu____3333 =
                   let uu____3338 =
                     let uu____3339 = un_uinst head1 in
                     uu____3339.FStar_Syntax_Syntax.n in
                   let uu____3342 =
                     let uu____3343 = un_uinst head2 in
                     uu____3343.FStar_Syntax_Syntax.n in
                   (uu____3338, uu____3342) in
                 (match uu____3333 with
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
                  | uu____3370 -> FStar_Pervasives_Native.None)) in
      let t12 = unmeta t11 in
      let t22 = unmeta t21 in
      match ((t12.FStar_Syntax_Syntax.n), (t22.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar bv1, FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____3387, uu____3388) ->
          let uu____3389 = unlazy t12 in eq_tm uu____3389 t22
      | (uu____3390, FStar_Syntax_Syntax.Tm_lazy uu____3391) ->
          let uu____3392 = unlazy t22 in eq_tm t12 uu____3392
      | (FStar_Syntax_Syntax.Tm_name a, FStar_Syntax_Syntax.Tm_name b) ->
          let uu____3395 = FStar_Syntax_Syntax.bv_eq a b in
          equal_if uu____3395
      | uu____3396 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____3419 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must in
          FStar_All.pipe_right uu____3419
            (fun uu____3467 ->
               match uu____3467 with
               | (f, args1, g, args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f, FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____3482 = FStar_Syntax_Syntax.fv_eq f g in
          equal_if uu____3482
      | (FStar_Syntax_Syntax.Tm_uinst (f, us), FStar_Syntax_Syntax.Tm_uinst
         (g, vs)) ->
          let uu____3495 = eq_tm f g in
          eq_and uu____3495
            (fun uu____3498 ->
               let uu____3499 = eq_univs_list us vs in equal_if uu____3499)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3500), uu____3501) -> Unknown
      | (uu____3502, FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____3503)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c, FStar_Syntax_Syntax.Tm_constant
         d) ->
          let uu____3506 = FStar_Const.eq_const c d in equal_iff uu____3506
      | (FStar_Syntax_Syntax.Tm_uvar (u1, ([], uu____3508)),
         FStar_Syntax_Syntax.Tm_uvar (u2, ([], uu____3510))) ->
          let uu____3539 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head in
          equal_if uu____3539
      | (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app
         (h2, args2)) ->
          let uu____3592 =
            let uu____3597 =
              let uu____3598 = un_uinst h1 in
              uu____3598.FStar_Syntax_Syntax.n in
            let uu____3601 =
              let uu____3602 = un_uinst h2 in
              uu____3602.FStar_Syntax_Syntax.n in
            (uu____3597, uu____3601) in
          (match uu____3592 with
           | (FStar_Syntax_Syntax.Tm_fvar f1, FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____3608 =
                    let uu____3609 = FStar_Syntax_Syntax.lid_of_fv f1 in
                    FStar_Ident.string_of_lid uu____3609 in
                  FStar_List.mem uu____3608 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____3610 ->
               let uu____3615 = eq_tm h1 h2 in
               eq_and uu____3615 (fun uu____3617 -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t13, bs1),
         FStar_Syntax_Syntax.Tm_match (t23, bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____3722 = FStar_List.zip bs1 bs2 in
            let uu____3785 = eq_tm t13 t23 in
            FStar_List.fold_right
              (fun uu____3822 ->
                 fun a ->
                   match uu____3822 with
                   | (b1, b2) ->
                       eq_and a (fun uu____3915 -> branch_matches b1 b2))
              uu____3722 uu____3785
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u, FStar_Syntax_Syntax.Tm_type v) ->
          let uu____3919 = eq_univs u v in equal_if uu____3919
      | (FStar_Syntax_Syntax.Tm_quoted (t13, q1),
         FStar_Syntax_Syntax.Tm_quoted (t23, q2)) ->
          let uu____3932 = eq_quoteinfo q1 q2 in
          eq_and uu____3932 (fun uu____3934 -> eq_tm t13 t23)
      | (FStar_Syntax_Syntax.Tm_refine (t13, phi1),
         FStar_Syntax_Syntax.Tm_refine (t23, phi2)) ->
          let uu____3947 =
            eq_tm t13.FStar_Syntax_Syntax.sort t23.FStar_Syntax_Syntax.sort in
          eq_and uu____3947 (fun uu____3949 -> eq_tm phi1 phi2)
      | uu____3950 -> Unknown
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
      | ([], uu____4020) -> NotEqual
      | (uu____4051, []) -> NotEqual
      | ((x1, t1)::a11, (x2, t2)::a21) ->
          let uu____4140 =
            let uu____4141 = FStar_Syntax_Syntax.bv_eq x1 x2 in
            Prims.op_Negation uu____4141 in
          if uu____4140
          then NotEqual
          else
            (let uu____4143 = eq_tm t1 t2 in
             match uu____4143 with
             | NotEqual -> NotEqual
             | Unknown ->
                 let uu____4144 = eq_antiquotes a11 a21 in
                 (match uu____4144 with
                  | NotEqual -> NotEqual
                  | uu____4145 -> Unknown)
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
        | (uu____4224, uu____4225) -> false in
      let uu____4234 = b1 in
      match uu____4234 with
      | (p1, w1, t1) ->
          let uu____4268 = b2 in
          (match uu____4268 with
           | (p2, w2, t2) ->
               let uu____4302 = FStar_Syntax_Syntax.eq_pat p1 p2 in
               if uu____4302
               then
                 let uu____4303 =
                   (let uu____4306 = eq_tm t1 t2 in uu____4306 = Equal) &&
                     (related_by
                        (fun t11 ->
                           fun t21 ->
                             let uu____4315 = eq_tm t11 t21 in
                             uu____4315 = Equal) w1 w2) in
                 (if uu____4303 then Equal else Unknown)
               else Unknown)
and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | ([], []) -> Equal
      | ((a, uu____4377)::a11, (b, uu____4380)::b1) ->
          let uu____4454 = eq_tm a b in
          (match uu____4454 with
           | Equal -> eq_args a11 b1
           | uu____4455 -> Unknown)
      | uu____4456 -> Unknown
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
      | (FStar_Pervasives_Native.None, uu____4509) -> NotEqual
      | (uu____4516, FStar_Pervasives_Native.None) -> NotEqual
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
      | uu____4553 -> NotEqual
let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x, uu____4569) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____4575, uu____4576) ->
        unrefine t2
    | uu____4617 -> t1
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____4623 =
      let uu____4624 = FStar_Syntax_Subst.compress t in
      uu____4624.FStar_Syntax_Syntax.n in
    match uu____4623 with
    | FStar_Syntax_Syntax.Tm_uvar uu____4627 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu____4641) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____4646 ->
        let uu____4663 =
          let uu____4664 = FStar_All.pipe_right t head_and_args in
          FStar_All.pipe_right uu____4664 FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____4663 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1, uu____4726, uu____4727) ->
        is_uvar t1
    | uu____4768 -> false
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____4774 =
      let uu____4775 = unrefine t in uu____4775.FStar_Syntax_Syntax.n in
    match uu____4774 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head, uu____4780) -> is_unit head
    | FStar_Syntax_Syntax.Tm_uinst (t1, uu____4806) -> is_unit t1
    | uu____4811 -> false
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____4817 =
      let uu____4818 = FStar_Syntax_Subst.compress t in
      uu____4818.FStar_Syntax_Syntax.n in
    match uu____4817 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____4822 -> false
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e ->
    let uu____4828 =
      let uu____4829 = FStar_Syntax_Subst.compress e in
      uu____4829.FStar_Syntax_Syntax.n in
    match uu____4828 with
    | FStar_Syntax_Syntax.Tm_abs uu____4832 -> true
    | uu____4851 -> false
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____4857 =
      let uu____4858 = FStar_Syntax_Subst.compress t in
      uu____4858.FStar_Syntax_Syntax.n in
    match uu____4857 with
    | FStar_Syntax_Syntax.Tm_arrow uu____4861 -> true
    | uu____4876 -> false
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x, uu____4884) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____4890, uu____4891) ->
        pre_typ t2
    | uu____4932 -> t1
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
      let uu____4956 =
        let uu____4957 = un_uinst typ1 in uu____4957.FStar_Syntax_Syntax.n in
      match uu____4956 with
      | FStar_Syntax_Syntax.Tm_app (head, args) ->
          let head1 = un_uinst head in
          (match head1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____5022 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____5052 -> FStar_Pervasives_Native.None
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____5072, lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids, uu____5079) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____5084, lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid, uu____5095, uu____5096, uu____5097, uu____5098, uu____5099) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid, uu____5109, uu____5110, uu____5111, uu____5112) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid, uu____5118, uu____5119, uu____5120, uu____5121, uu____5122) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____5128, uu____5129) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid, uu____5131, uu____5132) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect n -> [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____5134 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____5135 -> []
    | FStar_Syntax_Syntax.Sig_fail uu____5136 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____5147 -> []
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____5158 -> []
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____5179 -> FStar_Pervasives_Native.None
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x -> x.FStar_Syntax_Syntax.sigquals
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x -> x.FStar_Syntax_Syntax.sigrng
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___7_5202 ->
    match uu___7_5202 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
let range_of_arg :
  'uuuuuu5215 'uuuuuu5216 .
    ('uuuuuu5215 FStar_Syntax_Syntax.syntax * 'uuuuuu5216) ->
      FStar_Range.range
  =
  fun uu____5227 ->
    match uu____5227 with | (hd, uu____5235) -> hd.FStar_Syntax_Syntax.pos
let range_of_args :
  'uuuuuu5248 'uuuuuu5249 .
    ('uuuuuu5248 FStar_Syntax_Syntax.syntax * 'uuuuuu5249) Prims.list ->
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
      | uu____5346 ->
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
      let uu____5404 =
        FStar_List.map
          (fun uu____5431 ->
             match uu____5431 with
             | (bv, aq) ->
                 let uu____5450 = FStar_Syntax_Syntax.bv_to_name bv in
                 (uu____5450, aq)) bs in
      mk_app f uu____5404
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
          (let uu____5481 =
             let uu____5486 =
               let uu____5487 =
                 let uu____5488 = FStar_Ident.ident_of_lid lid in
                 FStar_Ident.string_of_id uu____5488 in
               mk_field_projector_name_from_string uu____5487 itext in
             let uu____5489 = FStar_Ident.range_of_id i in
             (uu____5486, uu____5489) in
           FStar_Ident.mk_ident uu____5481) in
      let uu____5490 =
        let uu____5491 = FStar_Ident.ns_of_lid lid in
        FStar_List.append uu____5491 [newi] in
      FStar_Ident.lid_of_ids uu____5490
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv -> Prims.int -> FStar_Ident.lident)
  =
  fun lid ->
    fun x ->
      fun i ->
        let nm =
          let uu____5510 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____5510
          then
            let uu____5511 =
              let uu____5516 =
                let uu____5517 = FStar_Util.string_of_int i in
                Prims.op_Hat "_" uu____5517 in
              let uu____5518 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____5516, uu____5518) in
            FStar_Ident.mk_ident uu____5511
          else x.FStar_Syntax_Syntax.ppname in
        mk_field_projector_name_from_ident lid nm
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses, uu____5530) -> ses
    | uu____5539 -> failwith "ses_of_sigbundle: not a Sig_bundle"
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv ->
    fun t ->
      let uu____5552 = FStar_Syntax_Unionfind.find uv in
      match uu____5552 with
      | FStar_Pervasives_Native.Some uu____5555 ->
          let uu____5556 =
            let uu____5557 =
              let uu____5558 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____5558 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____5557 in
          failwith uu____5556
      | uu____5559 -> FStar_Syntax_Unionfind.change uv t
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
            (let uu____5580 = FStar_Ident.string_of_id l1b in
             let uu____5581 = FStar_Ident.string_of_id l2b in
             uu____5580 = uu____5581)
      | (FStar_Syntax_Syntax.RecordType (ns1, f1),
         FStar_Syntax_Syntax.RecordType (ns2, f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1 ->
                    fun x2 ->
                      let uu____5608 = FStar_Ident.string_of_id x1 in
                      let uu____5609 = FStar_Ident.string_of_id x2 in
                      uu____5608 = uu____5609) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1 ->
                  fun x2 ->
                    let uu____5616 = FStar_Ident.string_of_id x1 in
                    let uu____5617 = FStar_Ident.string_of_id x2 in
                    uu____5616 = uu____5617) f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor (ns1, f1),
         FStar_Syntax_Syntax.RecordConstructor (ns2, f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1 ->
                    fun x2 ->
                      let uu____5644 = FStar_Ident.string_of_id x1 in
                      let uu____5645 = FStar_Ident.string_of_id x2 in
                      uu____5644 = uu____5645) f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1 ->
                  fun x2 ->
                    let uu____5652 = FStar_Ident.string_of_id x1 in
                    let uu____5653 = FStar_Ident.string_of_id x2 in
                    uu____5652 = uu____5653) f1 f2)
      | uu____5654 -> q1 = q2
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
              let uu____5699 =
                let uu___1040_5700 = rc in
                let uu____5701 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs) in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1040_5700.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____5701;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1040_5700.FStar_Syntax_Syntax.residual_flags)
                } in
              FStar_Pervasives_Native.Some uu____5699 in
        match bs with
        | [] -> t
        | uu____5718 ->
            let body =
              let uu____5720 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____5720 in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs', t1, lopt') ->
                 let uu____5750 =
                   let uu____5751 =
                     let uu____5770 =
                       let uu____5779 = FStar_Syntax_Subst.close_binders bs in
                       FStar_List.append uu____5779 bs' in
                     let uu____5794 = close_lopt lopt' in
                     (uu____5770, t1, uu____5794) in
                   FStar_Syntax_Syntax.Tm_abs uu____5751 in
                 FStar_Syntax_Syntax.mk uu____5750 t1.FStar_Syntax_Syntax.pos
             | uu____5809 ->
                 let uu____5810 =
                   let uu____5811 =
                     let uu____5830 = FStar_Syntax_Subst.close_binders bs in
                     let uu____5839 = close_lopt lopt in
                     (uu____5830, body, uu____5839) in
                   FStar_Syntax_Syntax.Tm_abs uu____5811 in
                 FStar_Syntax_Syntax.mk uu____5810 t.FStar_Syntax_Syntax.pos)
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
      | uu____5894 ->
          let uu____5903 =
            let uu____5904 =
              let uu____5919 = FStar_Syntax_Subst.close_binders bs in
              let uu____5928 = FStar_Syntax_Subst.close_comp bs c in
              (uu____5919, uu____5928) in
            FStar_Syntax_Syntax.Tm_arrow uu____5904 in
          FStar_Syntax_Syntax.mk uu____5903 c.FStar_Syntax_Syntax.pos
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs ->
    fun c ->
      let t = arrow bs c in
      let uu____5976 =
        let uu____5977 = FStar_Syntax_Subst.compress t in
        uu____5977.FStar_Syntax_Syntax.n in
      match uu____5976 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1, c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres, uu____6007) ->
               let uu____6016 =
                 let uu____6017 = FStar_Syntax_Subst.compress tres in
                 uu____6017.FStar_Syntax_Syntax.n in
               (match uu____6016 with
                | FStar_Syntax_Syntax.Tm_arrow (bs', c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      t.FStar_Syntax_Syntax.pos
                | uu____6060 -> t)
           | uu____6061 -> t)
      | uu____6062 -> t
let rec (canon_arrow :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let uu____6074 =
      let uu____6075 = FStar_Syntax_Subst.compress t in
      uu____6075.FStar_Syntax_Syntax.n in
    match uu____6074 with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let cn =
          match c.FStar_Syntax_Syntax.n with
          | FStar_Syntax_Syntax.Total (t1, u) ->
              let uu____6113 =
                let uu____6122 = canon_arrow t1 in (uu____6122, u) in
              FStar_Syntax_Syntax.Total uu____6113
          | uu____6129 -> c.FStar_Syntax_Syntax.n in
        let c1 =
          let uu___1084_6133 = c in
          {
            FStar_Syntax_Syntax.n = cn;
            FStar_Syntax_Syntax.pos =
              (uu___1084_6133.FStar_Syntax_Syntax.pos);
            FStar_Syntax_Syntax.vars =
              (uu___1084_6133.FStar_Syntax_Syntax.vars)
          } in
        flat_arrow bs c1
    | uu____6136 -> t
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b ->
    fun t ->
      let uu____6153 =
        let uu____6154 =
          let uu____6161 =
            let uu____6164 =
              let uu____6165 = FStar_Syntax_Syntax.mk_binder b in
              [uu____6165] in
            FStar_Syntax_Subst.close uu____6164 t in
          (b, uu____6161) in
        FStar_Syntax_Syntax.Tm_refine uu____6154 in
      let uu____6186 =
        let uu____6187 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____6187 t.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk uu____6153 uu____6186
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b -> FStar_Syntax_Subst.close_branch b
let (has_decreases : FStar_Syntax_Syntax.comp -> Prims.bool) =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____6199 =
          FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
            (FStar_Util.find_opt
               (fun uu___8_6208 ->
                  match uu___8_6208 with
                  | FStar_Syntax_Syntax.DECREASES uu____6209 -> true
                  | uu____6212 -> false)) in
        (match uu____6199 with
         | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES d) ->
             true
         | uu____6216 -> false)
    | uu____6219 -> false
let rec (arrow_formals_comp_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____6272 =
          (is_total_comp c) &&
            (let uu____6274 = has_decreases c in Prims.op_Negation uu____6274) in
        if uu____6272
        then
          let uu____6287 = arrow_formals_comp_ln (comp_result c) in
          (match uu____6287 with
           | (bs', k2) -> ((FStar_List.append bs bs'), k2))
        else (bs, c)
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6353;
           FStar_Syntax_Syntax.index = uu____6354;
           FStar_Syntax_Syntax.sort = s;_},
         uu____6356)
        ->
        let rec aux s1 k2 =
          let uu____6386 =
            let uu____6387 = FStar_Syntax_Subst.compress s1 in
            uu____6387.FStar_Syntax_Syntax.n in
          match uu____6386 with
          | FStar_Syntax_Syntax.Tm_arrow uu____6402 ->
              arrow_formals_comp_ln s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____6417;
                 FStar_Syntax_Syntax.index = uu____6418;
                 FStar_Syntax_Syntax.sort = s2;_},
               uu____6420)
              -> aux s2 k2
          | uu____6427 ->
              let uu____6428 = FStar_Syntax_Syntax.mk_Total k2 in
              ([], uu____6428) in
        aux s k1
    | uu____6443 ->
        let uu____6444 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____6444)
let (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp))
  =
  fun k ->
    let uu____6468 = arrow_formals_comp_ln k in
    match uu____6468 with | (bs, c) -> FStar_Syntax_Subst.open_comp bs c
let (arrow_formals_ln :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k ->
    let uu____6522 = arrow_formals_comp_ln k in
    match uu____6522 with | (bs, c) -> (bs, (comp_result c))
let (arrow_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k ->
    let uu____6588 = arrow_formals_comp k in
    match uu____6588 with | (bs, c) -> (bs, (comp_result c))
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let uu____6685 = FStar_Syntax_Subst.open_comp bs c in
          (match uu____6685 with
           | (bs1, c1) ->
               let ct = comp_to_comp_typ c1 in
               let uu____6709 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___9_6718 ->
                         match uu___9_6718 with
                         | FStar_Syntax_Syntax.DECREASES uu____6719 -> true
                         | uu____6722 -> false)) in
               (match uu____6709 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____6756 ->
                    let uu____6759 = is_total_comp c1 in
                    if uu____6759
                    then
                      let uu____6776 = arrow_until_decreases (comp_result c1) in
                      (match uu____6776 with
                       | (bs', d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____6868;
             FStar_Syntax_Syntax.index = uu____6869;
             FStar_Syntax_Syntax.sort = k2;_},
           uu____6871)
          -> arrow_until_decreases k2
      | uu____6878 -> ([], FStar_Pervasives_Native.None) in
    let uu____6899 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp in
    match uu____6899 with
    | (bs, dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs in
        let uu____6951 =
          FStar_Util.map_opt dopt
            (fun d ->
               let d_bvs = FStar_Syntax_Free.names d in
               let uu____6970 =
                 FStar_Common.tabulate n_univs (fun uu____6974 -> false) in
               let uu____6975 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____6997 ->
                         match uu____6997 with
                         | (x, uu____7005) -> FStar_Util.set_mem x d_bvs)) in
               FStar_List.append uu____6970 uu____6975) in
        ((n_univs + (FStar_List.length bs)), uu____6951)
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____7057 =
            let uu___1194_7058 = rc in
            let uu____7059 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1194_7058.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____7059;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1194_7058.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____7057
      | uu____7068 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____7102 =
        let uu____7103 =
          let uu____7106 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____7106 in
        uu____7103.FStar_Syntax_Syntax.n in
      match uu____7102 with
      | FStar_Syntax_Syntax.Tm_abs (bs, t2, what) ->
          let uu____7152 = aux t2 what in
          (match uu____7152 with
           | (bs', t3, what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____7224 -> ([], t1, abs_body_lcomp) in
    let uu____7241 = aux t FStar_Pervasives_Native.None in
    match uu____7241 with
    | (bs, t1, abs_body_lcomp) ->
        let uu____7289 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____7289 with
         | (bs1, t2, opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp in
             (bs1, t2, abs_body_lcomp1))
let (remove_inacc : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let no_acc uu____7322 =
      match uu____7322 with
      | (b, aq) ->
          let aq1 =
            match aq with
            | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
                (true)) ->
                FStar_Pervasives_Native.Some
                  (FStar_Syntax_Syntax.Implicit false)
            | uu____7334 -> aq in
          (b, aq1) in
    let uu____7339 = arrow_formals_comp_ln t in
    match uu____7339 with
    | (bs, c) ->
        (match bs with
         | [] -> t
         | uu____7376 ->
             let uu____7385 =
               let uu____7386 =
                 let uu____7401 = FStar_List.map no_acc bs in (uu____7401, c) in
               FStar_Syntax_Syntax.Tm_arrow uu____7386 in
             FStar_Syntax_Syntax.mk uu____7385 t.FStar_Syntax_Syntax.pos)
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
                    | (FStar_Pervasives_Native.None, uu____7570) -> def
                    | (uu____7581, []) -> def
                    | (FStar_Pervasives_Native.Some fvs, uu____7593) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun uu____7609 ->
                                  FStar_Syntax_Syntax.U_name uu____7609)) in
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
            let uu____7690 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____7690 with | (uvs1, c1) -> (uvs1, [], c1))
        | uu____7725 ->
            let t' = arrow binders c in
            let uu____7737 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____7737 with
             | (uvs1, t'1) ->
                 let uu____7758 =
                   let uu____7759 = FStar_Syntax_Subst.compress t'1 in
                   uu____7759.FStar_Syntax_Syntax.n in
                 (match uu____7758 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1, c1) ->
                      (uvs1, binders1, c1)
                  | uu____7808 -> failwith "Impossible"))
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        let uu____7829 =
          FStar_Ident.string_of_lid
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        FStar_Parser_Const.is_tuple_constructor_string uu____7829
    | uu____7830 -> false
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____7837 -> false
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
      let uu____7885 =
        let uu____7886 = pre_typ t in uu____7886.FStar_Syntax_Syntax.n in
      match uu____7885 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____7890 -> false
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t ->
    fun lid ->
      let uu____7901 =
        let uu____7902 = pre_typ t in uu____7902.FStar_Syntax_Syntax.n in
      match uu____7901 with
      | FStar_Syntax_Syntax.Tm_fvar uu____7905 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1, uu____7907) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1, uu____7933) ->
          is_constructed_typ t1 lid
      | uu____7938 -> false
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____7949 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____7950 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____7951 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2, uu____7953) -> get_tycon t2
    | uu____7978 -> FStar_Pervasives_Native.None
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____7984 =
      let uu____7985 = un_uinst t in uu____7985.FStar_Syntax_Syntax.n in
    match uu____7984 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____7989 -> false
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md ->
    let path = FStar_Ident.path_of_lid md in
    if (FStar_List.length path) > (Prims.of_int (2))
    then
      let uu____7996 =
        let uu____7999 = FStar_List.splitAt (Prims.of_int (2)) path in
        FStar_Pervasives_Native.fst uu____7999 in
      match uu____7996 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____8012 -> false
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
  fun uu____8024 ->
    let u =
      let uu____8030 =
        FStar_Syntax_Unionfind.univ_fresh FStar_Range.dummyRange in
      FStar_All.pipe_left
        (fun uu____8051 -> FStar_Syntax_Syntax.U_unif uu____8051) uu____8030 in
    let uu____8052 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Range.dummyRange in
    (uu____8052, u)
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a ->
    fun a' ->
      let uu____8063 = eq_tm a a' in
      match uu____8063 with | Equal -> true | uu____8064 -> false
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____8067 =
    let uu____8068 =
      let uu____8069 =
        FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
          FStar_Range.dummyRange in
      FStar_Syntax_Syntax.lid_as_fv uu____8069
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Syntax.Tm_fvar uu____8068 in
  FStar_Syntax_Syntax.mk uu____8067 FStar_Range.dummyRange
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
          let uu____8139 =
            let uu____8142 =
              let uu____8143 =
                let uu____8160 =
                  let uu____8171 = FStar_Syntax_Syntax.as_arg phi11 in
                  let uu____8180 =
                    let uu____8191 = FStar_Syntax_Syntax.as_arg phi2 in
                    [uu____8191] in
                  uu____8171 :: uu____8180 in
                (tand, uu____8160) in
              FStar_Syntax_Syntax.Tm_app uu____8143 in
            let uu____8236 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            FStar_Syntax_Syntax.mk uu____8142 uu____8236 in
          FStar_Pervasives_Native.Some uu____8139
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t ->
    fun phi1 ->
      fun phi2 ->
        let uu____8268 =
          let uu____8269 =
            let uu____8286 =
              let uu____8297 = FStar_Syntax_Syntax.as_arg phi1 in
              let uu____8306 =
                let uu____8317 = FStar_Syntax_Syntax.as_arg phi2 in
                [uu____8317] in
              uu____8297 :: uu____8306 in
            (op_t, uu____8286) in
          FStar_Syntax_Syntax.Tm_app uu____8269 in
        let uu____8362 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Syntax.mk uu____8268 uu____8362
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi ->
    let uu____8374 =
      let uu____8375 =
        let uu____8392 =
          let uu____8403 = FStar_Syntax_Syntax.as_arg phi in [uu____8403] in
        (t_not, uu____8392) in
      FStar_Syntax_Syntax.Tm_app uu____8375 in
    FStar_Syntax_Syntax.mk uu____8374 phi.FStar_Syntax_Syntax.pos
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
    let uu____8593 =
      let uu____8594 =
        let uu____8611 =
          let uu____8622 = FStar_Syntax_Syntax.as_arg e in [uu____8622] in
        (b2t_v, uu____8611) in
      FStar_Syntax_Syntax.Tm_app uu____8594 in
    FStar_Syntax_Syntax.mk uu____8593 e.FStar_Syntax_Syntax.pos
let (unb2t :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu____8668 = head_and_args e in
    match uu____8668 with
    | (hd, args) ->
        let uu____8713 =
          let uu____8728 =
            let uu____8729 = FStar_Syntax_Subst.compress hd in
            uu____8729.FStar_Syntax_Syntax.n in
          (uu____8728, args) in
        (match uu____8713 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, (e1, uu____8746)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.b2t_lid ->
             FStar_Pervasives_Native.Some e1
         | uu____8781 -> FStar_Pervasives_Native.None)
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____8801 =
      let uu____8802 = unmeta t in uu____8802.FStar_Syntax_Syntax.n in
    match uu____8801 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____8806 -> false
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let uu____8827 = is_t_true t1 in
      if uu____8827
      then t2
      else
        (let uu____8831 = is_t_true t2 in
         if uu____8831 then t1 else mk_conj t1 t2)
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1 ->
    fun t2 ->
      let uu____8855 = is_t_true t1 in
      if uu____8855
      then t_true
      else
        (let uu____8859 = is_t_true t2 in
         if uu____8859 then t_true else mk_disj t1 t2)
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1 ->
    fun e2 ->
      let uu____8883 =
        let uu____8884 =
          let uu____8901 =
            let uu____8912 = FStar_Syntax_Syntax.as_arg e1 in
            let uu____8921 =
              let uu____8932 = FStar_Syntax_Syntax.as_arg e2 in [uu____8932] in
            uu____8912 :: uu____8921 in
          (teq, uu____8901) in
        FStar_Syntax_Syntax.Tm_app uu____8884 in
      let uu____8977 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk uu____8883 uu____8977
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
          let uu____8999 =
            let uu____9000 =
              let uu____9017 =
                let uu____9028 = FStar_Syntax_Syntax.iarg t in
                let uu____9037 =
                  let uu____9048 = FStar_Syntax_Syntax.as_arg e1 in
                  let uu____9057 =
                    let uu____9068 = FStar_Syntax_Syntax.as_arg e2 in
                    [uu____9068] in
                  uu____9048 :: uu____9057 in
                uu____9028 :: uu____9037 in
              (eq_inst, uu____9017) in
            FStar_Syntax_Syntax.Tm_app uu____9000 in
          let uu____9121 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          FStar_Syntax_Syntax.mk uu____8999 uu____9121
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
        let uu____9145 =
          let uu____9146 =
            let uu____9163 =
              let uu____9174 = FStar_Syntax_Syntax.iarg t in
              let uu____9183 =
                let uu____9194 = FStar_Syntax_Syntax.as_arg x in
                let uu____9203 =
                  let uu____9214 = FStar_Syntax_Syntax.as_arg t' in
                  [uu____9214] in
                uu____9194 :: uu____9203 in
              uu____9174 :: uu____9183 in
            (t_has_type1, uu____9163) in
          FStar_Syntax_Syntax.Tm_app uu____9146 in
        FStar_Syntax_Syntax.mk uu____9145 FStar_Range.dummyRange
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
        let uu____9290 =
          let uu____9291 =
            let uu____9308 =
              let uu____9319 = FStar_Syntax_Syntax.iarg t in
              let uu____9328 =
                let uu____9339 = FStar_Syntax_Syntax.as_arg e in [uu____9339] in
              uu____9319 :: uu____9328 in
            (t_with_type1, uu____9308) in
          FStar_Syntax_Syntax.Tm_app uu____9291 in
        FStar_Syntax_Syntax.mk uu____9290 FStar_Range.dummyRange
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____9384 =
    let uu____9385 =
      let uu____9392 =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
          FStar_Syntax_Syntax.delta_constant
          (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
      (uu____9392, [FStar_Syntax_Syntax.U_zero]) in
    FStar_Syntax_Syntax.Tm_uinst uu____9385 in
  FStar_Syntax_Syntax.mk uu____9384 FStar_Range.dummyRange
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
        let uu____9422 =
          let uu____9423 =
            let uu____9440 =
              let uu____9451 = FStar_Syntax_Syntax.iarg t in
              let uu____9460 =
                let uu____9471 = FStar_Syntax_Syntax.as_arg e1 in
                let uu____9480 =
                  let uu____9491 = FStar_Syntax_Syntax.as_arg e2 in
                  [uu____9491] in
                uu____9471 :: uu____9480 in
              uu____9451 :: uu____9460 in
            (decidable_eq, uu____9440) in
          FStar_Syntax_Syntax.Tm_app uu____9423 in
        let uu____9544 =
          FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
            e2.FStar_Syntax_Syntax.pos in
        FStar_Syntax_Syntax.mk uu____9422 uu____9544
let (b_and : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.op_And
let (mk_and :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1 ->
    fun e2 ->
      let uu____9565 =
        let uu____9566 =
          let uu____9583 =
            let uu____9594 = FStar_Syntax_Syntax.as_arg e1 in
            let uu____9603 =
              let uu____9614 = FStar_Syntax_Syntax.as_arg e2 in [uu____9614] in
            uu____9594 :: uu____9603 in
          (b_and, uu____9583) in
        FStar_Syntax_Syntax.Tm_app uu____9566 in
      let uu____9659 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos in
      FStar_Syntax_Syntax.mk uu____9565 uu____9659
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
        let uu____9763 =
          let uu____9764 =
            let uu____9781 =
              let uu____9792 =
                FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
              let uu____9801 =
                let uu____9812 =
                  let uu____9821 =
                    let uu____9822 =
                      let uu____9823 = FStar_Syntax_Syntax.mk_binder x in
                      [uu____9823] in
                    abs uu____9822 body
                      (FStar_Pervasives_Native.Some (residual_tot ktype0)) in
                  FStar_Syntax_Syntax.as_arg uu____9821 in
                [uu____9812] in
              uu____9792 :: uu____9801 in
            (fa, uu____9781) in
          FStar_Syntax_Syntax.Tm_app uu____9764 in
        FStar_Syntax_Syntax.mk uu____9763 FStar_Range.dummyRange
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
             let uu____9947 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____9947
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
let (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____9960 -> true
    | uu____9961 -> false
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
          let uu____10006 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos in
          (uu____10006, FStar_Pervasives_Native.None, t1) in
        let else_branch =
          let uu____10034 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos in
          (uu____10034, FStar_Pervasives_Native.None, t2) in
        let uu____10047 =
          let uu____10048 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____10048 in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          uu____10047
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
      let uu____10122 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu____10125 =
        let uu____10136 = FStar_Syntax_Syntax.as_arg p in [uu____10136] in
      mk_app uu____10122 uu____10125
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
      let uu____10174 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u] in
      let uu____10177 =
        let uu____10188 = FStar_Syntax_Syntax.as_arg p in [uu____10188] in
      mk_app uu____10174 uu____10177
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____10222 = head_and_args t in
    match uu____10222 with
    | (head, args) ->
        let head1 = unascribe head in
        let head2 = un_uinst head1 in
        let uu____10271 =
          let uu____10286 =
            let uu____10287 = FStar_Syntax_Subst.compress head2 in
            uu____10287.FStar_Syntax_Syntax.n in
          (uu____10286, args) in
        (match uu____10271 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, (p, uu____10306)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b, p), []) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____10372 =
                    let uu____10377 =
                      let uu____10378 = FStar_Syntax_Syntax.mk_binder b in
                      [uu____10378] in
                    FStar_Syntax_Subst.open_term uu____10377 p in
                  (match uu____10372 with
                   | (bs, p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____10435 -> failwith "impossible" in
                       let uu____10442 =
                         let uu____10443 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____10443 in
                       if uu____10442
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____10457 -> FStar_Pervasives_Native.None)
         | uu____10460 -> FStar_Pervasives_Native.None)
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____10490 = head_and_args t in
    match uu____10490 with
    | (head, args) ->
        let uu____10541 =
          let uu____10556 =
            let uu____10557 = FStar_Syntax_Subst.compress head in
            uu____10557.FStar_Syntax_Syntax.n in
          (uu____10556, args) in
        (match uu____10541 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10579;
               FStar_Syntax_Syntax.vars = uu____10580;_},
             u::[]),
            (t1, uu____10583)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10630 -> FStar_Pervasives_Native.None)
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____10664 = head_and_args t in
    match uu____10664 with
    | (head, args) ->
        let uu____10715 =
          let uu____10730 =
            let uu____10731 = FStar_Syntax_Subst.compress head in
            uu____10731.FStar_Syntax_Syntax.n in
          (uu____10730, args) in
        (match uu____10715 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____10753;
               FStar_Syntax_Syntax.vars = uu____10754;_},
             u::[]),
            (t1, uu____10757)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____10804 -> FStar_Pervasives_Native.None)
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____10830 = let uu____10847 = unmeta t in head_and_args uu____10847 in
    match uu____10830 with
    | (head, uu____10849) ->
        let uu____10874 =
          let uu____10875 = un_uinst head in
          uu____10875.FStar_Syntax_Syntax.n in
        (match uu____10874 with
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
         | uu____10879 -> false)
let (arrow_one_ln :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____10897 =
      let uu____10898 = FStar_Syntax_Subst.compress t in
      uu____10898.FStar_Syntax_Syntax.n in
    match uu____10897 with
    | FStar_Syntax_Syntax.Tm_arrow ([], c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[], c) ->
        FStar_Pervasives_Native.Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs, c) ->
        let uu____11003 =
          let uu____11008 =
            let uu____11009 = arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____11009 in
          (b, uu____11008) in
        FStar_Pervasives_Native.Some uu____11003
    | uu____11014 -> FStar_Pervasives_Native.None
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu____11036 = arrow_one_ln t in
    FStar_Util.bind_opt uu____11036
      (fun uu____11064 ->
         match uu____11064 with
         | (b, c) ->
             let uu____11083 = FStar_Syntax_Subst.open_comp [b] c in
             (match uu____11083 with
              | (bs, c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____11146 ->
                        failwith
                          "impossible: open_comp returned different amount of binders" in
                  FStar_Pervasives_Native.Some (b1, c1)))
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu____11179 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____11179
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee ->
    match projectee with | QAll _0 -> true | uu____11227 -> false
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QAll _0 -> _0
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee ->
    match projectee with | QEx _0 -> true | uu____11264 -> false
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QEx _0 -> _0
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee ->
    match projectee with | BaseConn _0 -> true | uu____11299 -> false
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
          (t, FStar_Syntax_Syntax.Meta_monadic uu____11649) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t, FStar_Syntax_Syntax.Meta_monadic_lift uu____11661) ->
          unmeta_monadic t
      | uu____11674 -> f2 in
    let lookup_arity_lid table target_lid args =
      let arg_len = FStar_List.length args in
      let aux uu____11743 =
        match uu____11743 with
        | (arity, lids) ->
            if arg_len = arity
            then
              FStar_Util.find_map lids
                (fun uu____11780 ->
                   match uu____11780 with
                   | (lid, out_lid) ->
                       let uu____11789 =
                         FStar_Ident.lid_equals target_lid lid in
                       if uu____11789
                       then
                         FStar_Pervasives_Native.Some
                           (BaseConn (out_lid, args))
                       else FStar_Pervasives_Native.None)
            else FStar_Pervasives_Native.None in
      FStar_Util.find_map table aux in
    let destruct_base_conn t =
      let uu____11812 = head_and_args t in
      match uu____11812 with
      | (hd, args) ->
          let uu____11857 =
            let uu____11858 = un_uinst hd in
            uu____11858.FStar_Syntax_Syntax.n in
          (match uu____11857 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               lookup_arity_lid destruct_base_table
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
           | uu____11864 -> FStar_Pervasives_Native.None) in
    let destruct_sq_base_conn t =
      let uu____11873 = un_squash t in
      FStar_Util.bind_opt uu____11873
        (fun t1 ->
           let uu____11889 = head_and_args' t1 in
           match uu____11889 with
           | (hd, args) ->
               let uu____11928 =
                 let uu____11929 = un_uinst hd in
                 uu____11929.FStar_Syntax_Syntax.n in
               (match uu____11928 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    lookup_arity_lid destruct_sq_base_table
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      args
                | uu____11935 -> FStar_Pervasives_Native.None)) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2, FStar_Syntax_Syntax.Meta_pattern (uu____11976, pats)) ->
          let uu____12014 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____12014)
      | uu____12027 -> ([], t1) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____12088 = head_and_args t1 in
        match uu____12088 with
        | (t2, args) ->
            let uu____12143 = un_uinst t2 in
            let uu____12144 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____12185 ->
                      match uu____12185 with
                      | (t3, imp) ->
                          let uu____12204 = unascribe t3 in
                          (uu____12204, imp))) in
            (uu____12143, uu____12144) in
      let rec aux qopt out t1 =
        let uu____12253 = let uu____12276 = flat t1 in (qopt, uu____12276) in
        match uu____12253 with
        | (FStar_Pervasives_Native.Some fa,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu____12315;
              FStar_Syntax_Syntax.vars = uu____12316;_},
            ({
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                 (b::[], t2, uu____12319);
               FStar_Syntax_Syntax.pos = uu____12320;
               FStar_Syntax_Syntax.vars = uu____12321;_},
             uu____12322)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some fa,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu____12421;
              FStar_Syntax_Syntax.vars = uu____12422;_},
            uu____12423::({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_abs
                              (b::[], t2, uu____12426);
                            FStar_Syntax_Syntax.pos = uu____12427;
                            FStar_Syntax_Syntax.vars = uu____12428;_},
                          uu____12429)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu____12543;
              FStar_Syntax_Syntax.vars = uu____12544;_},
            ({
               FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                 (b::[], t2, uu____12547);
               FStar_Syntax_Syntax.pos = uu____12548;
               FStar_Syntax_Syntax.vars = uu____12549;_},
             uu____12550)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12641 =
              let uu____12644 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              FStar_Pervasives_Native.Some uu____12644 in
            aux uu____12641 (b :: out) t2
        | (FStar_Pervasives_Native.None,
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
              FStar_Syntax_Syntax.pos = uu____12652;
              FStar_Syntax_Syntax.vars = uu____12653;_},
            uu____12654::({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_abs
                              (b::[], t2, uu____12657);
                            FStar_Syntax_Syntax.pos = uu____12658;
                            FStar_Syntax_Syntax.vars = uu____12659;_},
                          uu____12660)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____12767 =
              let uu____12770 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              FStar_Pervasives_Native.Some uu____12770 in
            aux uu____12767 (b :: out) t2
        | (FStar_Pervasives_Native.Some b, uu____12778) ->
            let bs = FStar_List.rev out in
            let uu____12828 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____12828 with
             | (bs1, t2) ->
                 let uu____12837 = patterns t2 in
                 (match uu____12837 with
                  | (pats, body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____12885 -> FStar_Pervasives_Native.None in
      aux FStar_Pervasives_Native.None [] t in
    let rec destruct_sq_forall t =
      let uu____12938 = un_squash t in
      FStar_Util.bind_opt uu____12938
        (fun t1 ->
           let uu____12953 = arrow_one t1 in
           match uu____12953 with
           | FStar_Pervasives_Native.Some (b, c) ->
               let uu____12968 =
                 let uu____12969 = is_tot_or_gtot_comp c in
                 Prims.op_Negation uu____12969 in
               if uu____12968
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____12976 = comp_to_comp_typ_nouniv c in
                    uu____12976.FStar_Syntax_Syntax.result_typ in
                  let uu____12977 =
                    is_free_in (FStar_Pervasives_Native.fst b) q in
                  if uu____12977
                  then
                    let uu____12982 = patterns q in
                    match uu____12982 with
                    | (pats, q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____13044 =
                       let uu____13045 =
                         let uu____13050 =
                           let uu____13051 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort in
                           let uu____13062 =
                             let uu____13073 = FStar_Syntax_Syntax.as_arg q in
                             [uu____13073] in
                           uu____13051 :: uu____13062 in
                         (FStar_Parser_Const.imp_lid, uu____13050) in
                       BaseConn uu____13045 in
                     FStar_Pervasives_Native.Some uu____13044))
           | uu____13106 -> FStar_Pervasives_Native.None)
    and destruct_sq_exists t =
      let uu____13114 = un_squash t in
      FStar_Util.bind_opt uu____13114
        (fun t1 ->
           let uu____13145 = head_and_args' t1 in
           match uu____13145 with
           | (hd, args) ->
               let uu____13184 =
                 let uu____13199 =
                   let uu____13200 = un_uinst hd in
                   uu____13200.FStar_Syntax_Syntax.n in
                 (uu____13199, args) in
               (match uu____13184 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (a1, uu____13217)::(a2, uu____13219)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____13270 =
                      let uu____13271 = FStar_Syntax_Subst.compress a2 in
                      uu____13271.FStar_Syntax_Syntax.n in
                    (match uu____13270 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[], q, uu____13278) ->
                         let uu____13313 = FStar_Syntax_Subst.open_term [b] q in
                         (match uu____13313 with
                          | (bs, q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____13366 -> failwith "impossible" in
                              let uu____13373 = patterns q1 in
                              (match uu____13373 with
                               | (pats, q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____13434 -> FStar_Pervasives_Native.None)
                | uu____13435 -> FStar_Pervasives_Native.None))
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) ->
          let uu____13458 = destruct_sq_forall phi in
          (match uu____13458 with
           | FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) ->
               FStar_All.pipe_left
                 (fun uu____13468 -> FStar_Pervasives_Native.Some uu____13468)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13475 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) ->
          let uu____13481 = destruct_sq_exists phi in
          (match uu____13481 with
           | FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) ->
               FStar_All.pipe_left
                 (fun uu____13491 -> FStar_Pervasives_Native.Some uu____13491)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____13498 -> f1)
      | uu____13501 -> f1 in
    let phi = unmeta_monadic f in
    let uu____13505 = destruct_base_conn phi in
    FStar_Util.catch_opt uu____13505
      (fun uu____13510 ->
         let uu____13511 = destruct_q_conn phi in
         FStar_Util.catch_opt uu____13511
           (fun uu____13516 ->
              let uu____13517 = destruct_sq_base_conn phi in
              FStar_Util.catch_opt uu____13517
                (fun uu____13522 ->
                   let uu____13523 = destruct_sq_forall phi in
                   FStar_Util.catch_opt uu____13523
                     (fun uu____13528 ->
                        let uu____13529 = destruct_sq_exists phi in
                        FStar_Util.catch_opt uu____13529
                          (fun uu____13533 -> FStar_Pervasives_Native.None)))))
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid ->
    fun a ->
      fun pos ->
        let lb =
          let uu____13550 =
            let uu____13555 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None in
            FStar_Util.Inr uu____13555 in
          let uu____13556 =
            let uu____13557 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
            arrow a.FStar_Syntax_Syntax.action_params uu____13557 in
          let uu____13560 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____13550 a.FStar_Syntax_Syntax.action_univs uu____13556
            FStar_Parser_Const.effect_Tot_lid uu____13560 [] pos in
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
    let uu____13583 =
      let uu____13584 =
        let uu____13601 =
          let uu____13612 = FStar_Syntax_Syntax.as_arg t in [uu____13612] in
        (reify_, uu____13601) in
      FStar_Syntax_Syntax.Tm_app uu____13584 in
    FStar_Syntax_Syntax.mk uu____13583 t.FStar_Syntax_Syntax.pos
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t ->
    let reflect_ =
      let uu____13663 =
        let uu____13664 =
          let uu____13665 = FStar_Ident.lid_of_str "Bogus.Effect" in
          FStar_Const.Const_reflect uu____13665 in
        FStar_Syntax_Syntax.Tm_constant uu____13664 in
      FStar_Syntax_Syntax.mk uu____13663 t.FStar_Syntax_Syntax.pos in
    let uu____13666 =
      let uu____13667 =
        let uu____13684 =
          let uu____13695 = FStar_Syntax_Syntax.as_arg t in [uu____13695] in
        (reflect_, uu____13684) in
      FStar_Syntax_Syntax.Tm_app uu____13667 in
    FStar_Syntax_Syntax.mk uu____13666 t.FStar_Syntax_Syntax.pos
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____13738 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____13754 = unfold_lazy i in delta_qualifier uu____13754
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____13756 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____13757 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____13758 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____13781 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____13794 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____13795 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____13802 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____13803 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2, uu____13819) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____13824;
           FStar_Syntax_Syntax.index = uu____13825;
           FStar_Syntax_Syntax.sort = t2;_},
         uu____13827)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2, uu____13835) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2, uu____13841, uu____13842) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2, uu____13884) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____13909, t2, uu____13911) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____13936, t2) -> delta_qualifier t2
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
    let uu____13967 = delta_qualifier t in incr_delta_depth uu____13967
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____13973 =
      let uu____13974 = FStar_Syntax_Subst.compress t in
      uu____13974.FStar_Syntax_Syntax.n in
    match uu____13973 with
    | FStar_Syntax_Syntax.Tm_unknown -> true
    | uu____13977 -> false
let rec apply_last :
  'uuuuuu13984 .
    ('uuuuuu13984 -> 'uuuuuu13984) ->
      'uuuuuu13984 Prims.list -> 'uuuuuu13984 Prims.list
  =
  fun f ->
    fun l ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____14009 = f a in [uu____14009]
      | x::xs -> let uu____14014 = apply_last f xs in x :: uu____14014
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
          let uu____14060 =
            let uu____14061 =
              FStar_Syntax_Syntax.lid_as_fv l1
                FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor) in
            FStar_Syntax_Syntax.Tm_fvar uu____14061 in
          FStar_Syntax_Syntax.mk uu____14060 rng in
        let cons args pos =
          let uu____14073 =
            let uu____14074 = ctor FStar_Parser_Const.cons_lid in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14074
              [FStar_Syntax_Syntax.U_zero] in
          FStar_Syntax_Syntax.mk_Tm_app uu____14073 args pos in
        let nil args pos =
          let uu____14086 =
            let uu____14087 = ctor FStar_Parser_Const.nil_lid in
            FStar_Syntax_Syntax.mk_Tm_uinst uu____14087
              [FStar_Syntax_Syntax.U_zero] in
          FStar_Syntax_Syntax.mk_Tm_app uu____14086 args pos in
        let uu____14088 =
          let uu____14089 =
            let uu____14090 = FStar_Syntax_Syntax.iarg typ in [uu____14090] in
          nil uu____14089 rng in
        FStar_List.fold_right
          (fun t ->
             fun a ->
               let uu____14124 =
                 let uu____14125 = FStar_Syntax_Syntax.iarg typ in
                 let uu____14134 =
                   let uu____14145 = FStar_Syntax_Syntax.as_arg t in
                   let uu____14154 =
                     let uu____14165 = FStar_Syntax_Syntax.as_arg a in
                     [uu____14165] in
                   uu____14145 :: uu____14154 in
                 uu____14125 :: uu____14134 in
               cons uu____14124 t.FStar_Syntax_Syntax.pos) l uu____14088
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
        | uu____14269 -> false
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
          | uu____14376 -> false
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
        | uu____14531 -> false
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg ->
    fun cond ->
      if cond
      then true
      else
        ((let uu____14554 = FStar_ST.op_Bang debug_term_eq in
          if uu____14554
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
        let t11 = let uu____14703 = unmeta_safe t1 in canon_app uu____14703 in
        let t21 = let uu____14707 = unmeta_safe t2 in canon_app uu____14707 in
        let uu____14710 =
          let uu____14715 =
            let uu____14716 =
              let uu____14719 = un_uinst t11 in
              FStar_Syntax_Subst.compress uu____14719 in
            uu____14716.FStar_Syntax_Syntax.n in
          let uu____14720 =
            let uu____14721 =
              let uu____14724 = un_uinst t21 in
              FStar_Syntax_Subst.compress uu____14724 in
            uu____14721.FStar_Syntax_Syntax.n in
          (uu____14715, uu____14720) in
        match uu____14710 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____14725, uu____14726) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____14733, FStar_Syntax_Syntax.Tm_uinst uu____14734) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____14741, uu____14742) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____14757, FStar_Syntax_Syntax.Tm_delayed uu____14758) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____14773, uu____14774) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____14801, FStar_Syntax_Syntax.Tm_ascribed uu____14802) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x, FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x, FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x, FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____14835 = FStar_Syntax_Syntax.fv_eq x y in
            check "fvar" uu____14835
        | (FStar_Syntax_Syntax.Tm_constant c1,
           FStar_Syntax_Syntax.Tm_constant c2) ->
            let uu____14838 = FStar_Const.eq_const c1 c2 in
            check "const" uu____14838
        | (FStar_Syntax_Syntax.Tm_type uu____14839,
           FStar_Syntax_Syntax.Tm_type uu____14840) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1, t12, k1),
           FStar_Syntax_Syntax.Tm_abs (b2, t22, k2)) ->
            (let uu____14897 = eqlist (binder_eq_dbg dbg) b1 b2 in
             check "abs binders" uu____14897) &&
              (let uu____14905 = term_eq_dbg dbg t12 t22 in
               check "abs bodies" uu____14905)
        | (FStar_Syntax_Syntax.Tm_arrow (b1, c1),
           FStar_Syntax_Syntax.Tm_arrow (b2, c2)) ->
            (let uu____14952 = eqlist (binder_eq_dbg dbg) b1 b2 in
             check "arrow binders" uu____14952) &&
              (let uu____14960 = comp_eq_dbg dbg c1 c2 in
               check "arrow comp" uu____14960)
        | (FStar_Syntax_Syntax.Tm_refine (b1, t12),
           FStar_Syntax_Syntax.Tm_refine (b2, t22)) ->
            (let uu____14975 =
               term_eq_dbg dbg b1.FStar_Syntax_Syntax.sort
                 b2.FStar_Syntax_Syntax.sort in
             check "refine bv sort" uu____14975) &&
              (let uu____14977 = term_eq_dbg dbg t12 t22 in
               check "refine formula" uu____14977)
        | (FStar_Syntax_Syntax.Tm_app (f1, a1), FStar_Syntax_Syntax.Tm_app
           (f2, a2)) ->
            (let uu____15032 = term_eq_dbg dbg f1 f2 in
             check "app head" uu____15032) &&
              (let uu____15034 = eqlist (arg_eq_dbg dbg) a1 a2 in
               check "app args" uu____15034)
        | (FStar_Syntax_Syntax.Tm_match (t12, bs1),
           FStar_Syntax_Syntax.Tm_match (t22, bs2)) ->
            (let uu____15121 = term_eq_dbg dbg t12 t22 in
             check "match head" uu____15121) &&
              (let uu____15123 = eqlist (branch_eq_dbg dbg) bs1 bs2 in
               check "match branches" uu____15123)
        | (FStar_Syntax_Syntax.Tm_lazy uu____15138, uu____15139) ->
            let uu____15140 =
              let uu____15141 = unlazy t11 in term_eq_dbg dbg uu____15141 t21 in
            check "lazy_l" uu____15140
        | (uu____15142, FStar_Syntax_Syntax.Tm_lazy uu____15143) ->
            let uu____15144 =
              let uu____15145 = unlazy t21 in term_eq_dbg dbg t11 uu____15145 in
            check "lazy_r" uu____15144
        | (FStar_Syntax_Syntax.Tm_let ((b1, lbs1), t12),
           FStar_Syntax_Syntax.Tm_let ((b2, lbs2), t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____15181 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2 in
                check "let lbs" uu____15181))
              &&
              (let uu____15183 = term_eq_dbg dbg t12 t22 in
               check "let body" uu____15183)
        | (FStar_Syntax_Syntax.Tm_uvar (u1, uu____15185),
           FStar_Syntax_Syntax.Tm_uvar (u2, uu____15187)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted (qt1, qi1),
           FStar_Syntax_Syntax.Tm_quoted (qt2, qi2)) ->
            (let uu____15246 =
               let uu____15247 = eq_quoteinfo qi1 qi2 in uu____15247 = Equal in
             check "tm_quoted qi" uu____15246) &&
              (let uu____15249 = term_eq_dbg dbg qt1 qt2 in
               check "tm_quoted payload" uu____15249)
        | (FStar_Syntax_Syntax.Tm_meta (t12, m1), FStar_Syntax_Syntax.Tm_meta
           (t22, m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic (n1, ty1),
                FStar_Syntax_Syntax.Meta_monadic (n2, ty2)) ->
                 (let uu____15276 = FStar_Ident.lid_equals n1 n2 in
                  check "meta_monadic lid" uu____15276) &&
                   (let uu____15278 = term_eq_dbg dbg ty1 ty2 in
                    check "meta_monadic type" uu____15278)
             | (FStar_Syntax_Syntax.Meta_monadic_lift (s1, t13, ty1),
                FStar_Syntax_Syntax.Meta_monadic_lift (s2, t23, ty2)) ->
                 ((let uu____15295 = FStar_Ident.lid_equals s1 s2 in
                   check "meta_monadic_lift src" uu____15295) &&
                    (let uu____15297 = FStar_Ident.lid_equals t13 t23 in
                     check "meta_monadic_lift tgt" uu____15297))
                   &&
                   (let uu____15299 = term_eq_dbg dbg ty1 ty2 in
                    check "meta_monadic_lift type" uu____15299)
             | uu____15300 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown, uu____15305) -> fail "unk"
        | (uu____15306, FStar_Syntax_Syntax.Tm_unknown) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____15307, uu____15308) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____15309, uu____15310) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____15311, uu____15312) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____15313, uu____15314) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____15315, uu____15316) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____15317, uu____15318) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____15337, uu____15338) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____15353, uu____15354) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____15361, uu____15362) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____15379, uu____15380) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____15403, uu____15404) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____15417, uu____15418) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____15431, uu____15432) ->
            fail "bottom"
        | (uu____15439, FStar_Syntax_Syntax.Tm_bvar uu____15440) ->
            fail "bottom"
        | (uu____15441, FStar_Syntax_Syntax.Tm_name uu____15442) ->
            fail "bottom"
        | (uu____15443, FStar_Syntax_Syntax.Tm_fvar uu____15444) ->
            fail "bottom"
        | (uu____15445, FStar_Syntax_Syntax.Tm_constant uu____15446) ->
            fail "bottom"
        | (uu____15447, FStar_Syntax_Syntax.Tm_type uu____15448) ->
            fail "bottom"
        | (uu____15449, FStar_Syntax_Syntax.Tm_abs uu____15450) ->
            fail "bottom"
        | (uu____15469, FStar_Syntax_Syntax.Tm_arrow uu____15470) ->
            fail "bottom"
        | (uu____15485, FStar_Syntax_Syntax.Tm_refine uu____15486) ->
            fail "bottom"
        | (uu____15493, FStar_Syntax_Syntax.Tm_app uu____15494) ->
            fail "bottom"
        | (uu____15511, FStar_Syntax_Syntax.Tm_match uu____15512) ->
            fail "bottom"
        | (uu____15535, FStar_Syntax_Syntax.Tm_let uu____15536) ->
            fail "bottom"
        | (uu____15549, FStar_Syntax_Syntax.Tm_uvar uu____15550) ->
            fail "bottom"
        | (uu____15563, FStar_Syntax_Syntax.Tm_meta uu____15564) ->
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
               let uu____15597 = term_eq_dbg dbg t1 t2 in
               check "arg tm" uu____15597)
          (fun q1 ->
             fun q2 ->
               let uu____15607 =
                 let uu____15608 = eq_aqual q1 q2 in uu____15608 = Equal in
               check "arg qual" uu____15607) a1 a2
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
               let uu____15631 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort in
               check "binder sort" uu____15631)
          (fun q1 ->
             fun q2 ->
               let uu____15641 =
                 let uu____15642 = eq_aqual q1 q2 in uu____15642 = Equal in
               check "binder qual" uu____15641) b1 b2
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
        ((let uu____15654 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name in
          check "comp eff" uu____15654) &&
           (let uu____15656 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ in
            check "comp result typ" uu____15656))
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
    fun uu____15658 ->
      fun uu____15659 ->
        match (uu____15658, uu____15659) with
        | ((p1, w1, t1), (p2, w2, t2)) ->
            ((let uu____15784 = FStar_Syntax_Syntax.eq_pat p1 p2 in
              check "branch pat" uu____15784) &&
               (let uu____15786 = term_eq_dbg dbg t1 t2 in
                check "branch body" uu____15786))
              &&
              (let uu____15788 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some x,
                    FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None) -> true
                 | uu____15827 -> false in
               check "branch when" uu____15788)
and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg ->
    fun lb1 ->
      fun lb2 ->
        ((let uu____15845 =
            eqsum (fun bv1 -> fun bv2 -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname in
          check "lb bv" uu____15845) &&
           (let uu____15851 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp in
            check "lb typ" uu____15851))
          &&
          (let uu____15853 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef in
           check "lb def" uu____15853)
let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1 ->
    fun t2 ->
      let r =
        let uu____15865 = FStar_ST.op_Bang debug_term_eq in
        term_eq_dbg uu____15865 t1 t2 in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____15884 ->
        let uu____15899 =
          let uu____15900 = FStar_Syntax_Subst.compress t in
          sizeof uu____15900 in
        Prims.int_one + uu____15899
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____15902 = sizeof bv.FStar_Syntax_Syntax.sort in
        Prims.int_one + uu____15902
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____15904 = sizeof bv.FStar_Syntax_Syntax.sort in
        Prims.int_one + uu____15904
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) ->
        let uu____15911 = sizeof t1 in (FStar_List.length us) + uu____15911
    | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____15914) ->
        let uu____15939 = sizeof t1 in
        let uu____15940 =
          FStar_List.fold_left
            (fun acc ->
               fun uu____15953 ->
                 match uu____15953 with
                 | (bv, uu____15961) ->
                     let uu____15966 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____15966) Prims.int_zero bs in
        uu____15939 + uu____15940
    | FStar_Syntax_Syntax.Tm_app (hd, args) ->
        let uu____15993 = sizeof hd in
        let uu____15994 =
          FStar_List.fold_left
            (fun acc ->
               fun uu____16007 ->
                 match uu____16007 with
                 | (arg, uu____16015) ->
                     let uu____16020 = sizeof arg in acc + uu____16020)
            Prims.int_zero args in
        uu____15993 + uu____15994
    | uu____16021 -> Prims.int_one
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid ->
    fun t ->
      let uu____16032 =
        let uu____16033 = un_uinst t in uu____16033.FStar_Syntax_Syntax.n in
      match uu____16032 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____16037 -> false
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
           let uu____16092 = head_and_args t in
           match uu____16092 with
           | (head, args) ->
               let uu____16147 =
                 let uu____16148 = FStar_Syntax_Subst.compress head in
                 uu____16148.FStar_Syntax_Syntax.n in
               (match uu____16147 with
                | FStar_Syntax_Syntax.Tm_fvar fv when
                    FStar_Syntax_Syntax.fv_eq_lid fv attr ->
                    FStar_Pervasives_Native.Some args
                | uu____16174 -> FStar_Pervasives_Native.None)) attrs
let (remove_attr :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.attribute Prims.list ->
      FStar_Syntax_Syntax.attribute Prims.list)
  =
  fun attr ->
    fun attrs ->
      FStar_List.filter
        (fun a ->
           let uu____16206 = is_fvar attr a in Prims.op_Negation uu____16206)
        attrs
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p ->
    fun r ->
      FStar_Errors.set_option_warning_callback_range
        (FStar_Pervasives_Native.Some r);
      (let set_options s =
         let uu____16224 = FStar_Options.set_options s in
         match uu____16224 with
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
           ((let uu____16231 = FStar_Options.restore_cmd_line_options false in
             FStar_All.pipe_right uu____16231 (fun uu____16232 -> ()));
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
           let uu____16239 = FStar_Options.internal_pop () in
           if uu____16239
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
    | FStar_Syntax_Syntax.Tm_delayed uu____16265 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____16283 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____16298 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____16299 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____16300 -> []
    | FStar_Syntax_Syntax.Tm_unknown -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1, us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs, t1, uu____16309) ->
        let uu____16334 = FStar_Syntax_Subst.open_term bs t1 in
        (match uu____16334 with
         | (bs1, t2) ->
             let uu____16343 =
               FStar_List.collect
                 (fun uu____16355 ->
                    match uu____16355 with
                    | (b, uu____16365) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1 in
             let uu____16370 = unbound_variables t2 in
             FStar_List.append uu____16343 uu____16370)
    | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
        let uu____16395 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____16395 with
         | (bs1, c1) ->
             let uu____16404 =
               FStar_List.collect
                 (fun uu____16416 ->
                    match uu____16416 with
                    | (b, uu____16426) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1 in
             let uu____16431 = unbound_variables_comp c1 in
             FStar_List.append uu____16404 uu____16431)
    | FStar_Syntax_Syntax.Tm_refine (b, t1) ->
        let uu____16440 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1 in
        (match uu____16440 with
         | (bs, t2) ->
             let uu____16463 =
               FStar_List.collect
                 (fun uu____16475 ->
                    match uu____16475 with
                    | (b1, uu____16485) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs in
             let uu____16490 = unbound_variables t2 in
             FStar_List.append uu____16463 uu____16490)
    | FStar_Syntax_Syntax.Tm_app (t1, args) ->
        let uu____16519 =
          FStar_List.collect
            (fun uu____16533 ->
               match uu____16533 with
               | (x, uu____16545) -> unbound_variables x) args in
        let uu____16554 = unbound_variables t1 in
        FStar_List.append uu____16519 uu____16554
    | FStar_Syntax_Syntax.Tm_match (t1, pats) ->
        let uu____16595 = unbound_variables t1 in
        let uu____16598 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br ->
                  let uu____16613 = FStar_Syntax_Subst.open_branch br in
                  match uu____16613 with
                  | (p, wopt, t2) ->
                      let uu____16635 = unbound_variables t2 in
                      let uu____16638 =
                        match wopt with
                        | FStar_Pervasives_Native.None -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3 in
                      FStar_List.append uu____16635 uu____16638)) in
        FStar_List.append uu____16595 uu____16598
    | FStar_Syntax_Syntax.Tm_ascribed (t1, asc, uu____16652) ->
        let uu____16693 = unbound_variables t1 in
        let uu____16696 =
          let uu____16699 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2 in
          let uu____16730 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac in
          FStar_List.append uu____16699 uu____16730 in
        FStar_List.append uu____16693 uu____16696
    | FStar_Syntax_Syntax.Tm_let ((false, lb::[]), t1) ->
        let uu____16768 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp in
        let uu____16771 =
          let uu____16774 = unbound_variables lb.FStar_Syntax_Syntax.lbdef in
          let uu____16777 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____16782 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____16784 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1 in
                (match uu____16784 with
                 | (uu____16805, t2) -> unbound_variables t2) in
          FStar_List.append uu____16774 uu____16777 in
        FStar_List.append uu____16768 uu____16771
    | FStar_Syntax_Syntax.Tm_let ((uu____16807, lbs), t1) ->
        let uu____16824 = FStar_Syntax_Subst.open_let_rec lbs t1 in
        (match uu____16824 with
         | (lbs1, t2) ->
             let uu____16839 = unbound_variables t2 in
             let uu____16842 =
               FStar_List.collect
                 (fun lb ->
                    let uu____16849 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp in
                    let uu____16852 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef in
                    FStar_List.append uu____16849 uu____16852) lbs1 in
             FStar_List.append uu____16839 uu____16842)
    | FStar_Syntax_Syntax.Tm_quoted (tm1, qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static -> []
         | FStar_Syntax_Syntax.Quote_dynamic -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1, m) ->
        let uu____16869 = unbound_variables t1 in
        let uu____16872 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern (uu____16877, args) ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____16932 ->
                      match uu____16932 with
                      | (a, uu____16944) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____16953, uu____16954, t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____16960, t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____16966 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____16973 -> []
          | FStar_Syntax_Syntax.Meta_named uu____16974 -> [] in
        FStar_List.append uu____16869 uu____16872
and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t, uu____16981) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t, uu____16991) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____17001 = unbound_variables ct.FStar_Syntax_Syntax.result_typ in
        let uu____17004 =
          FStar_List.collect
            (fun uu____17018 ->
               match uu____17018 with
               | (a, uu____17030) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args in
        FStar_List.append uu____17001 uu____17004
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
            let uu____17144 = head_and_args h in
            (match uu____17144 with
             | (head, args) ->
                 let uu____17205 =
                   let uu____17206 = FStar_Syntax_Subst.compress head in
                   uu____17206.FStar_Syntax_Syntax.n in
                 (match uu____17205 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____17259 -> aux (h :: acc) t)) in
      aux [] attrs
let (extract_attr :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid ->
    fun se ->
      let uu____17282 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs in
      match uu____17282 with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs', t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2557_17324 = se in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2557_17324.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2557_17324.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2557_17324.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2557_17324.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs';
                FStar_Syntax_Syntax.sigopts =
                  (uu___2557_17324.FStar_Syntax_Syntax.sigopts)
              }), t)
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu____17330 =
      let uu____17331 = FStar_Syntax_Subst.compress t in
      uu____17331.FStar_Syntax_Syntax.n in
    match uu____17330 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____17334, c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats, uu____17360)::uu____17361 ->
                  let pats' = unmeta pats in
                  let uu____17421 = head_and_args pats' in
                  (match uu____17421 with
                   | (head, uu____17439) ->
                       let uu____17464 =
                         let uu____17465 = un_uinst head in
                         uu____17465.FStar_Syntax_Syntax.n in
                       (match uu____17464 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____17469 -> false))
              | uu____17470 -> false)
         | uu____17481 -> false)
    | uu____17482 -> false
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e ->
    let uu____17496 = let uu____17513 = unmeta e in head_and_args uu____17513 in
    match uu____17496 with
    | (head, args) ->
        let uu____17544 =
          let uu____17559 =
            let uu____17560 = un_uinst head in
            uu____17560.FStar_Syntax_Syntax.n in
          (uu____17559, args) in
        (match uu____17544 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, uu____17578) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            uu____17602::(hd, uu____17604)::(tl, uu____17606)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____17673 =
               let uu____17676 =
                 let uu____17679 = list_elements tl in
                 FStar_Util.must uu____17679 in
               hd :: uu____17676 in
             FStar_Pervasives_Native.Some uu____17673
         | uu____17688 -> FStar_Pervasives_Native.None)
let (unthunk : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t ->
    let uu____17710 =
      let uu____17711 = FStar_Syntax_Subst.compress t in
      uu____17711.FStar_Syntax_Syntax.n in
    match uu____17710 with
    | FStar_Syntax_Syntax.Tm_abs (b::[], e, uu____17716) ->
        let uu____17751 = FStar_Syntax_Subst.open_term [b] e in
        (match uu____17751 with
         | (bs, e1) ->
             let b1 = FStar_List.hd bs in
             let uu____17783 = is_free_in (FStar_Pervasives_Native.fst b1) e1 in
             if uu____17783
             then
               let uu____17786 =
                 let uu____17797 = FStar_Syntax_Syntax.as_arg exp_unit in
                 [uu____17797] in
               mk_app t uu____17786
             else e1)
    | uu____17823 ->
        let uu____17824 =
          let uu____17835 = FStar_Syntax_Syntax.as_arg exp_unit in
          [uu____17835] in
        mk_app t uu____17824
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
        let uu____17894 = list_elements e in
        match uu____17894 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             []) in
      let one_pat p =
        let uu____17927 =
          let uu____17944 = unmeta p in
          FStar_All.pipe_right uu____17944 head_and_args in
        match uu____17927 with
        | (head, args) ->
            let uu____17995 =
              let uu____18010 =
                let uu____18011 = un_uinst head in
                uu____18011.FStar_Syntax_Syntax.n in
              (uu____18010, args) in
            (match uu____17995 with
             | (FStar_Syntax_Syntax.Tm_fvar fv,
                (uu____18033, uu____18034)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____18086 ->
                 let uu____18101 =
                   let uu____18106 =
                     let uu____18107 = tts p in
                     FStar_Util.format1
                       "Not an atomic SMT pattern: %s; patterns on lemmas must be a list of simple SMTPat's or a single SMTPatOr containing a list of lists of patterns"
                       uu____18107 in
                   (FStar_Errors.Error_IllSMTPat, uu____18106) in
                 FStar_Errors.raise_error uu____18101
                   p.FStar_Syntax_Syntax.pos) in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____18147 =
            let uu____18164 = unmeta t1 in
            FStar_All.pipe_right uu____18164 head_and_args in
          match uu____18147 with
          | (head, args) ->
              let uu____18211 =
                let uu____18226 =
                  let uu____18227 = un_uinst head in
                  uu____18227.FStar_Syntax_Syntax.n in
                (uu____18226, args) in
              (match uu____18211 with
               | (FStar_Syntax_Syntax.Tm_fvar fv, (e, uu____18246)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____18283 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____18313 = smt_pat_or t1 in
            (match uu____18313 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____18335 = list_elements1 e in
                 FStar_All.pipe_right uu____18335
                   (FStar_List.map
                      (fun branch1 ->
                         let uu____18365 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____18365
                           (FStar_List.map one_pat)))
             | uu____18394 ->
                 let uu____18399 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____18399])
        | uu____18454 ->
            let uu____18457 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____18457] in
      let uu____18512 =
        let uu____18543 =
          let uu____18544 = FStar_Syntax_Subst.compress t in
          uu____18544.FStar_Syntax_Syntax.n in
        match uu____18543 with
        | FStar_Syntax_Syntax.Tm_arrow (binders, c) ->
            let uu____18599 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____18599 with
             | (binders1, c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____18666;
                        FStar_Syntax_Syntax.effect_name = uu____18667;
                        FStar_Syntax_Syntax.result_typ = uu____18668;
                        FStar_Syntax_Syntax.effect_args =
                          (pre, uu____18670)::(post, uu____18672)::(pats,
                                                                    uu____18674)::[];
                        FStar_Syntax_Syntax.flags = uu____18675;_}
                      ->
                      let uu____18736 = lemma_pats pats in
                      (binders1, pre, post, uu____18736)
                  | uu____18771 -> failwith "impos"))
        | uu____18802 -> failwith "Impos" in
      match uu____18512 with
      | (binders, pre, post, patterns) ->
          let post1 = unthunk_lemma_post post in
          let body =
            let uu____18885 =
              let uu____18886 =
                let uu____18893 = mk_imp pre post1 in
                let uu____18896 =
                  let uu____18897 =
                    let uu____18918 =
                      FStar_Syntax_Syntax.binders_to_names binders in
                    (uu____18918, patterns) in
                  FStar_Syntax_Syntax.Meta_pattern uu____18897 in
                (uu____18893, uu____18896) in
              FStar_Syntax_Syntax.Tm_meta uu____18886 in
            FStar_Syntax_Syntax.mk uu____18885 t.FStar_Syntax_Syntax.pos in
          let quant =
            let uu____18942 = universe_of_binders binders in
            FStar_List.fold_right2
              (fun b ->
                 fun u ->
                   fun out -> mk_forall u (FStar_Pervasives_Native.fst b) out)
              binders uu____18942 body in
          quant
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____18971 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
let (is_layered : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff uu____18977 -> true
    | uu____18978 -> false
let (is_dm4f : FStar_Syntax_Syntax.eff_decl -> Prims.bool) =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.DM4F_eff uu____18984 -> true
    | uu____18985 -> false
let (apply_wp_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun f ->
    fun combs ->
      let uu____19001 = f combs.FStar_Syntax_Syntax.ret_wp in
      let uu____19002 = f combs.FStar_Syntax_Syntax.bind_wp in
      let uu____19003 = f combs.FStar_Syntax_Syntax.stronger in
      let uu____19004 = f combs.FStar_Syntax_Syntax.if_then_else in
      let uu____19005 = f combs.FStar_Syntax_Syntax.ite_wp in
      let uu____19006 = f combs.FStar_Syntax_Syntax.close_wp in
      let uu____19007 = f combs.FStar_Syntax_Syntax.trivial in
      let uu____19008 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.repr in
      let uu____19011 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.return_repr in
      let uu____19014 =
        FStar_Util.map_option f combs.FStar_Syntax_Syntax.bind_repr in
      {
        FStar_Syntax_Syntax.ret_wp = uu____19001;
        FStar_Syntax_Syntax.bind_wp = uu____19002;
        FStar_Syntax_Syntax.stronger = uu____19003;
        FStar_Syntax_Syntax.if_then_else = uu____19004;
        FStar_Syntax_Syntax.ite_wp = uu____19005;
        FStar_Syntax_Syntax.close_wp = uu____19006;
        FStar_Syntax_Syntax.trivial = uu____19007;
        FStar_Syntax_Syntax.repr = uu____19008;
        FStar_Syntax_Syntax.return_repr = uu____19011;
        FStar_Syntax_Syntax.bind_repr = uu____19014
      }
let (apply_layered_eff_combinators :
  (FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun f ->
    fun combs ->
      let map_tuple uu____19045 =
        match uu____19045 with
        | (ts1, ts2) ->
            let uu____19056 = f ts1 in
            let uu____19057 = f ts2 in (uu____19056, uu____19057) in
      let uu____19058 = map_tuple combs.FStar_Syntax_Syntax.l_repr in
      let uu____19063 = map_tuple combs.FStar_Syntax_Syntax.l_return in
      let uu____19068 = map_tuple combs.FStar_Syntax_Syntax.l_bind in
      let uu____19073 = map_tuple combs.FStar_Syntax_Syntax.l_subcomp in
      let uu____19078 = map_tuple combs.FStar_Syntax_Syntax.l_if_then_else in
      {
        FStar_Syntax_Syntax.l_repr = uu____19058;
        FStar_Syntax_Syntax.l_return = uu____19063;
        FStar_Syntax_Syntax.l_bind = uu____19068;
        FStar_Syntax_Syntax.l_subcomp = uu____19073;
        FStar_Syntax_Syntax.l_if_then_else = uu____19078
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
          let uu____19099 = apply_wp_eff_combinators f combs1 in
          FStar_Syntax_Syntax.Primitive_eff uu____19099
      | FStar_Syntax_Syntax.DM4F_eff combs1 ->
          let uu____19101 = apply_wp_eff_combinators f combs1 in
          FStar_Syntax_Syntax.DM4F_eff uu____19101
      | FStar_Syntax_Syntax.Layered_eff combs1 ->
          let uu____19103 = apply_layered_eff_combinators f combs1 in
          FStar_Syntax_Syntax.Layered_eff uu____19103
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
    | uu____19117 -> FStar_Pervasives_Native.None
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
        let uu____19130 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_repr
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____19130
          (fun uu____19137 -> FStar_Pervasives_Native.Some uu____19137)
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
        let uu____19174 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_bind
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____19174
          (fun uu____19181 -> FStar_Pervasives_Native.Some uu____19181)
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
        let uu____19194 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_return
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____19194
          (fun uu____19201 -> FStar_Pervasives_Native.Some uu____19201)
let (get_wp_trivial_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____19214 -> FStar_Pervasives_Native.Some uu____19214)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.trivial
          (fun uu____19218 -> FStar_Pervasives_Native.Some uu____19218)
    | uu____19219 -> FStar_Pervasives_Native.None
let (get_layered_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19230 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_if_then_else
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____19230
          (fun uu____19237 -> FStar_Pervasives_Native.Some uu____19237)
    | uu____19238 -> FStar_Pervasives_Native.None
let (get_wp_if_then_else_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____19251 -> FStar_Pervasives_Native.Some uu____19251)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.if_then_else
          (fun uu____19255 -> FStar_Pervasives_Native.Some uu____19255)
    | uu____19256 -> FStar_Pervasives_Native.None
let (get_wp_ite_combinator :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.tscheme FStar_Pervasives_Native.option)
  =
  fun ed ->
    match ed.FStar_Syntax_Syntax.combinators with
    | FStar_Syntax_Syntax.Primitive_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____19269 -> FStar_Pervasives_Native.Some uu____19269)
    | FStar_Syntax_Syntax.DM4F_eff combs ->
        FStar_All.pipe_right combs.FStar_Syntax_Syntax.ite_wp
          (fun uu____19273 -> FStar_Pervasives_Native.Some uu____19273)
    | uu____19274 -> FStar_Pervasives_Native.None
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
    | FStar_Syntax_Syntax.Primitive_eff uu____19296 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.DM4F_eff uu____19297 ->
        FStar_Pervasives_Native.None
    | FStar_Syntax_Syntax.Layered_eff combs ->
        let uu____19299 =
          FStar_All.pipe_right combs.FStar_Syntax_Syntax.l_subcomp
            FStar_Pervasives_Native.fst in
        FStar_All.pipe_right uu____19299
          (fun uu____19306 -> FStar_Pervasives_Native.Some uu____19306)