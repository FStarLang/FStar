open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____40463 = FStar_ST.op_Bang tts_f  in
    match uu____40463 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____40527 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____40527 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____40534 =
      let uu____40537 =
        let uu____40540 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____40540]  in
      FStar_List.append lid.FStar_Ident.ns uu____40537  in
    FStar_Ident.lid_of_ids uu____40534
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____40558 .
    (FStar_Syntax_Syntax.bv * 'Auu____40558) ->
      (FStar_Syntax_Syntax.term * 'Auu____40558)
  =
  fun uu____40571  ->
    match uu____40571 with
    | (b,imp) ->
        let uu____40578 = FStar_Syntax_Syntax.bv_to_name b  in
        (uu____40578, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____40630 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____40630
            then []
            else
              (let uu____40649 = arg_of_non_null_binder b  in [uu____40649])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____40684 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____40766 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____40766
              then
                let b1 =
                  let uu____40792 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____40792, (FStar_Pervasives_Native.snd b))  in
                let uu____40799 = arg_of_non_null_binder b1  in
                (b1, uu____40799)
              else
                (let uu____40822 = arg_of_non_null_binder b  in
                 (b, uu____40822))))
       in
    FStar_All.pipe_right uu____40684 FStar_List.unzip
  
let (name_binders :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____40956 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____40956
              then
                let uu____40965 = b  in
                match uu____40965 with
                | (a,imp) ->
                    let b1 =
                      let uu____40985 =
                        let uu____40987 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____40987  in
                      FStar_Ident.id_of_text uu____40985  in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      }  in
                    (b2, imp)
              else b))
  
let (name_function_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
        let uu____41032 =
          let uu____41039 =
            let uu____41040 =
              let uu____41055 = name_binders binders  in (uu____41055, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____41040  in
          FStar_Syntax_Syntax.mk uu____41039  in
        uu____41032 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____41074 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____41111  ->
            match uu____41111 with
            | (t,imp) ->
                let uu____41122 =
                  let uu____41123 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____41123
                   in
                (uu____41122, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____41178  ->
            match uu____41178 with
            | (t,imp) ->
                let uu____41195 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____41195, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____41208 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____41208
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____41220 . 'Auu____41220 -> 'Auu____41220 Prims.list =
  fun s  -> [s] 
let (subst_of_list :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.subst_t)
  =
  fun formals  ->
    fun actuals  ->
      if (FStar_List.length formals) = (FStar_List.length actuals)
      then
        FStar_List.fold_right2
          (fun f  ->
             fun a  ->
               fun out  ->
                 (FStar_Syntax_Syntax.NT
                    ((FStar_Pervasives_Native.fst f),
                      (FStar_Pervasives_Native.fst a)))
                 :: out) formals actuals []
      else failwith "Ill-formed substitution"
  
let (rename_binders :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t)
  =
  fun replace_xs  ->
    fun with_ys  ->
      if (FStar_List.length replace_xs) = (FStar_List.length with_ys)
      then
        FStar_List.map2
          (fun uu____41346  ->
             fun uu____41347  ->
               match (uu____41346, uu____41347) with
               | ((x,uu____41373),(y,uu____41375)) ->
                   let uu____41396 =
                     let uu____41403 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____41403)  in
                   FStar_Syntax_Syntax.NT uu____41396) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____41419) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____41425,uu____41426) ->
        unmeta e2
    | uu____41467 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____41481 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____41488 -> e1
         | uu____41497 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____41499,uu____41500) ->
        unmeta_safe e2
    | uu____41541 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____41560 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____41563 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____41577 = univ_kernel u1  in
        (match uu____41577 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____41594 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____41603 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____41618 = univ_kernel u  in
    FStar_Pervasives_Native.snd uu____41618
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____41638,uu____41639) ->
          failwith "Impossible: compare_univs"
      | (uu____41643,FStar_Syntax_Syntax.U_bvar uu____41644) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____41649) ->
          ~- (Prims.parse_int "1")
      | (uu____41651,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____41654) -> ~- (Prims.parse_int "1")
      | (uu____41656,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____41660,FStar_Syntax_Syntax.U_unif
         uu____41661) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____41671,FStar_Syntax_Syntax.U_name
         uu____41672) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____41700 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____41702 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____41700 - uu____41702
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____41720 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____41720
                 (fun uu____41736  ->
                    match uu____41736 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____41764,uu____41765) ->
          ~- (Prims.parse_int "1")
      | (uu____41769,FStar_Syntax_Syntax.U_max uu____41770) ->
          (Prims.parse_int "1")
      | uu____41774 ->
          let uu____41779 = univ_kernel u1  in
          (match uu____41779 with
           | (k1,n1) ->
               let uu____41790 = univ_kernel u2  in
               (match uu____41790 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____41821 = compare_univs u1 u2  in
      uu____41821 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____41840 =
        let uu____41841 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____41841;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____41840
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____41861 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____41870 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____41893 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____41902 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____41929 =
          let uu____41930 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____41930  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____41929;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____41959 =
          let uu____41960 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____41960  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____41959;
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
  fun c  ->
    fun f  ->
      let uu___631_41996 = c  in
      let uu____41997 =
        let uu____41998 =
          let uu___633_41999 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___633_41999.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___633_41999.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___633_41999.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___633_41999.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____41998  in
      {
        FStar_Syntax_Syntax.n = uu____41997;
        FStar_Syntax_Syntax.pos = (uu___631_41996.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___631_41996.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____42025 -> c
        | FStar_Syntax_Syntax.GTotal uu____42034 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___645_42045 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___645_42045.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___645_42045.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___645_42045.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___645_42045.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___648_42046 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___648_42046.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___648_42046.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____42049  ->
           let uu____42050 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____42050)
  
let (comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,FStar_Pervasives_Native.Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu____42090 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____42105 -> true
    | FStar_Syntax_Syntax.GTotal uu____42115 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___402_42140  ->
               match uu___402_42140 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____42144 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___403_42157  ->
               match uu___403_42157 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____42161 -> false)))
  
let (is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
        FStar_Parser_Const.effect_Tot_lid)
       ||
       (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
          FStar_Parser_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___404_42174  ->
               match uu___404_42174 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____42178 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___405_42195  ->
            match uu___405_42195 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____42199 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___406_42212  ->
            match uu___406_42212 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____42216 -> false))
  
let (is_tot_or_gtot_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (is_total_comp c) ||
      (FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid
         (comp_effect_name c))
  
let (is_pure_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Pure_lid)
  
let (is_pure_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____42248 -> true
    | FStar_Syntax_Syntax.GTotal uu____42258 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___407_42273  ->
                   match uu___407_42273 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____42276 -> false)))
  
let (is_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Parser_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Parser_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Parser_Const.effect_Ghost_lid l)
  
let (is_div_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_DIV_lid) ||
       (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Div_lid))
      || (FStar_Ident.lid_equals l FStar_Parser_Const.effect_Dv_lid)
  
let (is_pure_or_ghost_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  -> (is_pure_comp c) || (is_ghost_effect (comp_effect_name c)) 
let (is_pure_or_ghost_effect : FStar_Ident.lident -> Prims.bool) =
  fun l  -> (is_pure_effect l) || (is_ghost_effect l) 
let (is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___408_42321  ->
               match uu___408_42321 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____42324 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____42340 =
      let uu____42341 = FStar_Syntax_Subst.compress t  in
      uu____42341.FStar_Syntax_Syntax.n  in
    match uu____42340 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____42345,c) -> is_pure_or_ghost_comp c
    | uu____42367 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____42382 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____42391 =
      let uu____42392 = FStar_Syntax_Subst.compress t  in
      uu____42392.FStar_Syntax_Syntax.n  in
    match uu____42391 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____42396,c) -> is_lemma_comp c
    | uu____42418 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____42426 =
      let uu____42427 = FStar_Syntax_Subst.compress t  in
      uu____42427.FStar_Syntax_Syntax.n  in
    match uu____42426 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____42431) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____42457) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____42494,t1,uu____42496) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____42522,uu____42523) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____42565) -> head_of t1
    | uu____42570 -> t
  
let (head_and_args :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list))
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____42648 -> (t1, [])
  
let rec (head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term * (FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list))
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____42730 = head_and_args' head1  in
        (match uu____42730 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____42799 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____42826) ->
        FStar_Syntax_Subst.compress t2
    | uu____42831 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____42839 =
      let uu____42840 = FStar_Syntax_Subst.compress t  in
      uu____42840.FStar_Syntax_Syntax.n  in
    match uu____42839 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____42844,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____42872)::uu____42873 ->
                  let pats' = unmeta pats  in
                  let uu____42933 = head_and_args pats'  in
                  (match uu____42933 with
                   | (head1,uu____42952) ->
                       let uu____42977 =
                         let uu____42978 = un_uinst head1  in
                         uu____42978.FStar_Syntax_Syntax.n  in
                       (match uu____42977 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____42983 -> false))
              | uu____42985 -> false)
         | uu____42997 -> false)
    | uu____42999 -> false
  
let (is_ml_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
           FStar_Parser_Const.effect_ML_lid)
          ||
          (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___409_43018  ->
                   match uu___409_43018 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____43021 -> false)))
    | uu____43023 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____43040) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____43050) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____43079 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____43088 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___827_43100 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___827_43100.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___827_43100.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___827_43100.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___827_43100.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____43114  ->
           let uu____43115 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____43115 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_43133  ->
            match uu___410_43133 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____43137 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____43145 -> []
    | FStar_Syntax_Syntax.GTotal uu____43162 -> []
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
  fun l  ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
  
let (is_primop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun f  ->
    match f.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____43206 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____43216,uu____43217) ->
        unascribe e2
    | uu____43258 -> e1
  
let rec (ascribe :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.comp'
                                                             FStar_Syntax_Syntax.syntax)
      FStar_Util.either * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option) ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun k  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____43311,uu____43312) ->
          ascribe t' k
      | uu____43353 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____43380 =
      let uu____43389 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____43389  in
    uu____43380 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____43445 =
      let uu____43446 = FStar_Syntax_Subst.compress t  in
      uu____43446.FStar_Syntax_Syntax.n  in
    match uu____43445 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____43450 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____43450
    | uu____43451 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____43458 =
      let uu____43459 = FStar_Syntax_Subst.compress t  in
      uu____43459.FStar_Syntax_Syntax.n  in
    match uu____43458 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____43463 ->
             let uu____43472 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____43472
         | uu____43473 -> t)
    | uu____43474 -> t
  
let (eq_lazy_kind :
  FStar_Syntax_Syntax.lazy_kind ->
    FStar_Syntax_Syntax.lazy_kind -> Prims.bool)
  =
  fun k  ->
    fun k'  ->
      match (k, k') with
      | (FStar_Syntax_Syntax.BadLazy ,FStar_Syntax_Syntax.BadLazy ) -> true
      | (FStar_Syntax_Syntax.Lazy_bv ,FStar_Syntax_Syntax.Lazy_bv ) -> true
      | (FStar_Syntax_Syntax.Lazy_binder ,FStar_Syntax_Syntax.Lazy_binder )
          -> true
      | (FStar_Syntax_Syntax.Lazy_fvar ,FStar_Syntax_Syntax.Lazy_fvar ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_comp ,FStar_Syntax_Syntax.Lazy_comp ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_env ,FStar_Syntax_Syntax.Lazy_env ) -> true
      | (FStar_Syntax_Syntax.Lazy_proofstate
         ,FStar_Syntax_Syntax.Lazy_proofstate ) -> true
      | (FStar_Syntax_Syntax.Lazy_goal ,FStar_Syntax_Syntax.Lazy_goal ) ->
          true
      | (FStar_Syntax_Syntax.Lazy_sigelt ,FStar_Syntax_Syntax.Lazy_sigelt )
          -> true
      | (FStar_Syntax_Syntax.Lazy_uvar ,FStar_Syntax_Syntax.Lazy_uvar ) ->
          true
      | uu____43498 -> false
  
let rec unlazy_as_t :
  'Auu____43511 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____43511
  =
  fun k  ->
    fun t  ->
      let uu____43522 =
        let uu____43523 = FStar_Syntax_Subst.compress t  in
        uu____43523.FStar_Syntax_Syntax.n  in
      match uu____43522 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____43528;
            FStar_Syntax_Syntax.rng = uu____43529;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____43532 -> failwith "Not a Tm_lazy of the expected kind"
  
let mk_lazy :
  'a .
    'a ->
      FStar_Syntax_Syntax.typ ->
        FStar_Syntax_Syntax.lazy_kind ->
          FStar_Range.range FStar_Pervasives_Native.option ->
            FStar_Syntax_Syntax.term
  =
  fun t  ->
    fun typ  ->
      fun k  ->
        fun r  ->
          let rng =
            match r with
            | FStar_Pervasives_Native.Some r1 -> r1
            | FStar_Pervasives_Native.None  -> FStar_Range.dummyRange  in
          let i =
            let uu____43573 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____43573;
              FStar_Syntax_Syntax.lkind = k;
              FStar_Syntax_Syntax.ltyp = typ;
              FStar_Syntax_Syntax.rng = rng
            }  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_lazy i)
            FStar_Pervasives_Native.None rng
  
let (canon_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____43586 =
      let uu____43601 = unascribe t  in head_and_args' uu____43601  in
    match uu____43586 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____43635 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____43646 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____43657 -> false
  
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
  fun f  ->
    fun g  ->
      match (f, g) with
      | (Equal ,Equal ) -> Equal
      | (NotEqual ,uu____43707) -> NotEqual
      | (uu____43708,NotEqual ) -> NotEqual
      | (Unknown ,uu____43709) -> Unknown
      | (uu____43710,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_43831 = if uu___411_43831 then Equal else Unknown
         in
      let equal_iff uu___412_43842 =
        if uu___412_43842 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____43863 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____43885 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____43885
        then
          let uu____43889 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____43966  ->
                    match uu____43966 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____44007 = eq_tm a1 a2  in
                        eq_inj acc uu____44007) Equal) uu____43889
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____44021 =
          let uu____44038 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____44038 head_and_args  in
        match uu____44021 with
        | (head1,args1) ->
            let uu____44091 =
              let uu____44108 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____44108 head_and_args  in
            (match uu____44091 with
             | (head2,args2) ->
                 let uu____44161 =
                   let uu____44166 =
                     let uu____44167 = un_uinst head1  in
                     uu____44167.FStar_Syntax_Syntax.n  in
                   let uu____44170 =
                     let uu____44171 = un_uinst head2  in
                     uu____44171.FStar_Syntax_Syntax.n  in
                   (uu____44166, uu____44170)  in
                 (match uu____44161 with
                  | (FStar_Syntax_Syntax.Tm_fvar
                     f,FStar_Syntax_Syntax.Tm_fvar g) when
                      (f.FStar_Syntax_Syntax.fv_qual =
                         (FStar_Pervasives_Native.Some
                            FStar_Syntax_Syntax.Data_ctor))
                        &&
                        (g.FStar_Syntax_Syntax.fv_qual =
                           (FStar_Pervasives_Native.Some
                              FStar_Syntax_Syntax.Data_ctor))
                      -> FStar_Pervasives_Native.Some (f, args1, g, args2)
                  | uu____44198 -> FStar_Pervasives_Native.None))
         in
      let uu____44211 =
        let uu____44216 =
          let uu____44217 = unmeta t11  in uu____44217.FStar_Syntax_Syntax.n
           in
        let uu____44220 =
          let uu____44221 = unmeta t21  in uu____44221.FStar_Syntax_Syntax.n
           in
        (uu____44216, uu____44220)  in
      match uu____44211 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____44227,uu____44228) ->
          let uu____44229 = unlazy t11  in eq_tm uu____44229 t21
      | (uu____44230,FStar_Syntax_Syntax.Tm_lazy uu____44231) ->
          let uu____44232 = unlazy t21  in eq_tm t11 uu____44232
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____44235 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____44259 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____44259
            (fun uu____44307  ->
               match uu____44307 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____44322 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____44322
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____44336 = eq_tm f g  in
          eq_and uu____44336
            (fun uu____44339  ->
               let uu____44340 = eq_univs_list us vs  in equal_if uu____44340)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____44342),uu____44343) -> Unknown
      | (uu____44344,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____44345)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____44348 = FStar_Const.eq_const c d  in
          equal_iff uu____44348
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____44351)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____44353))) ->
          let uu____44382 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____44382
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____44436 =
            let uu____44441 =
              let uu____44442 = un_uinst h1  in
              uu____44442.FStar_Syntax_Syntax.n  in
            let uu____44445 =
              let uu____44446 = un_uinst h2  in
              uu____44446.FStar_Syntax_Syntax.n  in
            (uu____44441, uu____44445)  in
          (match uu____44436 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____44452 =
                    let uu____44454 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____44454  in
                  FStar_List.mem uu____44452 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____44456 ->
               let uu____44461 = eq_tm h1 h2  in
               eq_and uu____44461 (fun uu____44463  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____44569 = FStar_List.zip bs1 bs2  in
            let uu____44632 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____44669  ->
                 fun a  ->
                   match uu____44669 with
                   | (b1,b2) ->
                       eq_and a (fun uu____44762  -> branch_matches b1 b2))
              uu____44569 uu____44632
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____44767 = eq_univs u v1  in equal_if uu____44767
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____44781 = eq_quoteinfo q1 q2  in
          eq_and uu____44781 (fun uu____44783  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____44796 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____44796 (fun uu____44798  -> eq_tm phi1 phi2)
      | uu____44799 -> Unknown

and (eq_quoteinfo :
  FStar_Syntax_Syntax.quoteinfo -> FStar_Syntax_Syntax.quoteinfo -> eq_result)
  =
  fun q1  ->
    fun q2  ->
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
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ([],uu____44871) -> NotEqual
      | (uu____44902,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____44994 = eq_tm t1 t2  in
             match uu____44994 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____44995 = eq_antiquotes a11 a21  in
                 (match uu____44995 with
                  | NotEqual  -> NotEqual
                  | uu____44996 -> Unknown)
             | Equal  -> eq_antiquotes a11 a21)

and (eq_aqual :
  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option ->
      eq_result)
  =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          Equal
      | (FStar_Pervasives_Native.None ,uu____45011) -> NotEqual
      | (uu____45018,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____45048 -> NotEqual

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
  fun b1  ->
    fun b2  ->
      let related_by f o1 o2 =
        match (o1, o2) with
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
            true
        | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
            f x y
        | (uu____45140,uu____45141) -> false  in
      let uu____45151 = b1  in
      match uu____45151 with
      | (p1,w1,t1) ->
          let uu____45185 = b2  in
          (match uu____45185 with
           | (p2,w2,t2) ->
               let uu____45219 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____45219
               then
                 let uu____45222 =
                   (let uu____45226 = eq_tm t1 t2  in uu____45226 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____45235 = eq_tm t11 t21  in
                             uu____45235 = Equal) w1 w2)
                    in
                 (if uu____45222 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____45300)::a11,(b,uu____45303)::b1) ->
          let uu____45377 = eq_tm a b  in
          (match uu____45377 with
           | Equal  -> eq_args a11 b1
           | uu____45378 -> Unknown)
      | uu____45379 -> Unknown

and (eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool)
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)

let rec (unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____45415) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____45421,uu____45422) ->
        unrefine t2
    | uu____45463 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45471 =
      let uu____45472 = FStar_Syntax_Subst.compress t  in
      uu____45472.FStar_Syntax_Syntax.n  in
    match uu____45471 with
    | FStar_Syntax_Syntax.Tm_uvar uu____45476 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____45491) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____45496 ->
        let uu____45513 =
          let uu____45514 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____45514 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____45513 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____45577,uu____45578) ->
        is_uvar t1
    | uu____45619 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45628 =
      let uu____45629 = unrefine t  in uu____45629.FStar_Syntax_Syntax.n  in
    match uu____45628 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____45635) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____45661) -> is_unit t1
    | uu____45666 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45675 =
      let uu____45676 = FStar_Syntax_Subst.compress t  in
      uu____45676.FStar_Syntax_Syntax.n  in
    match uu____45675 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____45681 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45690 =
      let uu____45691 = unrefine t  in uu____45691.FStar_Syntax_Syntax.n  in
    match uu____45690 with
    | FStar_Syntax_Syntax.Tm_type uu____45695 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____45699) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____45725) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____45730,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____45752 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____45761 =
      let uu____45762 = FStar_Syntax_Subst.compress e  in
      uu____45762.FStar_Syntax_Syntax.n  in
    match uu____45761 with
    | FStar_Syntax_Syntax.Tm_abs uu____45766 -> true
    | uu____45786 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45795 =
      let uu____45796 = FStar_Syntax_Subst.compress t  in
      uu____45796.FStar_Syntax_Syntax.n  in
    match uu____45795 with
    | FStar_Syntax_Syntax.Tm_arrow uu____45800 -> true
    | uu____45816 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____45826) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____45832,uu____45833) ->
        pre_typ t2
    | uu____45874 -> t1
  
let (destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list FStar_Pervasives_Native.option)
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____45899 =
        let uu____45900 = un_uinst typ1  in uu____45900.FStar_Syntax_Syntax.n
         in
      match uu____45899 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____45965 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____45995 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____46016,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____46023) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____46028,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____46039,uu____46040,uu____46041,uu____46042,uu____46043) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____46053,uu____46054,uu____46055,uu____46056) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____46062,uu____46063,uu____46064,uu____46065,uu____46066) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____46074,uu____46075) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____46077,uu____46078) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____46081 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____46082 -> []
    | FStar_Syntax_Syntax.Sig_main uu____46083 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____46097 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_46123  ->
    match uu___413_46123 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____46137 'Auu____46138 .
    ('Auu____46137 FStar_Syntax_Syntax.syntax * 'Auu____46138) ->
      FStar_Range.range
  =
  fun uu____46149  ->
    match uu____46149 with | (hd1,uu____46157) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____46171 'Auu____46172 .
    ('Auu____46171 FStar_Syntax_Syntax.syntax * 'Auu____46172) Prims.list ->
      FStar_Range.range -> FStar_Range.range
  =
  fun args  ->
    fun r  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left
           (fun r1  -> fun a  -> FStar_Range.union_ranges r1 (range_of_arg a))
           r)
  
let (mk_app :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list -> FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun args  ->
      match args with
      | [] -> f
      | uu____46270 ->
          let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
          FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args))
            FStar_Pervasives_Native.None r
  
let (mk_app_binders :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun f  ->
    fun bs  ->
      let uu____46329 =
        FStar_List.map
          (fun uu____46356  ->
             match uu____46356 with
             | (bv,aq) ->
                 let uu____46375 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____46375, aq)) bs
         in
      mk_app f uu____46329
  
let (mk_data :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Syntax_Syntax.syntax)
  =
  fun l  ->
    fun args  ->
      match args with
      | [] ->
          let uu____46425 = FStar_Ident.range_of_lid l  in
          let uu____46426 =
            let uu____46435 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____46435  in
          uu____46426 FStar_Pervasives_Native.None uu____46425
      | uu____46440 ->
          let e =
            let uu____46454 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____46454 args  in
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            e.FStar_Syntax_Syntax.pos
  
let (field_projector_prefix : Prims.string) = "__proj__" 
let (field_projector_sep : Prims.string) = "__item__" 
let (field_projector_contains_constructor : Prims.string -> Prims.bool) =
  fun s  -> FStar_Util.starts_with s field_projector_prefix 
let (mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string) =
  fun constr  ->
    fun field  ->
      Prims.op_Hat field_projector_prefix
        (Prims.op_Hat constr (Prims.op_Hat field_projector_sep field))
  
let (mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident) =
  fun lid  ->
    fun i  ->
      let itext = i.FStar_Ident.idText  in
      let newi =
        if field_projector_contains_constructor itext
        then i
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText itext),
              (i.FStar_Ident.idRange))
         in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
  
let (mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int -> (FStar_Ident.lident * FStar_Syntax_Syntax.bv))
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____46531 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____46531
          then
            let uu____46534 =
              let uu____46540 =
                let uu____46542 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____46542  in
              let uu____46545 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____46540, uu____46545)  in
            FStar_Ident.mk_ident uu____46534
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1421_46550 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1421_46550.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1421_46550.FStar_Syntax_Syntax.sort)
          }  in
        let uu____46551 = mk_field_projector_name_from_ident lid nm  in
        (uu____46551, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____46563) -> ses
    | uu____46572 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____46583 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____46596 = FStar_Syntax_Unionfind.find uv  in
      match uu____46596 with
      | FStar_Pervasives_Native.Some uu____46599 ->
          let uu____46600 =
            let uu____46602 =
              let uu____46604 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____46604  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____46602  in
          failwith uu____46600
      | uu____46609 -> FStar_Syntax_Unionfind.change uv t
  
let (qualifier_equal :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Syntax_Syntax.qualifier -> Prims.bool)
  =
  fun q1  ->
    fun q2  ->
      match (q1, q2) with
      | (FStar_Syntax_Syntax.Discriminator
         l1,FStar_Syntax_Syntax.Discriminator l2) ->
          FStar_Ident.lid_equals l1 l2
      | (FStar_Syntax_Syntax.Projector
         (l1a,l1b),FStar_Syntax_Syntax.Projector (l2a,l2b)) ->
          (FStar_Ident.lid_equals l1a l2a) &&
            (l1b.FStar_Ident.idText = l2b.FStar_Ident.idText)
      | (FStar_Syntax_Syntax.RecordType
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | (FStar_Syntax_Syntax.RecordConstructor
         (ns1,f1),FStar_Syntax_Syntax.RecordConstructor (ns2,f2)) ->
          ((((FStar_List.length ns1) = (FStar_List.length ns2)) &&
              (FStar_List.forall2
                 (fun x1  ->
                    fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
                 f1 f2))
             && ((FStar_List.length f1) = (FStar_List.length f2)))
            &&
            (FStar_List.forall2
               (fun x1  ->
                  fun x2  -> x1.FStar_Ident.idText = x2.FStar_Ident.idText)
               f1 f2)
      | uu____46692 -> q1 = q2
  
let (abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some rc ->
              let uu____46738 =
                let uu___1482_46739 = rc  in
                let uu____46740 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1482_46739.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____46740;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1482_46739.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____46738
           in
        match bs with
        | [] -> t
        | uu____46757 ->
            let body =
              let uu____46759 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____46759  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____46789 =
                   let uu____46796 =
                     let uu____46797 =
                       let uu____46816 =
                         let uu____46825 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____46825 bs'  in
                       let uu____46840 = close_lopt lopt'  in
                       (uu____46816, t1, uu____46840)  in
                     FStar_Syntax_Syntax.Tm_abs uu____46797  in
                   FStar_Syntax_Syntax.mk uu____46796  in
                 uu____46789 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____46855 ->
                 let uu____46856 =
                   let uu____46863 =
                     let uu____46864 =
                       let uu____46883 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____46892 = close_lopt lopt  in
                       (uu____46883, body, uu____46892)  in
                     FStar_Syntax_Syntax.Tm_abs uu____46864  in
                   FStar_Syntax_Syntax.mk uu____46863  in
                 uu____46856 FStar_Pervasives_Native.None
                   t.FStar_Syntax_Syntax.pos)
  
let (arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____46948 ->
          let uu____46957 =
            let uu____46964 =
              let uu____46965 =
                let uu____46980 = FStar_Syntax_Subst.close_binders bs  in
                let uu____46989 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____46980, uu____46989)  in
              FStar_Syntax_Syntax.Tm_arrow uu____46965  in
            FStar_Syntax_Syntax.mk uu____46964  in
          uu____46957 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____47038 =
        let uu____47039 = FStar_Syntax_Subst.compress t  in
        uu____47039.FStar_Syntax_Syntax.n  in
      match uu____47038 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____47069) ->
               let uu____47078 =
                 let uu____47079 = FStar_Syntax_Subst.compress tres  in
                 uu____47079.FStar_Syntax_Syntax.n  in
               (match uu____47078 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____47122 -> t)
           | uu____47123 -> t)
      | uu____47124 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____47142 =
        let uu____47143 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____47143 t.FStar_Syntax_Syntax.pos  in
      let uu____47144 =
        let uu____47151 =
          let uu____47152 =
            let uu____47159 =
              let uu____47162 =
                let uu____47163 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____47163]  in
              FStar_Syntax_Subst.close uu____47162 t  in
            (b, uu____47159)  in
          FStar_Syntax_Syntax.Tm_refine uu____47152  in
        FStar_Syntax_Syntax.mk uu____47151  in
      uu____47144 FStar_Pervasives_Native.None uu____47142
  
let (branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch) =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec (arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.comp))
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____47243 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____47243 with
         | (bs1,c1) ->
             let uu____47262 = is_total_comp c1  in
             if uu____47262
             then
               let uu____47277 = arrow_formals_comp (comp_result c1)  in
               (match uu____47277 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____47344;
           FStar_Syntax_Syntax.index = uu____47345;
           FStar_Syntax_Syntax.sort = s;_},uu____47347)
        ->
        let rec aux s1 k2 =
          let uu____47378 =
            let uu____47379 = FStar_Syntax_Subst.compress s1  in
            uu____47379.FStar_Syntax_Syntax.n  in
          match uu____47378 with
          | FStar_Syntax_Syntax.Tm_arrow uu____47394 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____47409;
                 FStar_Syntax_Syntax.index = uu____47410;
                 FStar_Syntax_Syntax.sort = s2;_},uu____47412)
              -> aux s2 k2
          | uu____47420 ->
              let uu____47421 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____47421)
           in
        aux s k1
    | uu____47436 ->
        let uu____47437 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____47437)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____47472 = arrow_formals_comp k  in
    match uu____47472 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____47614 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____47614 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____47638 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_47647  ->
                         match uu___414_47647 with
                         | FStar_Syntax_Syntax.DECREASES uu____47649 -> true
                         | uu____47653 -> false))
                  in
               (match uu____47638 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____47688 ->
                    let uu____47691 = is_total_comp c1  in
                    if uu____47691
                    then
                      let uu____47710 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____47710 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____47803;
             FStar_Syntax_Syntax.index = uu____47804;
             FStar_Syntax_Syntax.sort = k2;_},uu____47806)
          -> arrow_until_decreases k2
      | uu____47814 -> ([], FStar_Pervasives_Native.None)  in
    let uu____47835 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____47835 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____47889 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____47910 =
                 FStar_Common.tabulate n_univs (fun uu____47916  -> false)
                  in
               let uu____47919 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____47944  ->
                         match uu____47944 with
                         | (x,uu____47953) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____47910 uu____47919)
           in
        ((n_univs + (FStar_List.length bs)), uu____47889)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____48009 =
            let uu___1604_48010 = rc  in
            let uu____48011 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1604_48010.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____48011;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1604_48010.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____48009
      | uu____48020 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____48054 =
        let uu____48055 =
          let uu____48058 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____48058  in
        uu____48055.FStar_Syntax_Syntax.n  in
      match uu____48054 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____48104 = aux t2 what  in
          (match uu____48104 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____48176 -> ([], t1, abs_body_lcomp)  in
    let uu____48193 = aux t FStar_Pervasives_Native.None  in
    match uu____48193 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____48241 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____48241 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let (mk_letbinding :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
            FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
              -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun lbname  ->
    fun univ_vars  ->
      fun typ  ->
        fun eff  ->
          fun def  ->
            fun lbattrs  ->
              fun pos  ->
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
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Syntax_Syntax.univ_name Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list
                -> FStar_Range.range -> FStar_Syntax_Syntax.letbinding)
  =
  fun recs  ->
    fun lbname  ->
      fun univ_vars  ->
        fun typ  ->
          fun eff  ->
            fun def  ->
              fun attrs  ->
                fun pos  ->
                  let def1 =
                    match (recs, univ_vars) with
                    | (FStar_Pervasives_Native.None ,uu____48404) -> def
                    | (uu____48415,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____48427) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _48443  ->
                                  FStar_Syntax_Syntax.U_name _48443))
                           in
                        let inst1 =
                          FStar_All.pipe_right fvs
                            (FStar_List.map
                               (fun fv  ->
                                  (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                    universes)))
                           in
                        FStar_Syntax_InstFV.instantiate inst1 def
                     in
                  let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ
                     in
                  let def2 =
                    FStar_Syntax_Subst.close_univ_vars univ_vars def1  in
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
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____48525 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____48525 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____48560 ->
            let t' = arrow binders c  in
            let uu____48572 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____48572 with
             | (uvs1,t'1) ->
                 let uu____48593 =
                   let uu____48594 = FStar_Syntax_Subst.compress t'1  in
                   uu____48594.FStar_Syntax_Syntax.n  in
                 (match uu____48593 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____48643 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____48668 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____48679 -> false
  
let (is_lid_equality : FStar_Ident.lident -> Prims.bool) =
  fun x  -> FStar_Ident.lid_equals x FStar_Parser_Const.eq2_lid 
let (is_forall : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.forall_lid 
let (is_exists : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Parser_Const.exists_lid 
let (is_qlid : FStar_Ident.lident -> Prims.bool) =
  fun lid  -> (is_forall lid) || (is_exists lid) 
let (is_equality :
  FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun x  -> is_lid_equality x.FStar_Syntax_Syntax.v 
let (lid_is_connective : FStar_Ident.lident -> Prims.bool) =
  let lst =
    [FStar_Parser_Const.and_lid;
    FStar_Parser_Const.or_lid;
    FStar_Parser_Const.not_lid;
    FStar_Parser_Const.iff_lid;
    FStar_Parser_Const.imp_lid]  in
  fun lid  -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst 
let (is_constructor :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____48742 =
        let uu____48743 = pre_typ t  in uu____48743.FStar_Syntax_Syntax.n  in
      match uu____48742 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____48748 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____48762 =
        let uu____48763 = pre_typ t  in uu____48763.FStar_Syntax_Syntax.n  in
      match uu____48762 with
      | FStar_Syntax_Syntax.Tm_fvar uu____48767 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____48769) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____48795) ->
          is_constructed_typ t1 lid
      | uu____48800 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____48813 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____48814 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____48815 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____48817) -> get_tycon t2
    | uu____48842 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____48850 =
      let uu____48851 = un_uinst t  in uu____48851.FStar_Syntax_Syntax.n  in
    match uu____48850 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____48856 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____48870 =
        let uu____48874 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____48874  in
      match uu____48870 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____48906 -> false
    else false
  
let (ktype : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (ktype0 : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (type_u :
  unit -> (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.universe)) =
  fun uu____48925  ->
    let u =
      let uu____48931 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _48948  -> FStar_Syntax_Syntax.U_unif _48948)
        uu____48931
       in
    let uu____48949 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____48949, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____48962 = eq_tm a a'  in
      match uu____48962 with | Equal  -> true | uu____48965 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____48970 =
    let uu____48977 =
      let uu____48978 =
        let uu____48979 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____48979
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____48978  in
    FStar_Syntax_Syntax.mk uu____48977  in
  uu____48970 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (exp_true_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool true))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_false_bool : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_bool false))
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_unit : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_unit)
    FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_int : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_int (s, FStar_Pervasives_Native.None)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_char : FStar_BaseTypes.char -> FStar_Syntax_Syntax.term) =
  fun c  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_char c))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (exp_string : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant
         (FStar_Const.Const_string (s, FStar_Range.dummyRange)))
      FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (fvar_const : FStar_Ident.lident -> FStar_Syntax_Syntax.term) =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
      FStar_Pervasives_Native.None
  
let (tand : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.and_lid 
let (tor : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.or_lid 
let (timp : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (tiff : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "2"))
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
let (t_ctx_uvar_and_sust : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.ctx_uvar_and_subst_lid 
let (mk_conj_opt :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
    FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
        FStar_Pervasives_Native.option)
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.Some phi2
      | FStar_Pervasives_Native.Some phi11 ->
          let uu____49091 =
            let uu____49094 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____49095 =
              let uu____49102 =
                let uu____49103 =
                  let uu____49120 =
                    let uu____49131 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____49140 =
                      let uu____49151 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____49151]  in
                    uu____49131 :: uu____49140  in
                  (tand, uu____49120)  in
                FStar_Syntax_Syntax.Tm_app uu____49103  in
              FStar_Syntax_Syntax.mk uu____49102  in
            uu____49095 FStar_Pervasives_Native.None uu____49094  in
          FStar_Pervasives_Native.Some uu____49091
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____49228 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____49229 =
          let uu____49236 =
            let uu____49237 =
              let uu____49254 =
                let uu____49265 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____49274 =
                  let uu____49285 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____49285]  in
                uu____49265 :: uu____49274  in
              (op_t, uu____49254)  in
            FStar_Syntax_Syntax.Tm_app uu____49237  in
          FStar_Syntax_Syntax.mk uu____49236  in
        uu____49229 FStar_Pervasives_Native.None uu____49228
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____49342 =
      let uu____49349 =
        let uu____49350 =
          let uu____49367 =
            let uu____49378 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____49378]  in
          (t_not, uu____49367)  in
        FStar_Syntax_Syntax.Tm_app uu____49350  in
      FStar_Syntax_Syntax.mk uu____49349  in
    uu____49342 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
let (mk_conj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tand phi1 phi2 
let (mk_conj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
  
let (mk_disj :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  = fun phi1  -> fun phi2  -> mk_binop tor phi1 phi2 
let (mk_disj_l :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
  
let (mk_imp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2 
let (mk_iff :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2 
let (b2t :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e  ->
    let uu____49575 =
      let uu____49582 =
        let uu____49583 =
          let uu____49600 =
            let uu____49611 = FStar_Syntax_Syntax.as_arg e  in [uu____49611]
             in
          (b2t_v, uu____49600)  in
        FStar_Syntax_Syntax.Tm_app uu____49583  in
      FStar_Syntax_Syntax.mk uu____49582  in
    uu____49575 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49655 =
      let uu____49656 = unmeta t  in uu____49656.FStar_Syntax_Syntax.n  in
    match uu____49655 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____49661 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____49684 = is_t_true t1  in
      if uu____49684
      then t2
      else
        (let uu____49691 = is_t_true t2  in
         if uu____49691 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____49719 = is_t_true t1  in
      if uu____49719
      then t_true
      else
        (let uu____49726 = is_t_true t2  in
         if uu____49726 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____49755 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____49756 =
        let uu____49763 =
          let uu____49764 =
            let uu____49781 =
              let uu____49792 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____49801 =
                let uu____49812 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____49812]  in
              uu____49792 :: uu____49801  in
            (teq, uu____49781)  in
          FStar_Syntax_Syntax.Tm_app uu____49764  in
        FStar_Syntax_Syntax.mk uu____49763  in
      uu____49756 FStar_Pervasives_Native.None uu____49755
  
let (mk_eq2 :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun u  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u]  in
          let uu____49879 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____49880 =
            let uu____49887 =
              let uu____49888 =
                let uu____49905 =
                  let uu____49916 = FStar_Syntax_Syntax.iarg t  in
                  let uu____49925 =
                    let uu____49936 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____49945 =
                      let uu____49956 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____49956]  in
                    uu____49936 :: uu____49945  in
                  uu____49916 :: uu____49925  in
                (eq_inst, uu____49905)  in
              FStar_Syntax_Syntax.Tm_app uu____49888  in
            FStar_Syntax_Syntax.mk uu____49887  in
          uu____49880 FStar_Pervasives_Native.None uu____49879
  
let (mk_has_type :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    fun x  ->
      fun t'  ->
        let t_has_type = fvar_const FStar_Parser_Const.has_type_lid  in
        let t_has_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst
               (t_has_type,
                 [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        let uu____50033 =
          let uu____50040 =
            let uu____50041 =
              let uu____50058 =
                let uu____50069 = FStar_Syntax_Syntax.iarg t  in
                let uu____50078 =
                  let uu____50089 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____50098 =
                    let uu____50109 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____50109]  in
                  uu____50089 :: uu____50098  in
                uu____50069 :: uu____50078  in
              (t_has_type1, uu____50058)  in
            FStar_Syntax_Syntax.Tm_app uu____50041  in
          FStar_Syntax_Syntax.mk uu____50040  in
        uu____50033 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mk_with_type :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun t  ->
      fun e  ->
        let t_with_type =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.with_type_lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None
           in
        let t_with_type1 =
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_uinst (t_with_type, [u]))
            FStar_Pervasives_Native.None FStar_Range.dummyRange
           in
        let uu____50186 =
          let uu____50193 =
            let uu____50194 =
              let uu____50211 =
                let uu____50222 = FStar_Syntax_Syntax.iarg t  in
                let uu____50231 =
                  let uu____50242 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____50242]  in
                uu____50222 :: uu____50231  in
              (t_with_type1, uu____50211)  in
            FStar_Syntax_Syntax.Tm_app uu____50194  in
          FStar_Syntax_Syntax.mk uu____50193  in
        uu____50186 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____50289 =
    let uu____50296 =
      let uu____50297 =
        let uu____50304 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____50304, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____50297  in
    FStar_Syntax_Syntax.mk uu____50296  in
  uu____50289 FStar_Pervasives_Native.None FStar_Range.dummyRange 
let (lex_pair : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.lexcons_lid
    FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (tforall : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (t_haseq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar FStar_Parser_Const.haseq_lid
    FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
  
let (lcomp_of_comp : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.lcomp) =
  fun c0  ->
    let uu____50319 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____50332 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____50343 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____50319 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____50364  -> c0)
  
let (mk_residual_comp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.cflag Prims.list ->
        FStar_Syntax_Syntax.residual_comp)
  =
  fun l  ->
    fun t  ->
      fun f  ->
        {
          FStar_Syntax_Syntax.residual_effect = l;
          FStar_Syntax_Syntax.residual_typ = t;
          FStar_Syntax_Syntax.residual_flags = f
        }
  
let (residual_tot :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.residual_comp)
  =
  fun t  ->
    {
      FStar_Syntax_Syntax.residual_effect = FStar_Parser_Const.effect_Tot_lid;
      FStar_Syntax_Syntax.residual_typ = (FStar_Pervasives_Native.Some t);
      FStar_Syntax_Syntax.residual_flags = [FStar_Syntax_Syntax.TOTAL]
    }
  
let (residual_comp_of_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.residual_comp) =
  fun c  ->
    {
      FStar_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (comp_result c));
      FStar_Syntax_Syntax.residual_flags = (comp_flags c)
    }
  
let (residual_comp_of_lcomp :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.residual_comp) =
  fun lc  ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.FStar_Syntax_Syntax.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (FStar_Pervasives_Native.Some (lc.FStar_Syntax_Syntax.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.FStar_Syntax_Syntax.cflags)
    }
  
let (mk_forall_aux :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun fa  ->
    fun x  ->
      fun body  ->
        let uu____50447 =
          let uu____50454 =
            let uu____50455 =
              let uu____50472 =
                let uu____50483 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____50492 =
                  let uu____50503 =
                    let uu____50512 =
                      let uu____50513 =
                        let uu____50514 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____50514]  in
                      abs uu____50513 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____50512  in
                  [uu____50503]  in
                uu____50483 :: uu____50492  in
              (fa, uu____50472)  in
            FStar_Syntax_Syntax.Tm_app uu____50455  in
          FStar_Syntax_Syntax.mk uu____50454  in
        uu____50447 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (mk_forall_no_univ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  = fun x  -> fun body  -> mk_forall_aux tforall x body 
let (mk_forall :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun u  ->
    fun x  ->
      fun body  ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u]  in
        mk_forall_aux tforall1 x body
  
let (close_forall_no_univs :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ)
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____50641 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____50641
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____50660 -> true
    | uu____50662 -> false
  
let (if_then_else :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t1  ->
      fun t2  ->
        let then_branch =
          let uu____50709 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____50709, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____50738 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____50738, FStar_Pervasives_Native.None, t2)  in
        let uu____50752 =
          let uu____50753 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____50753  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____50752
  
let (mk_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
          FStar_Pervasives_Native.None
         in
      let uu____50829 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____50832 =
        let uu____50843 = FStar_Syntax_Syntax.as_arg p  in [uu____50843]  in
      mk_app uu____50829 uu____50832
  
let (mk_auto_squash :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun u  ->
    fun p  ->
      let sq =
        FStar_Syntax_Syntax.fvar FStar_Parser_Const.auto_squash_lid
          (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "2"))
          FStar_Pervasives_Native.None
         in
      let uu____50883 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____50886 =
        let uu____50897 = FStar_Syntax_Syntax.as_arg p  in [uu____50897]  in
      mk_app uu____50883 uu____50886
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____50932 = head_and_args t  in
    match uu____50932 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____50981 =
          let uu____50996 =
            let uu____50997 = FStar_Syntax_Subst.compress head3  in
            uu____50997.FStar_Syntax_Syntax.n  in
          (uu____50996, args)  in
        (match uu____50981 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____51016)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____51082 =
                    let uu____51087 =
                      let uu____51088 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____51088]  in
                    FStar_Syntax_Subst.open_term uu____51087 p  in
                  (match uu____51082 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____51145 -> failwith "impossible"  in
                       let uu____51153 =
                         let uu____51155 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____51155
                          in
                       if uu____51153
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____51171 -> FStar_Pervasives_Native.None)
         | uu____51174 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51205 = head_and_args t  in
    match uu____51205 with
    | (head1,args) ->
        let uu____51256 =
          let uu____51271 =
            let uu____51272 = FStar_Syntax_Subst.compress head1  in
            uu____51272.FStar_Syntax_Syntax.n  in
          (uu____51271, args)  in
        (match uu____51256 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____51294;
               FStar_Syntax_Syntax.vars = uu____51295;_},u::[]),(t1,uu____51298)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____51345 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51380 = head_and_args t  in
    match uu____51380 with
    | (head1,args) ->
        let uu____51431 =
          let uu____51446 =
            let uu____51447 = FStar_Syntax_Subst.compress head1  in
            uu____51447.FStar_Syntax_Syntax.n  in
          (uu____51446, args)  in
        (match uu____51431 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____51469;
               FStar_Syntax_Syntax.vars = uu____51470;_},u::[]),(t1,uu____51473)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____51520 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____51548 =
      let uu____51565 = unmeta t  in head_and_args uu____51565  in
    match uu____51548 with
    | (head1,uu____51568) ->
        let uu____51593 =
          let uu____51594 = un_uinst head1  in
          uu____51594.FStar_Syntax_Syntax.n  in
        (match uu____51593 with
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
         | uu____51599 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51619 =
      let uu____51632 =
        let uu____51633 = FStar_Syntax_Subst.compress t  in
        uu____51633.FStar_Syntax_Syntax.n  in
      match uu____51632 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____51763 =
            let uu____51774 =
              let uu____51775 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____51775  in
            (b, uu____51774)  in
          FStar_Pervasives_Native.Some uu____51763
      | uu____51792 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____51619
      (fun uu____51830  ->
         match uu____51830 with
         | (b,c) ->
             let uu____51867 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____51867 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____51930 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____51967 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____51967
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____52019 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____52062 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____52103 -> false
  
let (__proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args)) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0 
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____52142) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____52154) ->
          unmeta_monadic t
      | uu____52167 -> f2  in
    let destruct_base_conn f1 =
      let connectives =
        [(FStar_Parser_Const.true_lid, (Prims.parse_int "0"));
        (FStar_Parser_Const.false_lid, (Prims.parse_int "0"));
        (FStar_Parser_Const.and_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.or_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.imp_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.iff_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.ite_lid, (Prims.parse_int "3"));
        (FStar_Parser_Const.not_lid, (Prims.parse_int "1"));
        (FStar_Parser_Const.eq2_lid, (Prims.parse_int "3"));
        (FStar_Parser_Const.eq2_lid, (Prims.parse_int "2"));
        (FStar_Parser_Const.eq3_lid, (Prims.parse_int "4"));
        (FStar_Parser_Const.eq3_lid, (Prims.parse_int "2"))]  in
      let aux f2 uu____52263 =
        match uu____52263 with
        | (lid,arity) ->
            let uu____52272 =
              let uu____52289 = unmeta_monadic f2  in
              head_and_args uu____52289  in
            (match uu____52272 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____52319 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____52319
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____52395 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____52395)
      | uu____52408 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____52475 = head_and_args t1  in
        match uu____52475 with
        | (t2,args) ->
            let uu____52530 = un_uinst t2  in
            let uu____52531 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____52572  ->
                      match uu____52572 with
                      | (t3,imp) ->
                          let uu____52591 = unascribe t3  in
                          (uu____52591, imp)))
               in
            (uu____52530, uu____52531)
         in
      let rec aux qopt out t1 =
        let uu____52642 = let uu____52666 = flat t1  in (qopt, uu____52666)
           in
        match uu____52642 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____52706;
                 FStar_Syntax_Syntax.vars = uu____52707;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____52710);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____52711;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____52712;_},uu____52713)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____52815;
                 FStar_Syntax_Syntax.vars = uu____52816;_},uu____52817::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____52820);
                  FStar_Syntax_Syntax.pos = uu____52821;
                  FStar_Syntax_Syntax.vars = uu____52822;_},uu____52823)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____52940;
               FStar_Syntax_Syntax.vars = uu____52941;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____52944);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____52945;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____52946;_},uu____52947)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____53040 =
              let uu____53044 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____53044  in
            aux uu____53040 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____53054;
               FStar_Syntax_Syntax.vars = uu____53055;_},uu____53056::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____53059);
                FStar_Syntax_Syntax.pos = uu____53060;
                FStar_Syntax_Syntax.vars = uu____53061;_},uu____53062)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____53171 =
              let uu____53175 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____53175  in
            aux uu____53171 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____53185) ->
            let bs = FStar_List.rev out  in
            let uu____53238 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____53238 with
             | (bs1,t2) ->
                 let uu____53247 = patterns t2  in
                 (match uu____53247 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____53297 -> FStar_Pervasives_Native.None  in
      aux FStar_Pervasives_Native.None [] t  in
    let u_connectives =
      [(FStar_Parser_Const.true_lid, FStar_Parser_Const.c_true_lid,
         (Prims.parse_int "0"));
      (FStar_Parser_Const.false_lid, FStar_Parser_Const.c_false_lid,
        (Prims.parse_int "0"));
      (FStar_Parser_Const.and_lid, FStar_Parser_Const.c_and_lid,
        (Prims.parse_int "2"));
      (FStar_Parser_Const.or_lid, FStar_Parser_Const.c_or_lid,
        (Prims.parse_int "2"))]
       in
    let destruct_sq_base_conn t =
      let uu____53389 = un_squash t  in
      FStar_Util.bind_opt uu____53389
        (fun t1  ->
           let uu____53405 = head_and_args' t1  in
           match uu____53405 with
           | (hd1,args) ->
               let uu____53444 =
                 let uu____53450 =
                   let uu____53451 = un_uinst hd1  in
                   uu____53451.FStar_Syntax_Syntax.n  in
                 (uu____53450, (FStar_List.length args))  in
               (match uu____53444 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53467) when
                    (_53467 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53470) when
                    (_53470 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53473) when
                    (_53473 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53476) when
                    (_53476 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53479) when
                    (_53479 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53482) when
                    (_53482 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53485) when
                    (_53485 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53488) when
                    (_53488 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____53489 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____53519 = un_squash t  in
      FStar_Util.bind_opt uu____53519
        (fun t1  ->
           let uu____53534 = arrow_one t1  in
           match uu____53534 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____53549 =
                 let uu____53551 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____53551  in
               if uu____53549
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____53561 = comp_to_comp_typ_nouniv c  in
                    uu____53561.FStar_Syntax_Syntax.result_typ  in
                  let uu____53562 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____53562
                  then
                    let uu____53569 = patterns q  in
                    match uu____53569 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____53632 =
                       let uu____53633 =
                         let uu____53638 =
                           let uu____53639 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____53650 =
                             let uu____53661 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____53661]  in
                           uu____53639 :: uu____53650  in
                         (FStar_Parser_Const.imp_lid, uu____53638)  in
                       BaseConn uu____53633  in
                     FStar_Pervasives_Native.Some uu____53632))
           | uu____53694 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____53702 = un_squash t  in
      FStar_Util.bind_opt uu____53702
        (fun t1  ->
           let uu____53733 = head_and_args' t1  in
           match uu____53733 with
           | (hd1,args) ->
               let uu____53772 =
                 let uu____53787 =
                   let uu____53788 = un_uinst hd1  in
                   uu____53788.FStar_Syntax_Syntax.n  in
                 (uu____53787, args)  in
               (match uu____53772 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____53805)::(a2,uu____53807)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____53858 =
                      let uu____53859 = FStar_Syntax_Subst.compress a2  in
                      uu____53859.FStar_Syntax_Syntax.n  in
                    (match uu____53858 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____53866) ->
                         let uu____53901 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____53901 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____53954 -> failwith "impossible"  in
                              let uu____53962 = patterns q1  in
                              (match uu____53962 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____54023 -> FStar_Pervasives_Native.None)
                | uu____54024 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____54047 = destruct_sq_forall phi  in
          (match uu____54047 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _54057  -> FStar_Pervasives_Native.Some _54057)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____54064 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____54070 = destruct_sq_exists phi  in
          (match uu____54070 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _54080  -> FStar_Pervasives_Native.Some _54080)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____54087 -> f1)
      | uu____54090 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____54094 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____54094
      (fun uu____54099  ->
         let uu____54100 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____54100
           (fun uu____54105  ->
              let uu____54106 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____54106
                (fun uu____54111  ->
                   let uu____54112 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____54112
                     (fun uu____54117  ->
                        let uu____54118 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____54118
                          (fun uu____54122  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____54135 =
      let uu____54136 = FStar_Syntax_Subst.compress t  in
      uu____54136.FStar_Syntax_Syntax.n  in
    match uu____54135 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____54143) ->
        let uu____54178 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____54178 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____54212 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____54212
             then
               let uu____54219 =
                 let uu____54230 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____54230]  in
               mk_app t uu____54219
             else e1)
    | uu____54257 ->
        let uu____54258 =
          let uu____54269 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____54269]  in
        mk_app t uu____54258
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____54311 =
            let uu____54316 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____54316  in
          let uu____54317 =
            let uu____54318 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____54318  in
          let uu____54321 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____54311 a.FStar_Syntax_Syntax.action_univs uu____54317
            FStar_Parser_Const.effect_Tot_lid uu____54321 [] pos
           in
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
          FStar_Syntax_Syntax.sigattrs = []
        }
  
let (mk_reify :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reify_1 =
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify)
        FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
       in
    let uu____54347 =
      let uu____54354 =
        let uu____54355 =
          let uu____54372 =
            let uu____54383 = FStar_Syntax_Syntax.as_arg t  in [uu____54383]
             in
          (reify_1, uu____54372)  in
        FStar_Syntax_Syntax.Tm_app uu____54355  in
      FStar_Syntax_Syntax.mk uu____54354  in
    uu____54347 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____54435 =
        let uu____54442 =
          let uu____54443 =
            let uu____54444 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____54444  in
          FStar_Syntax_Syntax.Tm_constant uu____54443  in
        FStar_Syntax_Syntax.mk uu____54442  in
      uu____54435 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____54446 =
      let uu____54453 =
        let uu____54454 =
          let uu____54471 =
            let uu____54482 = FStar_Syntax_Syntax.as_arg t  in [uu____54482]
             in
          (reflect_, uu____54471)  in
        FStar_Syntax_Syntax.Tm_app uu____54454  in
      FStar_Syntax_Syntax.mk uu____54453  in
    uu____54446 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____54526 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____54551 = unfold_lazy i  in delta_qualifier uu____54551
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____54553 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____54554 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____54555 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____54578 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____54591 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____54592 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____54599 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____54600 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____54616) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____54621;
           FStar_Syntax_Syntax.index = uu____54622;
           FStar_Syntax_Syntax.sort = t2;_},uu____54624)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____54633) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____54639,uu____54640) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____54682) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____54707,t2,uu____54709) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____54734,t2) -> delta_qualifier t2
  
let rec (incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth) =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_constant_at_level i ->
        FStar_Syntax_Syntax.Delta_constant_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_equational_at_level i ->
        FStar_Syntax_Syntax.Delta_equational_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let (incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let uu____54773 = delta_qualifier t  in incr_delta_depth uu____54773
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____54781 =
      let uu____54782 = FStar_Syntax_Subst.compress t  in
      uu____54782.FStar_Syntax_Syntax.n  in
    match uu____54781 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____54787 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____54803 =
      let uu____54820 = unmeta e  in head_and_args uu____54820  in
    match uu____54803 with
    | (head1,args) ->
        let uu____54851 =
          let uu____54866 =
            let uu____54867 = un_uinst head1  in
            uu____54867.FStar_Syntax_Syntax.n  in
          (uu____54866, args)  in
        (match uu____54851 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____54885) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____54909::(hd1,uu____54911)::(tl1,uu____54913)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____54980 =
               let uu____54983 =
                 let uu____54986 = list_elements tl1  in
                 FStar_Util.must uu____54986  in
               hd1 :: uu____54983  in
             FStar_Pervasives_Native.Some uu____54980
         | uu____54995 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____55019 .
    ('Auu____55019 -> 'Auu____55019) ->
      'Auu____55019 Prims.list -> 'Auu____55019 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____55045 = f a  in [uu____55045]
      | x::xs -> let uu____55050 = apply_last f xs  in x :: uu____55050
  
let (dm4f_lid :
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident) =
  fun ed  ->
    fun name  ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname  in
      let p' =
        apply_last
          (fun s  ->
             Prims.op_Hat "_dm4f_" (Prims.op_Hat s (Prims.op_Hat "_" name)))
          p
         in
      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
  
let rec (mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term)
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____55105 =
            let uu____55112 =
              let uu____55113 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____55113  in
            FStar_Syntax_Syntax.mk uu____55112  in
          uu____55105 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____55127 =
            let uu____55132 =
              let uu____55133 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____55133
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____55132 args  in
          uu____55127 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____55147 =
            let uu____55152 =
              let uu____55153 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____55153
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____55152 args  in
          uu____55147 FStar_Pervasives_Native.None pos  in
        let uu____55154 =
          let uu____55155 =
            let uu____55156 = FStar_Syntax_Syntax.iarg typ  in [uu____55156]
             in
          nil uu____55155 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____55190 =
                 let uu____55191 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____55200 =
                   let uu____55211 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____55220 =
                     let uu____55231 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____55231]  in
                   uu____55211 :: uu____55220  in
                 uu____55191 :: uu____55200  in
               cons1 uu____55190 t.FStar_Syntax_Syntax.pos) l uu____55154
  
let rec eqlist :
  'a .
    ('a -> 'a -> Prims.bool) -> 'a Prims.list -> 'a Prims.list -> Prims.bool
  =
  fun eq1  ->
    fun xs  ->
      fun ys  ->
        match (xs, ys) with
        | ([],[]) -> true
        | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
        | uu____55340 -> false
  
let eqsum :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) ->
        ('a,'b) FStar_Util.either -> ('a,'b) FStar_Util.either -> Prims.bool
  =
  fun e1  ->
    fun e2  ->
      fun x  ->
        fun y  ->
          match (x, y) with
          | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
          | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
          | uu____55454 -> false
  
let eqprod :
  'a 'b .
    ('a -> 'a -> Prims.bool) ->
      ('b -> 'b -> Prims.bool) -> ('a * 'b) -> ('a * 'b) -> Prims.bool
  =
  fun e1  ->
    fun e2  ->
      fun x  ->
        fun y  ->
          match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
  
let eqopt :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a FStar_Pervasives_Native.option ->
        'a FStar_Pervasives_Native.option -> Prims.bool
  =
  fun e  ->
    fun x  ->
      fun y  ->
        match (x, y) with
        | (FStar_Pervasives_Native.Some x1,FStar_Pervasives_Native.Some y1)
            -> e x1 y1
        | uu____55620 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____55658 = FStar_ST.op_Bang debug_term_eq  in
          if uu____55658
          then FStar_Util.print1 ">>> term_eq failing: %s\n" msg
          else ());
         false)
  
let (fail : Prims.string -> Prims.bool) = fun msg  -> check msg false 
let rec (term_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun dbg  ->
    fun t1  ->
      fun t2  ->
        let t11 = let uu____55880 = unmeta_safe t1  in canon_app uu____55880
           in
        let t21 = let uu____55886 = unmeta_safe t2  in canon_app uu____55886
           in
        let uu____55889 =
          let uu____55894 =
            let uu____55895 =
              let uu____55898 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____55898  in
            uu____55895.FStar_Syntax_Syntax.n  in
          let uu____55899 =
            let uu____55900 =
              let uu____55903 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____55903  in
            uu____55900.FStar_Syntax_Syntax.n  in
          (uu____55894, uu____55899)  in
        match uu____55889 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____55905,uu____55906) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____55915,FStar_Syntax_Syntax.Tm_uinst uu____55916) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____55925,uu____55926) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____55951,FStar_Syntax_Syntax.Tm_delayed uu____55952) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____55977,uu____55978) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____56007,FStar_Syntax_Syntax.Tm_ascribed uu____56008) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____56047 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____56047
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____56052 = FStar_Const.eq_const c1 c2  in
            check "const" uu____56052
        | (FStar_Syntax_Syntax.Tm_type
           uu____56055,FStar_Syntax_Syntax.Tm_type uu____56056) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____56114 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____56114) &&
              (let uu____56124 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____56124)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____56173 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____56173) &&
              (let uu____56183 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____56183)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____56201 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____56201)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____56258 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____56258) &&
              (let uu____56262 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____56262)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____56351 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____56351) &&
              (let uu____56355 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____56355)
        | (FStar_Syntax_Syntax.Tm_lazy uu____56372,uu____56373) ->
            let uu____56374 =
              let uu____56376 = unlazy t11  in
              term_eq_dbg dbg uu____56376 t21  in
            check "lazy_l" uu____56374
        | (uu____56378,FStar_Syntax_Syntax.Tm_lazy uu____56379) ->
            let uu____56380 =
              let uu____56382 = unlazy t21  in
              term_eq_dbg dbg t11 uu____56382  in
            check "lazy_r" uu____56380
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____56427 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____56427))
              &&
              (let uu____56431 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____56431)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____56435),FStar_Syntax_Syntax.Tm_uvar (u2,uu____56437)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____56495 =
               let uu____56497 = eq_quoteinfo qi1 qi2  in uu____56497 = Equal
                in
             check "tm_quoted qi" uu____56495) &&
              (let uu____56500 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____56500)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____56530 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____56530) &&
                   (let uu____56534 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____56534)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____56553 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____56553) &&
                    (let uu____56557 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____56557))
                   &&
                   (let uu____56561 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____56561)
             | uu____56564 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____56570) -> fail "unk"
        | (uu____56572,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____56574,uu____56575) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____56577,uu____56578) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____56580,uu____56581) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____56583,uu____56584) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____56586,uu____56587) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____56589,uu____56590) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____56610,uu____56611) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____56627,uu____56628) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____56636,uu____56637) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____56655,uu____56656) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____56680,uu____56681) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____56696,uu____56697) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____56711,uu____56712) ->
            fail "bottom"
        | (uu____56720,FStar_Syntax_Syntax.Tm_bvar uu____56721) ->
            fail "bottom"
        | (uu____56723,FStar_Syntax_Syntax.Tm_name uu____56724) ->
            fail "bottom"
        | (uu____56726,FStar_Syntax_Syntax.Tm_fvar uu____56727) ->
            fail "bottom"
        | (uu____56729,FStar_Syntax_Syntax.Tm_constant uu____56730) ->
            fail "bottom"
        | (uu____56732,FStar_Syntax_Syntax.Tm_type uu____56733) ->
            fail "bottom"
        | (uu____56735,FStar_Syntax_Syntax.Tm_abs uu____56736) ->
            fail "bottom"
        | (uu____56756,FStar_Syntax_Syntax.Tm_arrow uu____56757) ->
            fail "bottom"
        | (uu____56773,FStar_Syntax_Syntax.Tm_refine uu____56774) ->
            fail "bottom"
        | (uu____56782,FStar_Syntax_Syntax.Tm_app uu____56783) ->
            fail "bottom"
        | (uu____56801,FStar_Syntax_Syntax.Tm_match uu____56802) ->
            fail "bottom"
        | (uu____56826,FStar_Syntax_Syntax.Tm_let uu____56827) ->
            fail "bottom"
        | (uu____56842,FStar_Syntax_Syntax.Tm_uvar uu____56843) ->
            fail "bottom"
        | (uu____56857,FStar_Syntax_Syntax.Tm_meta uu____56858) ->
            fail "bottom"

and (arg_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) ->
        Prims.bool)
  =
  fun dbg  ->
    fun a1  ->
      fun a2  ->
        eqprod
          (fun t1  ->
             fun t2  ->
               let uu____56893 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____56893)
          (fun q1  ->
             fun q2  ->
               let uu____56905 =
                 let uu____56907 = eq_aqual q1 q2  in uu____56907 = Equal  in
               check "arg qual" uu____56905) a1 a2

and (binder_eq_dbg :
  Prims.bool ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) -> Prims.bool)
  =
  fun dbg  ->
    fun b1  ->
      fun b2  ->
        eqprod
          (fun b11  ->
             fun b21  ->
               let uu____56932 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____56932)
          (fun q1  ->
             fun q2  ->
               let uu____56944 =
                 let uu____56946 = eq_aqual q1 q2  in uu____56946 = Equal  in
               check "binder qual" uu____56944) b1 b2

and (lcomp_eq_dbg :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c1  -> fun c2  -> fail "lcomp"

and (residual_eq_dbg :
  FStar_Syntax_Syntax.residual_comp ->
    FStar_Syntax_Syntax.residual_comp -> Prims.bool)
  = fun r1  -> fun r2  -> fail "residual"

and (comp_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool)
  =
  fun dbg  ->
    fun c1  ->
      fun c2  ->
        let c11 = comp_to_comp_typ_nouniv c1  in
        let c21 = comp_to_comp_typ_nouniv c2  in
        ((let uu____56966 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____56966) &&
           (let uu____56970 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____56970))
          && true

and (eq_flags_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.cflag -> FStar_Syntax_Syntax.cflag -> Prims.bool)
  = fun dbg  -> fun f1  -> fun f2  -> true

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
  fun dbg  ->
    fun uu____56980  ->
      fun uu____56981  ->
        match (uu____56980, uu____56981) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____57108 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____57108) &&
               (let uu____57112 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____57112))
              &&
              (let uu____57116 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____57158 -> false  in
               check "branch when" uu____57116)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____57179 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____57179) &&
           (let uu____57188 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____57188))
          &&
          (let uu____57192 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____57192)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____57209 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____57209 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____57263 ->
        let uu____57286 =
          let uu____57288 = FStar_Syntax_Subst.compress t  in
          sizeof uu____57288  in
        (Prims.parse_int "1") + uu____57286
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____57291 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____57291
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____57295 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____57295
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____57304 = sizeof t1  in (FStar_List.length us) + uu____57304
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____57308) ->
        let uu____57333 = sizeof t1  in
        let uu____57335 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____57350  ->
                 match uu____57350 with
                 | (bv,uu____57360) ->
                     let uu____57365 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____57365) (Prims.parse_int "0") bs
           in
        uu____57333 + uu____57335
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____57394 = sizeof hd1  in
        let uu____57396 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____57411  ->
                 match uu____57411 with
                 | (arg,uu____57421) ->
                     let uu____57426 = sizeof arg  in acc + uu____57426)
            (Prims.parse_int "0") args
           in
        uu____57394 + uu____57396
    | uu____57429 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____57443 =
        let uu____57444 = un_uinst t  in uu____57444.FStar_Syntax_Syntax.n
         in
      match uu____57443 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____57449 -> false
  
let (is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  -> is_fvar FStar_Parser_Const.synth_lid t 
let (has_attribute :
  FStar_Syntax_Syntax.attribute Prims.list ->
    FStar_Ident.lident -> Prims.bool)
  = fun attrs  -> fun attr  -> FStar_Util.for_some (is_fvar attr) attrs 
let (process_pragma :
  FStar_Syntax_Syntax.pragma -> FStar_Range.range -> unit) =
  fun p  ->
    fun r  ->
      let set_options1 t s =
        let uu____57498 = FStar_Options.set_options t s  in
        match uu____57498 with
        | FStar_Getopt.Success  -> ()
        | FStar_Getopt.Help  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Failed to process pragma: use 'fstar --help' to see which options are available")
              r
        | FStar_Getopt.Error s1 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                (Prims.op_Hat "Failed to process pragma: " s1)) r
         in
      match p with
      | FStar_Syntax_Syntax.LightOff  ->
          if p = FStar_Syntax_Syntax.LightOff
          then FStar_Options.set_ml_ish ()
          else ()
      | FStar_Syntax_Syntax.SetOptions o -> set_options1 FStar_Options.Set o
      | FStar_Syntax_Syntax.ResetOptions sopt ->
          ((let uu____57515 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____57515 (fun a1  -> ()));
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
      | FStar_Syntax_Syntax.PushOptions sopt ->
          (FStar_Options.internal_push ();
           (match sopt with
            | FStar_Pervasives_Native.None  -> ()
            | FStar_Pervasives_Native.Some s ->
                set_options1 FStar_Options.Reset s))
      | FStar_Syntax_Syntax.PopOptions  ->
          let uu____57530 = FStar_Options.internal_pop ()  in
          if uu____57530
          then ()
          else
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FailToProcessPragma,
                "Cannot #pop-options, stack would become empty") r
  
let rec (unbound_variables :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun tm  ->
    let t = FStar_Syntax_Subst.compress tm  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____57562 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____57589 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____57604 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____57605 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____57606 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____57615) ->
        let uu____57640 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____57640 with
         | (bs1,t2) ->
             let uu____57649 =
               FStar_List.collect
                 (fun uu____57661  ->
                    match uu____57661 with
                    | (b,uu____57671) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____57676 = unbound_variables t2  in
             FStar_List.append uu____57649 uu____57676)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____57701 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____57701 with
         | (bs1,c1) ->
             let uu____57710 =
               FStar_List.collect
                 (fun uu____57722  ->
                    match uu____57722 with
                    | (b,uu____57732) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____57737 = unbound_variables_comp c1  in
             FStar_List.append uu____57710 uu____57737)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____57746 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____57746 with
         | (bs,t2) ->
             let uu____57769 =
               FStar_List.collect
                 (fun uu____57781  ->
                    match uu____57781 with
                    | (b1,uu____57791) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____57796 = unbound_variables t2  in
             FStar_List.append uu____57769 uu____57796)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____57825 =
          FStar_List.collect
            (fun uu____57839  ->
               match uu____57839 with
               | (x,uu____57851) -> unbound_variables x) args
           in
        let uu____57860 = unbound_variables t1  in
        FStar_List.append uu____57825 uu____57860
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____57901 = unbound_variables t1  in
        let uu____57904 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____57919 = FStar_Syntax_Subst.open_branch br  in
                  match uu____57919 with
                  | (p,wopt,t2) ->
                      let uu____57941 = unbound_variables t2  in
                      let uu____57944 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____57941 uu____57944))
           in
        FStar_List.append uu____57901 uu____57904
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____57958) ->
        let uu____57999 = unbound_variables t1  in
        let uu____58002 =
          let uu____58005 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____58036 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____58005 uu____58036  in
        FStar_List.append uu____57999 uu____58002
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____58077 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____58080 =
          let uu____58083 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____58086 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____58091 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____58093 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____58093 with
                 | (uu____58114,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____58083 uu____58086  in
        FStar_List.append uu____58077 uu____58080
    | FStar_Syntax_Syntax.Tm_let ((uu____58116,lbs),t1) ->
        let uu____58136 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____58136 with
         | (lbs1,t2) ->
             let uu____58151 = unbound_variables t2  in
             let uu____58154 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____58161 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____58164 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____58161 uu____58164) lbs1
                in
             FStar_List.append uu____58151 uu____58154)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____58181 = unbound_variables t1  in
        let uu____58184 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____58223  ->
                      match uu____58223 with
                      | (a,uu____58235) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____58244,uu____58245,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____58251,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____58257 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____58266 -> []
          | FStar_Syntax_Syntax.Meta_named uu____58267 -> []  in
        FStar_List.append uu____58181 uu____58184

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____58274) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____58284) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____58294 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____58297 =
          FStar_List.collect
            (fun uu____58311  ->
               match uu____58311 with
               | (a,uu____58323) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____58294 uu____58297

let (extract_attr' :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.term Prims.list ->
      (FStar_Syntax_Syntax.term Prims.list * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid  ->
    fun attrs  ->
      let rec aux acc attrs1 =
        match attrs1 with
        | [] -> FStar_Pervasives_Native.None
        | h::t ->
            let uu____58438 = head_and_args h  in
            (match uu____58438 with
             | (head1,args) ->
                 let uu____58499 =
                   let uu____58500 = FStar_Syntax_Subst.compress head1  in
                   uu____58500.FStar_Syntax_Syntax.n  in
                 (match uu____58499 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____58553 -> aux (h :: acc) t))
         in
      aux [] attrs
  
let (extract_attr :
  FStar_Ident.lid ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.args)
        FStar_Pervasives_Native.option)
  =
  fun attr_lid  ->
    fun se  ->
      let uu____58577 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____58577 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2985_58619 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2985_58619.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2985_58619.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2985_58619.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2985_58619.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  