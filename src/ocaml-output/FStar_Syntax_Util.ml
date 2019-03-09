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
                (fun uu___409_42849  ->
                   match uu___409_42849 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____42852 -> false)))
    | uu____42854 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____42871) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____42881) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____42910 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____42919 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___801_42931 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___801_42931.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___801_42931.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___801_42931.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___801_42931.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____42945  ->
           let uu____42946 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____42946 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_42964  ->
            match uu___410_42964 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____42968 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____42976 -> []
    | FStar_Syntax_Syntax.GTotal uu____42993 -> []
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
    | uu____43037 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____43047,uu____43048) ->
        unascribe e2
    | uu____43089 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____43142,uu____43143) ->
          ascribe t' k
      | uu____43184 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____43211 =
      let uu____43220 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____43220  in
    uu____43211 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____43276 =
      let uu____43277 = FStar_Syntax_Subst.compress t  in
      uu____43277.FStar_Syntax_Syntax.n  in
    match uu____43276 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____43281 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____43281
    | uu____43282 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____43289 =
      let uu____43290 = FStar_Syntax_Subst.compress t  in
      uu____43290.FStar_Syntax_Syntax.n  in
    match uu____43289 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____43294 ->
             let uu____43303 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____43303
         | uu____43304 -> t)
    | uu____43305 -> t
  
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
      | uu____43329 -> false
  
let rec unlazy_as_t :
  'Auu____43342 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____43342
  =
  fun k  ->
    fun t  ->
      let uu____43353 =
        let uu____43354 = FStar_Syntax_Subst.compress t  in
        uu____43354.FStar_Syntax_Syntax.n  in
      match uu____43353 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____43359;
            FStar_Syntax_Syntax.rng = uu____43360;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____43363 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____43404 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____43404;
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
    let uu____43417 =
      let uu____43432 = unascribe t  in head_and_args' uu____43432  in
    match uu____43417 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____43466 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____43477 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____43488 -> false
  
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
      | (NotEqual ,uu____43538) -> NotEqual
      | (uu____43539,NotEqual ) -> NotEqual
      | (Unknown ,uu____43540) -> Unknown
      | (uu____43541,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_43662 = if uu___411_43662 then Equal else Unknown
         in
      let equal_iff uu___412_43673 =
        if uu___412_43673 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____43694 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____43716 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____43716
        then
          let uu____43720 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____43797  ->
                    match uu____43797 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____43838 = eq_tm a1 a2  in
                        eq_inj acc uu____43838) Equal) uu____43720
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____43852 =
          let uu____43869 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____43869 head_and_args  in
        match uu____43852 with
        | (head1,args1) ->
            let uu____43922 =
              let uu____43939 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____43939 head_and_args  in
            (match uu____43922 with
             | (head2,args2) ->
                 let uu____43992 =
                   let uu____43997 =
                     let uu____43998 = un_uinst head1  in
                     uu____43998.FStar_Syntax_Syntax.n  in
                   let uu____44001 =
                     let uu____44002 = un_uinst head2  in
                     uu____44002.FStar_Syntax_Syntax.n  in
                   (uu____43997, uu____44001)  in
                 (match uu____43992 with
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
                  | uu____44029 -> FStar_Pervasives_Native.None))
         in
      let uu____44042 =
        let uu____44047 =
          let uu____44048 = unmeta t11  in uu____44048.FStar_Syntax_Syntax.n
           in
        let uu____44051 =
          let uu____44052 = unmeta t21  in uu____44052.FStar_Syntax_Syntax.n
           in
        (uu____44047, uu____44051)  in
      match uu____44042 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____44058,uu____44059) ->
          let uu____44060 = unlazy t11  in eq_tm uu____44060 t21
      | (uu____44061,FStar_Syntax_Syntax.Tm_lazy uu____44062) ->
          let uu____44063 = unlazy t21  in eq_tm t11 uu____44063
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____44066 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____44090 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____44090
            (fun uu____44138  ->
               match uu____44138 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____44153 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____44153
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____44167 = eq_tm f g  in
          eq_and uu____44167
            (fun uu____44170  ->
               let uu____44171 = eq_univs_list us vs  in equal_if uu____44171)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____44173),uu____44174) -> Unknown
      | (uu____44175,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____44176)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____44179 = FStar_Const.eq_const c d  in
          equal_iff uu____44179
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____44182)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____44184))) ->
          let uu____44213 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____44213
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____44267 =
            let uu____44272 =
              let uu____44273 = un_uinst h1  in
              uu____44273.FStar_Syntax_Syntax.n  in
            let uu____44276 =
              let uu____44277 = un_uinst h2  in
              uu____44277.FStar_Syntax_Syntax.n  in
            (uu____44272, uu____44276)  in
          (match uu____44267 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____44283 =
                    let uu____44285 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____44285  in
                  FStar_List.mem uu____44283 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____44287 ->
               let uu____44292 = eq_tm h1 h2  in
               eq_and uu____44292 (fun uu____44294  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____44400 = FStar_List.zip bs1 bs2  in
            let uu____44463 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____44500  ->
                 fun a  ->
                   match uu____44500 with
                   | (b1,b2) ->
                       eq_and a (fun uu____44593  -> branch_matches b1 b2))
              uu____44400 uu____44463
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____44598 = eq_univs u v1  in equal_if uu____44598
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____44612 = eq_quoteinfo q1 q2  in
          eq_and uu____44612 (fun uu____44614  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____44627 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____44627 (fun uu____44629  -> eq_tm phi1 phi2)
      | uu____44630 -> Unknown

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
      | ([],uu____44702) -> NotEqual
      | (uu____44733,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____44825 = eq_tm t1 t2  in
             match uu____44825 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____44826 = eq_antiquotes a11 a21  in
                 (match uu____44826 with
                  | NotEqual  -> NotEqual
                  | uu____44827 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____44842) -> NotEqual
      | (uu____44849,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____44879 -> NotEqual

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
        | (uu____44971,uu____44972) -> false  in
      let uu____44982 = b1  in
      match uu____44982 with
      | (p1,w1,t1) ->
          let uu____45016 = b2  in
          (match uu____45016 with
           | (p2,w2,t2) ->
               let uu____45050 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____45050
               then
                 let uu____45053 =
                   (let uu____45057 = eq_tm t1 t2  in uu____45057 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____45066 = eq_tm t11 t21  in
                             uu____45066 = Equal) w1 w2)
                    in
                 (if uu____45053 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____45131)::a11,(b,uu____45134)::b1) ->
          let uu____45208 = eq_tm a b  in
          (match uu____45208 with
           | Equal  -> eq_args a11 b1
           | uu____45209 -> Unknown)
      | uu____45210 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____45246) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____45252,uu____45253) ->
        unrefine t2
    | uu____45294 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45302 =
      let uu____45303 = FStar_Syntax_Subst.compress t  in
      uu____45303.FStar_Syntax_Syntax.n  in
    match uu____45302 with
    | FStar_Syntax_Syntax.Tm_uvar uu____45307 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____45322) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____45327 ->
        let uu____45344 =
          let uu____45345 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____45345 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____45344 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____45408,uu____45409) ->
        is_uvar t1
    | uu____45450 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45459 =
      let uu____45460 = unrefine t  in uu____45460.FStar_Syntax_Syntax.n  in
    match uu____45459 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____45466) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____45492) -> is_unit t1
    | uu____45497 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45506 =
      let uu____45507 = FStar_Syntax_Subst.compress t  in
      uu____45507.FStar_Syntax_Syntax.n  in
    match uu____45506 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____45512 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45521 =
      let uu____45522 = unrefine t  in uu____45522.FStar_Syntax_Syntax.n  in
    match uu____45521 with
    | FStar_Syntax_Syntax.Tm_type uu____45526 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____45530) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____45556) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____45561,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____45583 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____45592 =
      let uu____45593 = FStar_Syntax_Subst.compress e  in
      uu____45593.FStar_Syntax_Syntax.n  in
    match uu____45592 with
    | FStar_Syntax_Syntax.Tm_abs uu____45597 -> true
    | uu____45617 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45626 =
      let uu____45627 = FStar_Syntax_Subst.compress t  in
      uu____45627.FStar_Syntax_Syntax.n  in
    match uu____45626 with
    | FStar_Syntax_Syntax.Tm_arrow uu____45631 -> true
    | uu____45647 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____45657) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____45663,uu____45664) ->
        pre_typ t2
    | uu____45705 -> t1
  
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
      let uu____45730 =
        let uu____45731 = un_uinst typ1  in uu____45731.FStar_Syntax_Syntax.n
         in
      match uu____45730 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____45796 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____45826 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____45847,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____45854) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____45859,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____45870,uu____45871,uu____45872,uu____45873,uu____45874) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____45884,uu____45885,uu____45886,uu____45887) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____45893,uu____45894,uu____45895,uu____45896,uu____45897) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____45905,uu____45906) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____45908,uu____45909) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____45912 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____45913 -> []
    | FStar_Syntax_Syntax.Sig_main uu____45914 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____45928 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_45954  ->
    match uu___413_45954 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____45968 'Auu____45969 .
    ('Auu____45968 FStar_Syntax_Syntax.syntax * 'Auu____45969) ->
      FStar_Range.range
  =
  fun uu____45980  ->
    match uu____45980 with | (hd1,uu____45988) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____46002 'Auu____46003 .
    ('Auu____46002 FStar_Syntax_Syntax.syntax * 'Auu____46003) Prims.list ->
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
      | uu____46101 ->
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
      let uu____46160 =
        FStar_List.map
          (fun uu____46187  ->
             match uu____46187 with
             | (bv,aq) ->
                 let uu____46206 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____46206, aq)) bs
         in
      mk_app f uu____46160
  
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
          let uu____46256 = FStar_Ident.range_of_lid l  in
          let uu____46257 =
            let uu____46266 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____46266  in
          uu____46257 FStar_Pervasives_Native.None uu____46256
      | uu____46271 ->
          let e =
            let uu____46285 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____46285 args  in
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
          let uu____46362 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____46362
          then
            let uu____46365 =
              let uu____46371 =
                let uu____46373 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____46373  in
              let uu____46376 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____46371, uu____46376)  in
            FStar_Ident.mk_ident uu____46365
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1395_46381 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1395_46381.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1395_46381.FStar_Syntax_Syntax.sort)
          }  in
        let uu____46382 = mk_field_projector_name_from_ident lid nm  in
        (uu____46382, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____46394) -> ses
    | uu____46403 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____46414 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____46427 = FStar_Syntax_Unionfind.find uv  in
      match uu____46427 with
      | FStar_Pervasives_Native.Some uu____46430 ->
          let uu____46431 =
            let uu____46433 =
              let uu____46435 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____46435  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____46433  in
          failwith uu____46431
      | uu____46440 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____46523 -> q1 = q2
  
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
              let uu____46569 =
                let uu___1456_46570 = rc  in
                let uu____46571 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1456_46570.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____46571;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1456_46570.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____46569
           in
        match bs with
        | [] -> t
        | uu____46588 ->
            let body =
              let uu____46590 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____46590  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____46620 =
                   let uu____46627 =
                     let uu____46628 =
                       let uu____46647 =
                         let uu____46656 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____46656 bs'  in
                       let uu____46671 = close_lopt lopt'  in
                       (uu____46647, t1, uu____46671)  in
                     FStar_Syntax_Syntax.Tm_abs uu____46628  in
                   FStar_Syntax_Syntax.mk uu____46627  in
                 uu____46620 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____46686 ->
                 let uu____46687 =
                   let uu____46694 =
                     let uu____46695 =
                       let uu____46714 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____46723 = close_lopt lopt  in
                       (uu____46714, body, uu____46723)  in
                     FStar_Syntax_Syntax.Tm_abs uu____46695  in
                   FStar_Syntax_Syntax.mk uu____46694  in
                 uu____46687 FStar_Pervasives_Native.None
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
      | uu____46779 ->
          let uu____46788 =
            let uu____46795 =
              let uu____46796 =
                let uu____46811 = FStar_Syntax_Subst.close_binders bs  in
                let uu____46820 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____46811, uu____46820)  in
              FStar_Syntax_Syntax.Tm_arrow uu____46796  in
            FStar_Syntax_Syntax.mk uu____46795  in
          uu____46788 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____46869 =
        let uu____46870 = FStar_Syntax_Subst.compress t  in
        uu____46870.FStar_Syntax_Syntax.n  in
      match uu____46869 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____46900) ->
               let uu____46909 =
                 let uu____46910 = FStar_Syntax_Subst.compress tres  in
                 uu____46910.FStar_Syntax_Syntax.n  in
               (match uu____46909 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____46953 -> t)
           | uu____46954 -> t)
      | uu____46955 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____46973 =
        let uu____46974 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____46974 t.FStar_Syntax_Syntax.pos  in
      let uu____46975 =
        let uu____46982 =
          let uu____46983 =
            let uu____46990 =
              let uu____46993 =
                let uu____46994 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____46994]  in
              FStar_Syntax_Subst.close uu____46993 t  in
            (b, uu____46990)  in
          FStar_Syntax_Syntax.Tm_refine uu____46983  in
        FStar_Syntax_Syntax.mk uu____46982  in
      uu____46975 FStar_Pervasives_Native.None uu____46973
  
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
        let uu____47074 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____47074 with
         | (bs1,c1) ->
             let uu____47093 = is_total_comp c1  in
             if uu____47093
             then
               let uu____47108 = arrow_formals_comp (comp_result c1)  in
               (match uu____47108 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____47175;
           FStar_Syntax_Syntax.index = uu____47176;
           FStar_Syntax_Syntax.sort = s;_},uu____47178)
        ->
        let rec aux s1 k2 =
          let uu____47209 =
            let uu____47210 = FStar_Syntax_Subst.compress s1  in
            uu____47210.FStar_Syntax_Syntax.n  in
          match uu____47209 with
          | FStar_Syntax_Syntax.Tm_arrow uu____47225 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____47240;
                 FStar_Syntax_Syntax.index = uu____47241;
                 FStar_Syntax_Syntax.sort = s2;_},uu____47243)
              -> aux s2 k2
          | uu____47251 ->
              let uu____47252 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____47252)
           in
        aux s k1
    | uu____47267 ->
        let uu____47268 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____47268)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____47303 = arrow_formals_comp k  in
    match uu____47303 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____47445 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____47445 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____47469 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_47478  ->
                         match uu___414_47478 with
                         | FStar_Syntax_Syntax.DECREASES uu____47480 -> true
                         | uu____47484 -> false))
                  in
               (match uu____47469 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____47519 ->
                    let uu____47522 = is_total_comp c1  in
                    if uu____47522
                    then
                      let uu____47541 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____47541 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____47634;
             FStar_Syntax_Syntax.index = uu____47635;
             FStar_Syntax_Syntax.sort = k2;_},uu____47637)
          -> arrow_until_decreases k2
      | uu____47645 -> ([], FStar_Pervasives_Native.None)  in
    let uu____47666 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____47666 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____47720 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____47741 =
                 FStar_Common.tabulate n_univs (fun uu____47747  -> false)
                  in
               let uu____47750 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____47775  ->
                         match uu____47775 with
                         | (x,uu____47784) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____47741 uu____47750)
           in
        ((n_univs + (FStar_List.length bs)), uu____47720)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____47840 =
            let uu___1578_47841 = rc  in
            let uu____47842 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1578_47841.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____47842;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1578_47841.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____47840
      | uu____47851 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____47885 =
        let uu____47886 =
          let uu____47889 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____47889  in
        uu____47886.FStar_Syntax_Syntax.n  in
      match uu____47885 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____47935 = aux t2 what  in
          (match uu____47935 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____48007 -> ([], t1, abs_body_lcomp)  in
    let uu____48024 = aux t FStar_Pervasives_Native.None  in
    match uu____48024 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____48072 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____48072 with
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
                    | (FStar_Pervasives_Native.None ,uu____48235) -> def
                    | (uu____48246,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____48258) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _48274  ->
                                  FStar_Syntax_Syntax.U_name _48274))
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
            let uu____48356 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____48356 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____48391 ->
            let t' = arrow binders c  in
            let uu____48403 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____48403 with
             | (uvs1,t'1) ->
                 let uu____48424 =
                   let uu____48425 = FStar_Syntax_Subst.compress t'1  in
                   uu____48425.FStar_Syntax_Syntax.n  in
                 (match uu____48424 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____48474 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____48499 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____48510 -> false
  
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
      let uu____48573 =
        let uu____48574 = pre_typ t  in uu____48574.FStar_Syntax_Syntax.n  in
      match uu____48573 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____48579 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____48593 =
        let uu____48594 = pre_typ t  in uu____48594.FStar_Syntax_Syntax.n  in
      match uu____48593 with
      | FStar_Syntax_Syntax.Tm_fvar uu____48598 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____48600) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____48626) ->
          is_constructed_typ t1 lid
      | uu____48631 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____48644 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____48645 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____48646 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____48648) -> get_tycon t2
    | uu____48673 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____48681 =
      let uu____48682 = un_uinst t  in uu____48682.FStar_Syntax_Syntax.n  in
    match uu____48681 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____48687 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____48701 =
        let uu____48705 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____48705  in
      match uu____48701 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____48737 -> false
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
  fun uu____48756  ->
    let u =
      let uu____48762 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _48779  -> FStar_Syntax_Syntax.U_unif _48779)
        uu____48762
       in
    let uu____48780 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____48780, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____48793 = eq_tm a a'  in
      match uu____48793 with | Equal  -> true | uu____48796 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____48801 =
    let uu____48808 =
      let uu____48809 =
        let uu____48810 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____48810
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____48809  in
    FStar_Syntax_Syntax.mk uu____48808  in
  uu____48801 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____48922 =
            let uu____48925 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____48926 =
              let uu____48933 =
                let uu____48934 =
                  let uu____48951 =
                    let uu____48962 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____48971 =
                      let uu____48982 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____48982]  in
                    uu____48962 :: uu____48971  in
                  (tand, uu____48951)  in
                FStar_Syntax_Syntax.Tm_app uu____48934  in
              FStar_Syntax_Syntax.mk uu____48933  in
            uu____48926 FStar_Pervasives_Native.None uu____48925  in
          FStar_Pervasives_Native.Some uu____48922
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____49059 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____49060 =
          let uu____49067 =
            let uu____49068 =
              let uu____49085 =
                let uu____49096 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____49105 =
                  let uu____49116 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____49116]  in
                uu____49096 :: uu____49105  in
              (op_t, uu____49085)  in
            FStar_Syntax_Syntax.Tm_app uu____49068  in
          FStar_Syntax_Syntax.mk uu____49067  in
        uu____49060 FStar_Pervasives_Native.None uu____49059
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____49173 =
      let uu____49180 =
        let uu____49181 =
          let uu____49198 =
            let uu____49209 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____49209]  in
          (t_not, uu____49198)  in
        FStar_Syntax_Syntax.Tm_app uu____49181  in
      FStar_Syntax_Syntax.mk uu____49180  in
    uu____49173 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____49406 =
      let uu____49413 =
        let uu____49414 =
          let uu____49431 =
            let uu____49442 = FStar_Syntax_Syntax.as_arg e  in [uu____49442]
             in
          (b2t_v, uu____49431)  in
        FStar_Syntax_Syntax.Tm_app uu____49414  in
      FStar_Syntax_Syntax.mk uu____49413  in
    uu____49406 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49486 =
      let uu____49487 = unmeta t  in uu____49487.FStar_Syntax_Syntax.n  in
    match uu____49486 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____49492 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____49515 = is_t_true t1  in
      if uu____49515
      then t2
      else
        (let uu____49522 = is_t_true t2  in
         if uu____49522 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____49550 = is_t_true t1  in
      if uu____49550
      then t_true
      else
        (let uu____49557 = is_t_true t2  in
         if uu____49557 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____49586 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____49587 =
        let uu____49594 =
          let uu____49595 =
            let uu____49612 =
              let uu____49623 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____49632 =
                let uu____49643 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____49643]  in
              uu____49623 :: uu____49632  in
            (teq, uu____49612)  in
          FStar_Syntax_Syntax.Tm_app uu____49595  in
        FStar_Syntax_Syntax.mk uu____49594  in
      uu____49587 FStar_Pervasives_Native.None uu____49586
  
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
          let uu____49710 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____49711 =
            let uu____49718 =
              let uu____49719 =
                let uu____49736 =
                  let uu____49747 = FStar_Syntax_Syntax.iarg t  in
                  let uu____49756 =
                    let uu____49767 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____49776 =
                      let uu____49787 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____49787]  in
                    uu____49767 :: uu____49776  in
                  uu____49747 :: uu____49756  in
                (eq_inst, uu____49736)  in
              FStar_Syntax_Syntax.Tm_app uu____49719  in
            FStar_Syntax_Syntax.mk uu____49718  in
          uu____49711 FStar_Pervasives_Native.None uu____49710
  
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
        let uu____49864 =
          let uu____49871 =
            let uu____49872 =
              let uu____49889 =
                let uu____49900 = FStar_Syntax_Syntax.iarg t  in
                let uu____49909 =
                  let uu____49920 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____49929 =
                    let uu____49940 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____49940]  in
                  uu____49920 :: uu____49929  in
                uu____49900 :: uu____49909  in
              (t_has_type1, uu____49889)  in
            FStar_Syntax_Syntax.Tm_app uu____49872  in
          FStar_Syntax_Syntax.mk uu____49871  in
        uu____49864 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____50017 =
          let uu____50024 =
            let uu____50025 =
              let uu____50042 =
                let uu____50053 = FStar_Syntax_Syntax.iarg t  in
                let uu____50062 =
                  let uu____50073 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____50073]  in
                uu____50053 :: uu____50062  in
              (t_with_type1, uu____50042)  in
            FStar_Syntax_Syntax.Tm_app uu____50025  in
          FStar_Syntax_Syntax.mk uu____50024  in
        uu____50017 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____50120 =
    let uu____50127 =
      let uu____50128 =
        let uu____50135 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____50135, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____50128  in
    FStar_Syntax_Syntax.mk uu____50127  in
  uu____50120 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____50150 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____50163 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____50174 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____50150 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____50195  -> c0)
  
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
        let uu____50278 =
          let uu____50285 =
            let uu____50286 =
              let uu____50303 =
                let uu____50314 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____50323 =
                  let uu____50334 =
                    let uu____50343 =
                      let uu____50344 =
                        let uu____50345 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____50345]  in
                      abs uu____50344 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____50343  in
                  [uu____50334]  in
                uu____50314 :: uu____50323  in
              (fa, uu____50303)  in
            FStar_Syntax_Syntax.Tm_app uu____50286  in
          FStar_Syntax_Syntax.mk uu____50285  in
        uu____50278 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____50472 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____50472
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____50491 -> true
    | uu____50493 -> false
  
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
          let uu____50540 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____50540, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____50569 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____50569, FStar_Pervasives_Native.None, t2)  in
        let uu____50583 =
          let uu____50584 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____50584  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____50583
  
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
      let uu____50660 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____50663 =
        let uu____50674 = FStar_Syntax_Syntax.as_arg p  in [uu____50674]  in
      mk_app uu____50660 uu____50663
  
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
      let uu____50714 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____50717 =
        let uu____50728 = FStar_Syntax_Syntax.as_arg p  in [uu____50728]  in
      mk_app uu____50714 uu____50717
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____50763 = head_and_args t  in
    match uu____50763 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____50812 =
          let uu____50827 =
            let uu____50828 = FStar_Syntax_Subst.compress head3  in
            uu____50828.FStar_Syntax_Syntax.n  in
          (uu____50827, args)  in
        (match uu____50812 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____50847)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____50913 =
                    let uu____50918 =
                      let uu____50919 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____50919]  in
                    FStar_Syntax_Subst.open_term uu____50918 p  in
                  (match uu____50913 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____50976 -> failwith "impossible"  in
                       let uu____50984 =
                         let uu____50986 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____50986
                          in
                       if uu____50984
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____51002 -> FStar_Pervasives_Native.None)
         | uu____51005 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51036 = head_and_args t  in
    match uu____51036 with
    | (head1,args) ->
        let uu____51087 =
          let uu____51102 =
            let uu____51103 = FStar_Syntax_Subst.compress head1  in
            uu____51103.FStar_Syntax_Syntax.n  in
          (uu____51102, args)  in
        (match uu____51087 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____51125;
               FStar_Syntax_Syntax.vars = uu____51126;_},u::[]),(t1,uu____51129)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____51176 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51211 = head_and_args t  in
    match uu____51211 with
    | (head1,args) ->
        let uu____51262 =
          let uu____51277 =
            let uu____51278 = FStar_Syntax_Subst.compress head1  in
            uu____51278.FStar_Syntax_Syntax.n  in
          (uu____51277, args)  in
        (match uu____51262 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____51300;
               FStar_Syntax_Syntax.vars = uu____51301;_},u::[]),(t1,uu____51304)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____51351 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____51379 =
      let uu____51396 = unmeta t  in head_and_args uu____51396  in
    match uu____51379 with
    | (head1,uu____51399) ->
        let uu____51424 =
          let uu____51425 = un_uinst head1  in
          uu____51425.FStar_Syntax_Syntax.n  in
        (match uu____51424 with
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
         | uu____51430 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51450 =
      let uu____51463 =
        let uu____51464 = FStar_Syntax_Subst.compress t  in
        uu____51464.FStar_Syntax_Syntax.n  in
      match uu____51463 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____51594 =
            let uu____51605 =
              let uu____51606 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____51606  in
            (b, uu____51605)  in
          FStar_Pervasives_Native.Some uu____51594
      | uu____51623 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____51450
      (fun uu____51661  ->
         match uu____51661 with
         | (b,c) ->
             let uu____51698 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____51698 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____51761 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____51798 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____51798
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____51850 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____51893 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____51934 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____51973) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____51985) ->
          unmeta_monadic t
      | uu____51998 -> f2  in
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
      let aux f2 uu____52094 =
        match uu____52094 with
        | (lid,arity) ->
            let uu____52103 =
              let uu____52120 = unmeta_monadic f2  in
              head_and_args uu____52120  in
            (match uu____52103 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____52150 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____52150
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____52226 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____52226)
      | uu____52239 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____52306 = head_and_args t1  in
        match uu____52306 with
        | (t2,args) ->
            let uu____52361 = un_uinst t2  in
            let uu____52362 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____52403  ->
                      match uu____52403 with
                      | (t3,imp) ->
                          let uu____52422 = unascribe t3  in
                          (uu____52422, imp)))
               in
            (uu____52361, uu____52362)
         in
      let rec aux qopt out t1 =
        let uu____52473 = let uu____52497 = flat t1  in (qopt, uu____52497)
           in
        match uu____52473 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____52537;
                 FStar_Syntax_Syntax.vars = uu____52538;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____52541);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____52542;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____52543;_},uu____52544)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____52646;
                 FStar_Syntax_Syntax.vars = uu____52647;_},uu____52648::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____52651);
                  FStar_Syntax_Syntax.pos = uu____52652;
                  FStar_Syntax_Syntax.vars = uu____52653;_},uu____52654)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____52771;
               FStar_Syntax_Syntax.vars = uu____52772;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____52775);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____52776;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____52777;_},uu____52778)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____52871 =
              let uu____52875 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____52875  in
            aux uu____52871 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____52885;
               FStar_Syntax_Syntax.vars = uu____52886;_},uu____52887::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____52890);
                FStar_Syntax_Syntax.pos = uu____52891;
                FStar_Syntax_Syntax.vars = uu____52892;_},uu____52893)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____53002 =
              let uu____53006 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____53006  in
            aux uu____53002 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____53016) ->
            let bs = FStar_List.rev out  in
            let uu____53069 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____53069 with
             | (bs1,t2) ->
                 let uu____53078 = patterns t2  in
                 (match uu____53078 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____53128 -> FStar_Pervasives_Native.None  in
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
      let uu____53220 = un_squash t  in
      FStar_Util.bind_opt uu____53220
        (fun t1  ->
           let uu____53236 = head_and_args' t1  in
           match uu____53236 with
           | (hd1,args) ->
               let uu____53275 =
                 let uu____53281 =
                   let uu____53282 = un_uinst hd1  in
                   uu____53282.FStar_Syntax_Syntax.n  in
                 (uu____53281, (FStar_List.length args))  in
               (match uu____53275 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53298) when
                    (_53298 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53301) when
                    (_53301 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53304) when
                    (_53304 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53307) when
                    (_53307 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53310) when
                    (_53310 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53313) when
                    (_53313 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53316) when
                    (_53316 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53319) when
                    (_53319 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____53320 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____53350 = un_squash t  in
      FStar_Util.bind_opt uu____53350
        (fun t1  ->
           let uu____53365 = arrow_one t1  in
           match uu____53365 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____53380 =
                 let uu____53382 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____53382  in
               if uu____53380
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____53392 = comp_to_comp_typ_nouniv c  in
                    uu____53392.FStar_Syntax_Syntax.result_typ  in
                  let uu____53393 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____53393
                  then
                    let uu____53400 = patterns q  in
                    match uu____53400 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____53463 =
                       let uu____53464 =
                         let uu____53469 =
                           let uu____53470 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____53481 =
                             let uu____53492 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____53492]  in
                           uu____53470 :: uu____53481  in
                         (FStar_Parser_Const.imp_lid, uu____53469)  in
                       BaseConn uu____53464  in
                     FStar_Pervasives_Native.Some uu____53463))
           | uu____53525 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____53533 = un_squash t  in
      FStar_Util.bind_opt uu____53533
        (fun t1  ->
           let uu____53564 = head_and_args' t1  in
           match uu____53564 with
           | (hd1,args) ->
               let uu____53603 =
                 let uu____53618 =
                   let uu____53619 = un_uinst hd1  in
                   uu____53619.FStar_Syntax_Syntax.n  in
                 (uu____53618, args)  in
               (match uu____53603 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____53636)::(a2,uu____53638)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____53689 =
                      let uu____53690 = FStar_Syntax_Subst.compress a2  in
                      uu____53690.FStar_Syntax_Syntax.n  in
                    (match uu____53689 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____53697) ->
                         let uu____53732 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____53732 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____53785 -> failwith "impossible"  in
                              let uu____53793 = patterns q1  in
                              (match uu____53793 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____53854 -> FStar_Pervasives_Native.None)
                | uu____53855 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____53878 = destruct_sq_forall phi  in
          (match uu____53878 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _53888  -> FStar_Pervasives_Native.Some _53888)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____53895 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____53901 = destruct_sq_exists phi  in
          (match uu____53901 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _53911  -> FStar_Pervasives_Native.Some _53911)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____53918 -> f1)
      | uu____53921 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____53925 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____53925
      (fun uu____53930  ->
         let uu____53931 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____53931
           (fun uu____53936  ->
              let uu____53937 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____53937
                (fun uu____53942  ->
                   let uu____53943 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____53943
                     (fun uu____53948  ->
                        let uu____53949 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____53949
                          (fun uu____53953  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____53971 =
            let uu____53976 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____53976  in
          let uu____53977 =
            let uu____53978 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____53978  in
          let uu____53981 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____53971 a.FStar_Syntax_Syntax.action_univs uu____53977
            FStar_Parser_Const.effect_Tot_lid uu____53981 [] pos
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
    let uu____54007 =
      let uu____54014 =
        let uu____54015 =
          let uu____54032 =
            let uu____54043 = FStar_Syntax_Syntax.as_arg t  in [uu____54043]
             in
          (reify_1, uu____54032)  in
        FStar_Syntax_Syntax.Tm_app uu____54015  in
      FStar_Syntax_Syntax.mk uu____54014  in
    uu____54007 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____54095 =
        let uu____54102 =
          let uu____54103 =
            let uu____54104 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____54104  in
          FStar_Syntax_Syntax.Tm_constant uu____54103  in
        FStar_Syntax_Syntax.mk uu____54102  in
      uu____54095 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____54106 =
      let uu____54113 =
        let uu____54114 =
          let uu____54131 =
            let uu____54142 = FStar_Syntax_Syntax.as_arg t  in [uu____54142]
             in
          (reflect_, uu____54131)  in
        FStar_Syntax_Syntax.Tm_app uu____54114  in
      FStar_Syntax_Syntax.mk uu____54113  in
    uu____54106 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____54186 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____54211 = unfold_lazy i  in delta_qualifier uu____54211
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____54213 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____54214 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____54215 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____54238 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____54251 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____54252 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____54259 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____54260 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____54276) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____54281;
           FStar_Syntax_Syntax.index = uu____54282;
           FStar_Syntax_Syntax.sort = t2;_},uu____54284)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____54293) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____54299,uu____54300) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____54342) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____54367,t2,uu____54369) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____54394,t2) -> delta_qualifier t2
  
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
    let uu____54433 = delta_qualifier t  in incr_delta_depth uu____54433
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____54441 =
      let uu____54442 = FStar_Syntax_Subst.compress t  in
      uu____54442.FStar_Syntax_Syntax.n  in
    match uu____54441 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____54447 -> false
  
let rec apply_last :
  'Auu____54456 .
    ('Auu____54456 -> 'Auu____54456) ->
      'Auu____54456 Prims.list -> 'Auu____54456 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____54482 = f a  in [uu____54482]
      | x::xs -> let uu____54487 = apply_last f xs  in x :: uu____54487
  
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
          let uu____54542 =
            let uu____54549 =
              let uu____54550 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____54550  in
            FStar_Syntax_Syntax.mk uu____54549  in
          uu____54542 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____54564 =
            let uu____54569 =
              let uu____54570 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____54570
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____54569 args  in
          uu____54564 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____54584 =
            let uu____54589 =
              let uu____54590 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____54590
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____54589 args  in
          uu____54584 FStar_Pervasives_Native.None pos  in
        let uu____54591 =
          let uu____54592 =
            let uu____54593 = FStar_Syntax_Syntax.iarg typ  in [uu____54593]
             in
          nil uu____54592 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____54627 =
                 let uu____54628 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____54637 =
                   let uu____54648 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____54657 =
                     let uu____54668 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____54668]  in
                   uu____54648 :: uu____54657  in
                 uu____54628 :: uu____54637  in
               cons1 uu____54627 t.FStar_Syntax_Syntax.pos) l uu____54591
  
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
        | uu____54777 -> false
  
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
          | uu____54891 -> false
  
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
        | uu____55057 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____55095 = FStar_ST.op_Bang debug_term_eq  in
          if uu____55095
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
        let t11 = let uu____55317 = unmeta_safe t1  in canon_app uu____55317
           in
        let t21 = let uu____55323 = unmeta_safe t2  in canon_app uu____55323
           in
        let uu____55326 =
          let uu____55331 =
            let uu____55332 =
              let uu____55335 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____55335  in
            uu____55332.FStar_Syntax_Syntax.n  in
          let uu____55336 =
            let uu____55337 =
              let uu____55340 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____55340  in
            uu____55337.FStar_Syntax_Syntax.n  in
          (uu____55331, uu____55336)  in
        match uu____55326 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____55342,uu____55343) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____55352,FStar_Syntax_Syntax.Tm_uinst uu____55353) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____55362,uu____55363) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____55388,FStar_Syntax_Syntax.Tm_delayed uu____55389) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____55414,uu____55415) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____55444,FStar_Syntax_Syntax.Tm_ascribed uu____55445) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____55484 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____55484
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____55489 = FStar_Const.eq_const c1 c2  in
            check "const" uu____55489
        | (FStar_Syntax_Syntax.Tm_type
           uu____55492,FStar_Syntax_Syntax.Tm_type uu____55493) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____55551 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____55551) &&
              (let uu____55561 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____55561)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____55610 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____55610) &&
              (let uu____55620 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____55620)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____55638 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____55638)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____55695 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____55695) &&
              (let uu____55699 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____55699)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____55788 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____55788) &&
              (let uu____55792 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____55792)
        | (FStar_Syntax_Syntax.Tm_lazy uu____55809,uu____55810) ->
            let uu____55811 =
              let uu____55813 = unlazy t11  in
              term_eq_dbg dbg uu____55813 t21  in
            check "lazy_l" uu____55811
        | (uu____55815,FStar_Syntax_Syntax.Tm_lazy uu____55816) ->
            let uu____55817 =
              let uu____55819 = unlazy t21  in
              term_eq_dbg dbg t11 uu____55819  in
            check "lazy_r" uu____55817
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____55864 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____55864))
              &&
              (let uu____55868 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____55868)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____55872),FStar_Syntax_Syntax.Tm_uvar (u2,uu____55874)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____55932 =
               let uu____55934 = eq_quoteinfo qi1 qi2  in uu____55934 = Equal
                in
             check "tm_quoted qi" uu____55932) &&
              (let uu____55937 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____55937)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____55967 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____55967) &&
                   (let uu____55971 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____55971)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____55990 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____55990) &&
                    (let uu____55994 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____55994))
                   &&
                   (let uu____55998 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____55998)
             | uu____56001 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____56007) -> fail "unk"
        | (uu____56009,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____56011,uu____56012) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____56014,uu____56015) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____56017,uu____56018) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____56020,uu____56021) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____56023,uu____56024) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____56026,uu____56027) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____56047,uu____56048) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____56064,uu____56065) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____56073,uu____56074) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____56092,uu____56093) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____56117,uu____56118) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____56133,uu____56134) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____56148,uu____56149) ->
            fail "bottom"
        | (uu____56157,FStar_Syntax_Syntax.Tm_bvar uu____56158) ->
            fail "bottom"
        | (uu____56160,FStar_Syntax_Syntax.Tm_name uu____56161) ->
            fail "bottom"
        | (uu____56163,FStar_Syntax_Syntax.Tm_fvar uu____56164) ->
            fail "bottom"
        | (uu____56166,FStar_Syntax_Syntax.Tm_constant uu____56167) ->
            fail "bottom"
        | (uu____56169,FStar_Syntax_Syntax.Tm_type uu____56170) ->
            fail "bottom"
        | (uu____56172,FStar_Syntax_Syntax.Tm_abs uu____56173) ->
            fail "bottom"
        | (uu____56193,FStar_Syntax_Syntax.Tm_arrow uu____56194) ->
            fail "bottom"
        | (uu____56210,FStar_Syntax_Syntax.Tm_refine uu____56211) ->
            fail "bottom"
        | (uu____56219,FStar_Syntax_Syntax.Tm_app uu____56220) ->
            fail "bottom"
        | (uu____56238,FStar_Syntax_Syntax.Tm_match uu____56239) ->
            fail "bottom"
        | (uu____56263,FStar_Syntax_Syntax.Tm_let uu____56264) ->
            fail "bottom"
        | (uu____56279,FStar_Syntax_Syntax.Tm_uvar uu____56280) ->
            fail "bottom"
        | (uu____56294,FStar_Syntax_Syntax.Tm_meta uu____56295) ->
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
               let uu____56330 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____56330)
          (fun q1  ->
             fun q2  ->
               let uu____56342 =
                 let uu____56344 = eq_aqual q1 q2  in uu____56344 = Equal  in
               check "arg qual" uu____56342) a1 a2

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
               let uu____56369 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____56369)
          (fun q1  ->
             fun q2  ->
               let uu____56381 =
                 let uu____56383 = eq_aqual q1 q2  in uu____56383 = Equal  in
               check "binder qual" uu____56381) b1 b2

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
        ((let uu____56403 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____56403) &&
           (let uu____56407 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____56407))
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
    fun uu____56417  ->
      fun uu____56418  ->
        match (uu____56417, uu____56418) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____56545 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____56545) &&
               (let uu____56549 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____56549))
              &&
              (let uu____56553 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____56595 -> false  in
               check "branch when" uu____56553)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____56616 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____56616) &&
           (let uu____56625 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____56625))
          &&
          (let uu____56629 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____56629)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____56646 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____56646 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____56700 ->
        let uu____56723 =
          let uu____56725 = FStar_Syntax_Subst.compress t  in
          sizeof uu____56725  in
        (Prims.parse_int "1") + uu____56723
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____56728 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____56728
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____56732 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____56732
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____56741 = sizeof t1  in (FStar_List.length us) + uu____56741
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____56745) ->
        let uu____56770 = sizeof t1  in
        let uu____56772 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____56787  ->
                 match uu____56787 with
                 | (bv,uu____56797) ->
                     let uu____56802 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____56802) (Prims.parse_int "0") bs
           in
        uu____56770 + uu____56772
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____56831 = sizeof hd1  in
        let uu____56833 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____56848  ->
                 match uu____56848 with
                 | (arg,uu____56858) ->
                     let uu____56863 = sizeof arg  in acc + uu____56863)
            (Prims.parse_int "0") args
           in
        uu____56831 + uu____56833
    | uu____56866 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____56880 =
        let uu____56881 = un_uinst t  in uu____56881.FStar_Syntax_Syntax.n
         in
      match uu____56880 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____56886 -> false
  
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
        let uu____56935 = FStar_Options.set_options t s  in
        match uu____56935 with
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
          ((let uu____56952 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____56952 (fun a1  -> ()));
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
          let uu____56967 = FStar_Options.internal_pop ()  in
          if uu____56967
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
    | FStar_Syntax_Syntax.Tm_delayed uu____56999 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____57026 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____57041 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____57042 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____57043 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____57052) ->
        let uu____57077 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____57077 with
         | (bs1,t2) ->
             let uu____57086 =
               FStar_List.collect
                 (fun uu____57098  ->
                    match uu____57098 with
                    | (b,uu____57108) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____57113 = unbound_variables t2  in
             FStar_List.append uu____57086 uu____57113)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____57138 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____57138 with
         | (bs1,c1) ->
             let uu____57147 =
               FStar_List.collect
                 (fun uu____57159  ->
                    match uu____57159 with
                    | (b,uu____57169) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____57174 = unbound_variables_comp c1  in
             FStar_List.append uu____57147 uu____57174)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____57183 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____57183 with
         | (bs,t2) ->
             let uu____57206 =
               FStar_List.collect
                 (fun uu____57218  ->
                    match uu____57218 with
                    | (b1,uu____57228) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____57233 = unbound_variables t2  in
             FStar_List.append uu____57206 uu____57233)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____57262 =
          FStar_List.collect
            (fun uu____57276  ->
               match uu____57276 with
               | (x,uu____57288) -> unbound_variables x) args
           in
        let uu____57297 = unbound_variables t1  in
        FStar_List.append uu____57262 uu____57297
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____57338 = unbound_variables t1  in
        let uu____57341 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____57356 = FStar_Syntax_Subst.open_branch br  in
                  match uu____57356 with
                  | (p,wopt,t2) ->
                      let uu____57378 = unbound_variables t2  in
                      let uu____57381 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____57378 uu____57381))
           in
        FStar_List.append uu____57338 uu____57341
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____57395) ->
        let uu____57436 = unbound_variables t1  in
        let uu____57439 =
          let uu____57442 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____57473 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____57442 uu____57473  in
        FStar_List.append uu____57436 uu____57439
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____57514 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____57517 =
          let uu____57520 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____57523 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____57528 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____57530 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____57530 with
                 | (uu____57551,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____57520 uu____57523  in
        FStar_List.append uu____57514 uu____57517
    | FStar_Syntax_Syntax.Tm_let ((uu____57553,lbs),t1) ->
        let uu____57573 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____57573 with
         | (lbs1,t2) ->
             let uu____57588 = unbound_variables t2  in
             let uu____57591 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____57598 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____57601 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____57598 uu____57601) lbs1
                in
             FStar_List.append uu____57588 uu____57591)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____57618 = unbound_variables t1  in
        let uu____57621 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____57660  ->
                      match uu____57660 with
                      | (a,uu____57672) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____57681,uu____57682,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____57688,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____57694 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____57703 -> []
          | FStar_Syntax_Syntax.Meta_named uu____57704 -> []  in
        FStar_List.append uu____57618 uu____57621

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____57711) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____57721) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____57731 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____57734 =
          FStar_List.collect
            (fun uu____57748  ->
               match uu____57748 with
               | (a,uu____57760) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____57731 uu____57734

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
            let uu____57875 = head_and_args h  in
            (match uu____57875 with
             | (head1,args) ->
                 let uu____57936 =
                   let uu____57937 = FStar_Syntax_Subst.compress head1  in
                   uu____57937.FStar_Syntax_Syntax.n  in
                 (match uu____57936 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____57990 -> aux (h :: acc) t))
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
      let uu____58014 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____58014 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2926_58056 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2926_58056.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2926_58056.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2926_58056.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2926_58056.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____58064 =
      let uu____58065 = FStar_Syntax_Subst.compress t  in
      uu____58065.FStar_Syntax_Syntax.n  in
    match uu____58064 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____58069,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____58097)::uu____58098 ->
                  let pats' = unmeta pats  in
                  let uu____58158 = head_and_args pats'  in
                  (match uu____58158 with
                   | (head1,uu____58177) ->
                       let uu____58202 =
                         let uu____58203 = un_uinst head1  in
                         uu____58203.FStar_Syntax_Syntax.n  in
                       (match uu____58202 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____58208 -> false))
              | uu____58210 -> false)
         | uu____58222 -> false)
    | uu____58224 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____58240 =
      let uu____58257 = unmeta e  in head_and_args uu____58257  in
    match uu____58240 with
    | (head1,args) ->
        let uu____58288 =
          let uu____58303 =
            let uu____58304 = un_uinst head1  in
            uu____58304.FStar_Syntax_Syntax.n  in
          (uu____58303, args)  in
        (match uu____58288 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____58322) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____58346::(hd1,uu____58348)::(tl1,uu____58350)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____58417 =
               let uu____58420 =
                 let uu____58423 = list_elements tl1  in
                 FStar_Util.must uu____58423  in
               hd1 :: uu____58420  in
             FStar_Pervasives_Native.Some uu____58417
         | uu____58432 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____58461 =
      let uu____58462 = FStar_Syntax_Subst.compress t  in
      uu____58462.FStar_Syntax_Syntax.n  in
    match uu____58461 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____58469) ->
        let uu____58504 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____58504 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____58538 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____58538
             then
               let uu____58545 =
                 let uu____58556 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____58556]  in
               mk_app t uu____58545
             else e1)
    | uu____58583 ->
        let uu____58584 =
          let uu____58595 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____58595]  in
        mk_app t uu____58584
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____58650 = list_elements e  in
        match uu____58650 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____58681 =
          let uu____58698 = unmeta p  in
          FStar_All.pipe_right uu____58698 head_and_args  in
        match uu____58681 with
        | (head1,args) ->
            let uu____58749 =
              let uu____58764 =
                let uu____58765 = un_uinst head1  in
                uu____58765.FStar_Syntax_Syntax.n  in
              (uu____58764, args)  in
            (match uu____58749 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____58787,uu____58788)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____58840 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____58895 =
            let uu____58912 = unmeta t1  in
            FStar_All.pipe_right uu____58912 head_and_args  in
          match uu____58895 with
          | (head1,args) ->
              let uu____58959 =
                let uu____58974 =
                  let uu____58975 = un_uinst head1  in
                  uu____58975.FStar_Syntax_Syntax.n  in
                (uu____58974, args)  in
              (match uu____58959 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____58994)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____59031 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____59061 = smt_pat_or1 t1  in
            (match uu____59061 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____59083 = list_elements1 e  in
                 FStar_All.pipe_right uu____59083
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____59113 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____59113
                           (FStar_List.map one_pat)))
             | uu____59136 ->
                 let uu____59141 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____59141])
        | uu____59192 ->
            let uu____59195 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____59195]
         in
      let uu____59246 =
        let uu____59279 =
          let uu____59280 = FStar_Syntax_Subst.compress t  in
          uu____59280.FStar_Syntax_Syntax.n  in
        match uu____59279 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____59337 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____59337 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____59408;
                        FStar_Syntax_Syntax.effect_name = uu____59409;
                        FStar_Syntax_Syntax.result_typ = uu____59410;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____59412)::(post,uu____59414)::(pats,uu____59416)::[];
                        FStar_Syntax_Syntax.flags = uu____59417;_}
                      ->
                      let uu____59478 = lemma_pats pats  in
                      (binders1, pre, post, uu____59478)
                  | uu____59515 -> failwith "impos"))
        | uu____59549 -> failwith "Impos"  in
      match uu____59246 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____59641 =
              let uu____59648 =
                let uu____59649 =
                  let uu____59656 = mk_imp pre post1  in
                  (uu____59656, (FStar_Syntax_Syntax.Meta_pattern patterns))
                   in
                FStar_Syntax_Syntax.Tm_meta uu____59649  in
              FStar_Syntax_Syntax.mk uu____59648  in
            uu____59641 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____59662 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____59662 body
             in
          quant
  