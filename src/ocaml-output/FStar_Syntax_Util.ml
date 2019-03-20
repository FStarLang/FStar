open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____40483 = FStar_ST.op_Bang tts_f  in
    match uu____40483 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____40547 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____40547 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____40554 =
      let uu____40557 =
        let uu____40560 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____40560]  in
      FStar_List.append lid.FStar_Ident.ns uu____40557  in
    FStar_Ident.lid_of_ids uu____40554
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____40578 .
    (FStar_Syntax_Syntax.bv * 'Auu____40578) ->
      (FStar_Syntax_Syntax.term * 'Auu____40578)
  =
  fun uu____40591  ->
    match uu____40591 with
    | (b,imp) ->
        let uu____40598 = FStar_Syntax_Syntax.bv_to_name b  in
        (uu____40598, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____40650 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____40650
            then []
            else
              (let uu____40669 = arg_of_non_null_binder b  in [uu____40669])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____40704 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____40786 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____40786
              then
                let b1 =
                  let uu____40812 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____40812, (FStar_Pervasives_Native.snd b))  in
                let uu____40819 = arg_of_non_null_binder b1  in
                (b1, uu____40819)
              else
                (let uu____40842 = arg_of_non_null_binder b  in
                 (b, uu____40842))))
       in
    FStar_All.pipe_right uu____40704 FStar_List.unzip
  
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
              let uu____40976 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____40976
              then
                let uu____40985 = b  in
                match uu____40985 with
                | (a,imp) ->
                    let b1 =
                      let uu____41005 =
                        let uu____41007 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____41007  in
                      FStar_Ident.id_of_text uu____41005  in
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
        let uu____41052 =
          let uu____41059 =
            let uu____41060 =
              let uu____41075 = name_binders binders  in (uu____41075, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____41060  in
          FStar_Syntax_Syntax.mk uu____41059  in
        uu____41052 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____41094 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____41131  ->
            match uu____41131 with
            | (t,imp) ->
                let uu____41142 =
                  let uu____41143 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____41143
                   in
                (uu____41142, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____41198  ->
            match uu____41198 with
            | (t,imp) ->
                let uu____41215 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____41215, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____41228 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____41228
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____41240 . 'Auu____41240 -> 'Auu____41240 Prims.list =
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
          (fun uu____41366  ->
             fun uu____41367  ->
               match (uu____41366, uu____41367) with
               | ((x,uu____41393),(y,uu____41395)) ->
                   let uu____41416 =
                     let uu____41423 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____41423)  in
                   FStar_Syntax_Syntax.NT uu____41416) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____41439) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____41445,uu____41446) ->
        unmeta e2
    | uu____41487 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____41501 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____41508 -> e1
         | uu____41517 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____41519,uu____41520) ->
        unmeta_safe e2
    | uu____41561 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____41580 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____41583 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____41597 = univ_kernel u1  in
        (match uu____41597 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____41614 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____41623 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____41638 = univ_kernel u  in
    FStar_Pervasives_Native.snd uu____41638
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____41658,uu____41659) ->
          failwith "Impossible: compare_univs"
      | (uu____41663,FStar_Syntax_Syntax.U_bvar uu____41664) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____41669) ->
          ~- (Prims.parse_int "1")
      | (uu____41671,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____41674) -> ~- (Prims.parse_int "1")
      | (uu____41676,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____41680,FStar_Syntax_Syntax.U_unif
         uu____41681) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____41691,FStar_Syntax_Syntax.U_name
         uu____41692) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____41720 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____41722 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____41720 - uu____41722
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____41740 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____41740
                 (fun uu____41756  ->
                    match uu____41756 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____41784,uu____41785) ->
          ~- (Prims.parse_int "1")
      | (uu____41789,FStar_Syntax_Syntax.U_max uu____41790) ->
          (Prims.parse_int "1")
      | uu____41794 ->
          let uu____41799 = univ_kernel u1  in
          (match uu____41799 with
           | (k1,n1) ->
               let uu____41810 = univ_kernel u2  in
               (match uu____41810 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____41841 = compare_univs u1 u2  in
      uu____41841 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____41860 =
        let uu____41861 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____41861;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____41860
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____41881 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____41890 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____41913 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____41922 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____41949 =
          let uu____41950 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____41950  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____41949;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____41979 =
          let uu____41980 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____41980  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____41979;
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
      let uu___631_42016 = c  in
      let uu____42017 =
        let uu____42018 =
          let uu___633_42019 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___633_42019.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___633_42019.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___633_42019.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___633_42019.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____42018  in
      {
        FStar_Syntax_Syntax.n = uu____42017;
        FStar_Syntax_Syntax.pos = (uu___631_42016.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___631_42016.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____42045 -> c
        | FStar_Syntax_Syntax.GTotal uu____42054 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___645_42065 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___645_42065.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___645_42065.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___645_42065.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___645_42065.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___648_42066 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___648_42066.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___648_42066.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____42069  ->
           let uu____42070 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____42070)
  
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
    | uu____42110 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____42125 -> true
    | FStar_Syntax_Syntax.GTotal uu____42135 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___402_42160  ->
               match uu___402_42160 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____42164 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___403_42177  ->
               match uu___403_42177 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____42181 -> false)))
  
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
            (fun uu___404_42194  ->
               match uu___404_42194 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____42198 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___405_42215  ->
            match uu___405_42215 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____42219 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___406_42232  ->
            match uu___406_42232 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____42236 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____42268 -> true
    | FStar_Syntax_Syntax.GTotal uu____42278 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___407_42293  ->
                   match uu___407_42293 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____42296 -> false)))
  
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
            (fun uu___408_42341  ->
               match uu___408_42341 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____42344 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____42360 =
      let uu____42361 = FStar_Syntax_Subst.compress t  in
      uu____42361.FStar_Syntax_Syntax.n  in
    match uu____42360 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____42365,c) -> is_pure_or_ghost_comp c
    | uu____42387 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____42402 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____42411 =
      let uu____42412 = FStar_Syntax_Subst.compress t  in
      uu____42412.FStar_Syntax_Syntax.n  in
    match uu____42411 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____42416,c) -> is_lemma_comp c
    | uu____42438 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____42446 =
      let uu____42447 = FStar_Syntax_Subst.compress t  in
      uu____42447.FStar_Syntax_Syntax.n  in
    match uu____42446 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____42451) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____42477) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____42514,t1,uu____42516) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____42542,uu____42543) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____42585) -> head_of t1
    | uu____42590 -> t
  
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
    | uu____42668 -> (t1, [])
  
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
        let uu____42750 = head_and_args' head1  in
        (match uu____42750 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____42819 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____42846) ->
        FStar_Syntax_Subst.compress t2
    | uu____42851 -> t1
  
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
                (fun uu___409_42869  ->
                   match uu___409_42869 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____42872 -> false)))
    | uu____42874 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____42891) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____42901) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____42930 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____42939 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___801_42951 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___801_42951.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___801_42951.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___801_42951.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___801_42951.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____42965  ->
           let uu____42966 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____42966 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_42984  ->
            match uu___410_42984 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____42988 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____42996 -> []
    | FStar_Syntax_Syntax.GTotal uu____43013 -> []
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
    | uu____43057 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____43067,uu____43068) ->
        unascribe e2
    | uu____43109 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____43162,uu____43163) ->
          ascribe t' k
      | uu____43204 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____43231 =
      let uu____43240 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____43240  in
    uu____43231 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____43296 =
      let uu____43297 = FStar_Syntax_Subst.compress t  in
      uu____43297.FStar_Syntax_Syntax.n  in
    match uu____43296 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____43301 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____43301
    | uu____43302 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____43309 =
      let uu____43310 = FStar_Syntax_Subst.compress t  in
      uu____43310.FStar_Syntax_Syntax.n  in
    match uu____43309 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____43314 ->
             let uu____43323 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____43323
         | uu____43324 -> t)
    | uu____43325 -> t
  
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
      | uu____43349 -> false
  
let rec unlazy_as_t :
  'Auu____43362 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____43362
  =
  fun k  ->
    fun t  ->
      let uu____43373 =
        let uu____43374 = FStar_Syntax_Subst.compress t  in
        uu____43374.FStar_Syntax_Syntax.n  in
      match uu____43373 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____43379;
            FStar_Syntax_Syntax.rng = uu____43380;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____43383 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____43424 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____43424;
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
    let uu____43437 =
      let uu____43452 = unascribe t  in head_and_args' uu____43452  in
    match uu____43437 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____43486 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____43497 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____43508 -> false
  
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
      | (NotEqual ,uu____43558) -> NotEqual
      | (uu____43559,NotEqual ) -> NotEqual
      | (Unknown ,uu____43560) -> Unknown
      | (uu____43561,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_43682 = if uu___411_43682 then Equal else Unknown
         in
      let equal_iff uu___412_43693 =
        if uu___412_43693 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____43714 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____43736 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____43736
        then
          let uu____43740 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____43817  ->
                    match uu____43817 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____43858 = eq_tm a1 a2  in
                        eq_inj acc uu____43858) Equal) uu____43740
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____43872 =
          let uu____43889 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____43889 head_and_args  in
        match uu____43872 with
        | (head1,args1) ->
            let uu____43942 =
              let uu____43959 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____43959 head_and_args  in
            (match uu____43942 with
             | (head2,args2) ->
                 let uu____44012 =
                   let uu____44017 =
                     let uu____44018 = un_uinst head1  in
                     uu____44018.FStar_Syntax_Syntax.n  in
                   let uu____44021 =
                     let uu____44022 = un_uinst head2  in
                     uu____44022.FStar_Syntax_Syntax.n  in
                   (uu____44017, uu____44021)  in
                 (match uu____44012 with
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
                  | uu____44049 -> FStar_Pervasives_Native.None))
         in
      let uu____44062 =
        let uu____44067 =
          let uu____44068 = unmeta t11  in uu____44068.FStar_Syntax_Syntax.n
           in
        let uu____44071 =
          let uu____44072 = unmeta t21  in uu____44072.FStar_Syntax_Syntax.n
           in
        (uu____44067, uu____44071)  in
      match uu____44062 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____44078,uu____44079) ->
          let uu____44080 = unlazy t11  in eq_tm uu____44080 t21
      | (uu____44081,FStar_Syntax_Syntax.Tm_lazy uu____44082) ->
          let uu____44083 = unlazy t21  in eq_tm t11 uu____44083
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____44086 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____44110 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____44110
            (fun uu____44158  ->
               match uu____44158 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____44173 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____44173
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____44187 = eq_tm f g  in
          eq_and uu____44187
            (fun uu____44190  ->
               let uu____44191 = eq_univs_list us vs  in equal_if uu____44191)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____44193),uu____44194) -> Unknown
      | (uu____44195,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____44196)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____44199 = FStar_Const.eq_const c d  in
          equal_iff uu____44199
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____44202)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____44204))) ->
          let uu____44233 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____44233
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____44287 =
            let uu____44292 =
              let uu____44293 = un_uinst h1  in
              uu____44293.FStar_Syntax_Syntax.n  in
            let uu____44296 =
              let uu____44297 = un_uinst h2  in
              uu____44297.FStar_Syntax_Syntax.n  in
            (uu____44292, uu____44296)  in
          (match uu____44287 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____44303 =
                    let uu____44305 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____44305  in
                  FStar_List.mem uu____44303 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____44307 ->
               let uu____44312 = eq_tm h1 h2  in
               eq_and uu____44312 (fun uu____44314  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____44420 = FStar_List.zip bs1 bs2  in
            let uu____44483 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____44520  ->
                 fun a  ->
                   match uu____44520 with
                   | (b1,b2) ->
                       eq_and a (fun uu____44613  -> branch_matches b1 b2))
              uu____44420 uu____44483
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____44618 = eq_univs u v1  in equal_if uu____44618
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____44632 = eq_quoteinfo q1 q2  in
          eq_and uu____44632 (fun uu____44634  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____44647 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____44647 (fun uu____44649  -> eq_tm phi1 phi2)
      | uu____44650 -> Unknown

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
      | ([],uu____44722) -> NotEqual
      | (uu____44753,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____44845 = eq_tm t1 t2  in
             match uu____44845 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____44846 = eq_antiquotes a11 a21  in
                 (match uu____44846 with
                  | NotEqual  -> NotEqual
                  | uu____44847 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____44862) -> NotEqual
      | (uu____44869,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____44899 -> NotEqual

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
        | (uu____44991,uu____44992) -> false  in
      let uu____45002 = b1  in
      match uu____45002 with
      | (p1,w1,t1) ->
          let uu____45036 = b2  in
          (match uu____45036 with
           | (p2,w2,t2) ->
               let uu____45070 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____45070
               then
                 let uu____45073 =
                   (let uu____45077 = eq_tm t1 t2  in uu____45077 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____45086 = eq_tm t11 t21  in
                             uu____45086 = Equal) w1 w2)
                    in
                 (if uu____45073 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____45151)::a11,(b,uu____45154)::b1) ->
          let uu____45228 = eq_tm a b  in
          (match uu____45228 with
           | Equal  -> eq_args a11 b1
           | uu____45229 -> Unknown)
      | uu____45230 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____45266) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____45272,uu____45273) ->
        unrefine t2
    | uu____45314 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45322 =
      let uu____45323 = FStar_Syntax_Subst.compress t  in
      uu____45323.FStar_Syntax_Syntax.n  in
    match uu____45322 with
    | FStar_Syntax_Syntax.Tm_uvar uu____45327 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____45342) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____45347 ->
        let uu____45364 =
          let uu____45365 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____45365 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____45364 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____45428,uu____45429) ->
        is_uvar t1
    | uu____45470 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45479 =
      let uu____45480 = unrefine t  in uu____45480.FStar_Syntax_Syntax.n  in
    match uu____45479 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____45486) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____45512) -> is_unit t1
    | uu____45517 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45526 =
      let uu____45527 = FStar_Syntax_Subst.compress t  in
      uu____45527.FStar_Syntax_Syntax.n  in
    match uu____45526 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____45532 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45541 =
      let uu____45542 = unrefine t  in uu____45542.FStar_Syntax_Syntax.n  in
    match uu____45541 with
    | FStar_Syntax_Syntax.Tm_type uu____45546 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____45550) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____45576) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____45581,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____45603 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____45612 =
      let uu____45613 = FStar_Syntax_Subst.compress e  in
      uu____45613.FStar_Syntax_Syntax.n  in
    match uu____45612 with
    | FStar_Syntax_Syntax.Tm_abs uu____45617 -> true
    | uu____45637 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____45646 =
      let uu____45647 = FStar_Syntax_Subst.compress t  in
      uu____45647.FStar_Syntax_Syntax.n  in
    match uu____45646 with
    | FStar_Syntax_Syntax.Tm_arrow uu____45651 -> true
    | uu____45667 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____45677) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____45683,uu____45684) ->
        pre_typ t2
    | uu____45725 -> t1
  
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
      let uu____45750 =
        let uu____45751 = un_uinst typ1  in uu____45751.FStar_Syntax_Syntax.n
         in
      match uu____45750 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____45816 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____45846 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____45867,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____45874) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____45879,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____45890,uu____45891,uu____45892,uu____45893,uu____45894) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____45904,uu____45905,uu____45906,uu____45907) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____45913,uu____45914,uu____45915,uu____45916,uu____45917) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____45925,uu____45926) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____45928,uu____45929) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____45932 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____45933 -> []
    | FStar_Syntax_Syntax.Sig_main uu____45934 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____45948 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_45974  ->
    match uu___413_45974 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____45988 'Auu____45989 .
    ('Auu____45988 FStar_Syntax_Syntax.syntax * 'Auu____45989) ->
      FStar_Range.range
  =
  fun uu____46000  ->
    match uu____46000 with | (hd1,uu____46008) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____46022 'Auu____46023 .
    ('Auu____46022 FStar_Syntax_Syntax.syntax * 'Auu____46023) Prims.list ->
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
      | uu____46121 ->
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
      let uu____46180 =
        FStar_List.map
          (fun uu____46207  ->
             match uu____46207 with
             | (bv,aq) ->
                 let uu____46226 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____46226, aq)) bs
         in
      mk_app f uu____46180
  
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
          let uu____46276 = FStar_Ident.range_of_lid l  in
          let uu____46277 =
            let uu____46286 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____46286  in
          uu____46277 FStar_Pervasives_Native.None uu____46276
      | uu____46291 ->
          let e =
            let uu____46305 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____46305 args  in
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
          let uu____46382 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____46382
          then
            let uu____46385 =
              let uu____46391 =
                let uu____46393 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____46393  in
              let uu____46396 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____46391, uu____46396)  in
            FStar_Ident.mk_ident uu____46385
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1395_46401 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1395_46401.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1395_46401.FStar_Syntax_Syntax.sort)
          }  in
        let uu____46402 = mk_field_projector_name_from_ident lid nm  in
        (uu____46402, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____46414) -> ses
    | uu____46423 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____46434 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____46447 = FStar_Syntax_Unionfind.find uv  in
      match uu____46447 with
      | FStar_Pervasives_Native.Some uu____46450 ->
          let uu____46451 =
            let uu____46453 =
              let uu____46455 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____46455  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____46453  in
          failwith uu____46451
      | uu____46460 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____46543 -> q1 = q2
  
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
              let uu____46589 =
                let uu___1456_46590 = rc  in
                let uu____46591 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1456_46590.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____46591;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1456_46590.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____46589
           in
        match bs with
        | [] -> t
        | uu____46608 ->
            let body =
              let uu____46610 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____46610  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____46640 =
                   let uu____46647 =
                     let uu____46648 =
                       let uu____46667 =
                         let uu____46676 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____46676 bs'  in
                       let uu____46691 = close_lopt lopt'  in
                       (uu____46667, t1, uu____46691)  in
                     FStar_Syntax_Syntax.Tm_abs uu____46648  in
                   FStar_Syntax_Syntax.mk uu____46647  in
                 uu____46640 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____46706 ->
                 let uu____46707 =
                   let uu____46714 =
                     let uu____46715 =
                       let uu____46734 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____46743 = close_lopt lopt  in
                       (uu____46734, body, uu____46743)  in
                     FStar_Syntax_Syntax.Tm_abs uu____46715  in
                   FStar_Syntax_Syntax.mk uu____46714  in
                 uu____46707 FStar_Pervasives_Native.None
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
      | uu____46799 ->
          let uu____46808 =
            let uu____46815 =
              let uu____46816 =
                let uu____46831 = FStar_Syntax_Subst.close_binders bs  in
                let uu____46840 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____46831, uu____46840)  in
              FStar_Syntax_Syntax.Tm_arrow uu____46816  in
            FStar_Syntax_Syntax.mk uu____46815  in
          uu____46808 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____46889 =
        let uu____46890 = FStar_Syntax_Subst.compress t  in
        uu____46890.FStar_Syntax_Syntax.n  in
      match uu____46889 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____46920) ->
               let uu____46929 =
                 let uu____46930 = FStar_Syntax_Subst.compress tres  in
                 uu____46930.FStar_Syntax_Syntax.n  in
               (match uu____46929 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____46973 -> t)
           | uu____46974 -> t)
      | uu____46975 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____46993 =
        let uu____46994 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____46994 t.FStar_Syntax_Syntax.pos  in
      let uu____46995 =
        let uu____47002 =
          let uu____47003 =
            let uu____47010 =
              let uu____47013 =
                let uu____47014 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____47014]  in
              FStar_Syntax_Subst.close uu____47013 t  in
            (b, uu____47010)  in
          FStar_Syntax_Syntax.Tm_refine uu____47003  in
        FStar_Syntax_Syntax.mk uu____47002  in
      uu____46995 FStar_Pervasives_Native.None uu____46993
  
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
        let uu____47094 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____47094 with
         | (bs1,c1) ->
             let uu____47113 = is_total_comp c1  in
             if uu____47113
             then
               let uu____47128 = arrow_formals_comp (comp_result c1)  in
               (match uu____47128 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____47195;
           FStar_Syntax_Syntax.index = uu____47196;
           FStar_Syntax_Syntax.sort = s;_},uu____47198)
        ->
        let rec aux s1 k2 =
          let uu____47229 =
            let uu____47230 = FStar_Syntax_Subst.compress s1  in
            uu____47230.FStar_Syntax_Syntax.n  in
          match uu____47229 with
          | FStar_Syntax_Syntax.Tm_arrow uu____47245 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____47260;
                 FStar_Syntax_Syntax.index = uu____47261;
                 FStar_Syntax_Syntax.sort = s2;_},uu____47263)
              -> aux s2 k2
          | uu____47271 ->
              let uu____47272 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____47272)
           in
        aux s k1
    | uu____47287 ->
        let uu____47288 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____47288)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____47323 = arrow_formals_comp k  in
    match uu____47323 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____47465 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____47465 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____47489 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_47498  ->
                         match uu___414_47498 with
                         | FStar_Syntax_Syntax.DECREASES uu____47500 -> true
                         | uu____47504 -> false))
                  in
               (match uu____47489 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____47539 ->
                    let uu____47542 = is_total_comp c1  in
                    if uu____47542
                    then
                      let uu____47561 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____47561 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____47654;
             FStar_Syntax_Syntax.index = uu____47655;
             FStar_Syntax_Syntax.sort = k2;_},uu____47657)
          -> arrow_until_decreases k2
      | uu____47665 -> ([], FStar_Pervasives_Native.None)  in
    let uu____47686 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____47686 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____47740 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____47761 =
                 FStar_Common.tabulate n_univs (fun uu____47767  -> false)
                  in
               let uu____47770 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____47795  ->
                         match uu____47795 with
                         | (x,uu____47804) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____47761 uu____47770)
           in
        ((n_univs + (FStar_List.length bs)), uu____47740)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____47860 =
            let uu___1578_47861 = rc  in
            let uu____47862 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1578_47861.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____47862;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1578_47861.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____47860
      | uu____47871 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____47905 =
        let uu____47906 =
          let uu____47909 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____47909  in
        uu____47906.FStar_Syntax_Syntax.n  in
      match uu____47905 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____47955 = aux t2 what  in
          (match uu____47955 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____48027 -> ([], t1, abs_body_lcomp)  in
    let uu____48044 = aux t FStar_Pervasives_Native.None  in
    match uu____48044 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____48092 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____48092 with
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
                    | (FStar_Pervasives_Native.None ,uu____48255) -> def
                    | (uu____48266,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____48278) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _48294  ->
                                  FStar_Syntax_Syntax.U_name _48294))
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
            let uu____48376 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____48376 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____48411 ->
            let t' = arrow binders c  in
            let uu____48423 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____48423 with
             | (uvs1,t'1) ->
                 let uu____48444 =
                   let uu____48445 = FStar_Syntax_Subst.compress t'1  in
                   uu____48445.FStar_Syntax_Syntax.n  in
                 (match uu____48444 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____48494 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____48519 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____48530 -> false
  
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
      let uu____48593 =
        let uu____48594 = pre_typ t  in uu____48594.FStar_Syntax_Syntax.n  in
      match uu____48593 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____48599 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____48613 =
        let uu____48614 = pre_typ t  in uu____48614.FStar_Syntax_Syntax.n  in
      match uu____48613 with
      | FStar_Syntax_Syntax.Tm_fvar uu____48618 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____48620) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____48646) ->
          is_constructed_typ t1 lid
      | uu____48651 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____48664 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____48665 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____48666 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____48668) -> get_tycon t2
    | uu____48693 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____48701 =
      let uu____48702 = un_uinst t  in uu____48702.FStar_Syntax_Syntax.n  in
    match uu____48701 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____48707 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____48721 =
        let uu____48725 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____48725  in
      match uu____48721 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____48757 -> false
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
  fun uu____48776  ->
    let u =
      let uu____48782 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _48799  -> FStar_Syntax_Syntax.U_unif _48799)
        uu____48782
       in
    let uu____48800 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____48800, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____48813 = eq_tm a a'  in
      match uu____48813 with | Equal  -> true | uu____48816 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____48821 =
    let uu____48828 =
      let uu____48829 =
        let uu____48830 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____48830
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____48829  in
    FStar_Syntax_Syntax.mk uu____48828  in
  uu____48821 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____48942 =
            let uu____48945 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____48946 =
              let uu____48953 =
                let uu____48954 =
                  let uu____48971 =
                    let uu____48982 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____48991 =
                      let uu____49002 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____49002]  in
                    uu____48982 :: uu____48991  in
                  (tand, uu____48971)  in
                FStar_Syntax_Syntax.Tm_app uu____48954  in
              FStar_Syntax_Syntax.mk uu____48953  in
            uu____48946 FStar_Pervasives_Native.None uu____48945  in
          FStar_Pervasives_Native.Some uu____48942
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____49079 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____49080 =
          let uu____49087 =
            let uu____49088 =
              let uu____49105 =
                let uu____49116 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____49125 =
                  let uu____49136 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____49136]  in
                uu____49116 :: uu____49125  in
              (op_t, uu____49105)  in
            FStar_Syntax_Syntax.Tm_app uu____49088  in
          FStar_Syntax_Syntax.mk uu____49087  in
        uu____49080 FStar_Pervasives_Native.None uu____49079
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____49193 =
      let uu____49200 =
        let uu____49201 =
          let uu____49218 =
            let uu____49229 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____49229]  in
          (t_not, uu____49218)  in
        FStar_Syntax_Syntax.Tm_app uu____49201  in
      FStar_Syntax_Syntax.mk uu____49200  in
    uu____49193 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____49426 =
      let uu____49433 =
        let uu____49434 =
          let uu____49451 =
            let uu____49462 = FStar_Syntax_Syntax.as_arg e  in [uu____49462]
             in
          (b2t_v, uu____49451)  in
        FStar_Syntax_Syntax.Tm_app uu____49434  in
      FStar_Syntax_Syntax.mk uu____49433  in
    uu____49426 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49506 =
      let uu____49507 = unmeta t  in uu____49507.FStar_Syntax_Syntax.n  in
    match uu____49506 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____49512 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____49535 = is_t_true t1  in
      if uu____49535
      then t2
      else
        (let uu____49542 = is_t_true t2  in
         if uu____49542 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____49570 = is_t_true t1  in
      if uu____49570
      then t_true
      else
        (let uu____49577 = is_t_true t2  in
         if uu____49577 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____49606 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____49607 =
        let uu____49614 =
          let uu____49615 =
            let uu____49632 =
              let uu____49643 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____49652 =
                let uu____49663 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____49663]  in
              uu____49643 :: uu____49652  in
            (teq, uu____49632)  in
          FStar_Syntax_Syntax.Tm_app uu____49615  in
        FStar_Syntax_Syntax.mk uu____49614  in
      uu____49607 FStar_Pervasives_Native.None uu____49606
  
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
          let uu____49730 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____49731 =
            let uu____49738 =
              let uu____49739 =
                let uu____49756 =
                  let uu____49767 = FStar_Syntax_Syntax.iarg t  in
                  let uu____49776 =
                    let uu____49787 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____49796 =
                      let uu____49807 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____49807]  in
                    uu____49787 :: uu____49796  in
                  uu____49767 :: uu____49776  in
                (eq_inst, uu____49756)  in
              FStar_Syntax_Syntax.Tm_app uu____49739  in
            FStar_Syntax_Syntax.mk uu____49738  in
          uu____49731 FStar_Pervasives_Native.None uu____49730
  
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
        let uu____49884 =
          let uu____49891 =
            let uu____49892 =
              let uu____49909 =
                let uu____49920 = FStar_Syntax_Syntax.iarg t  in
                let uu____49929 =
                  let uu____49940 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____49949 =
                    let uu____49960 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____49960]  in
                  uu____49940 :: uu____49949  in
                uu____49920 :: uu____49929  in
              (t_has_type1, uu____49909)  in
            FStar_Syntax_Syntax.Tm_app uu____49892  in
          FStar_Syntax_Syntax.mk uu____49891  in
        uu____49884 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____50037 =
          let uu____50044 =
            let uu____50045 =
              let uu____50062 =
                let uu____50073 = FStar_Syntax_Syntax.iarg t  in
                let uu____50082 =
                  let uu____50093 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____50093]  in
                uu____50073 :: uu____50082  in
              (t_with_type1, uu____50062)  in
            FStar_Syntax_Syntax.Tm_app uu____50045  in
          FStar_Syntax_Syntax.mk uu____50044  in
        uu____50037 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____50140 =
    let uu____50147 =
      let uu____50148 =
        let uu____50155 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____50155, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____50148  in
    FStar_Syntax_Syntax.mk uu____50147  in
  uu____50140 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____50170 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____50183 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____50194 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____50170 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____50215  -> c0)
  
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
        let uu____50298 =
          let uu____50305 =
            let uu____50306 =
              let uu____50323 =
                let uu____50334 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____50343 =
                  let uu____50354 =
                    let uu____50363 =
                      let uu____50364 =
                        let uu____50365 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____50365]  in
                      abs uu____50364 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____50363  in
                  [uu____50354]  in
                uu____50334 :: uu____50343  in
              (fa, uu____50323)  in
            FStar_Syntax_Syntax.Tm_app uu____50306  in
          FStar_Syntax_Syntax.mk uu____50305  in
        uu____50298 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____50492 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____50492
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____50511 -> true
    | uu____50513 -> false
  
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
          let uu____50560 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____50560, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____50589 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____50589, FStar_Pervasives_Native.None, t2)  in
        let uu____50603 =
          let uu____50604 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____50604  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____50603
  
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
      let uu____50680 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____50683 =
        let uu____50694 = FStar_Syntax_Syntax.as_arg p  in [uu____50694]  in
      mk_app uu____50680 uu____50683
  
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
      let uu____50734 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____50737 =
        let uu____50748 = FStar_Syntax_Syntax.as_arg p  in [uu____50748]  in
      mk_app uu____50734 uu____50737
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____50783 = head_and_args t  in
    match uu____50783 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____50832 =
          let uu____50847 =
            let uu____50848 = FStar_Syntax_Subst.compress head3  in
            uu____50848.FStar_Syntax_Syntax.n  in
          (uu____50847, args)  in
        (match uu____50832 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____50867)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____50933 =
                    let uu____50938 =
                      let uu____50939 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____50939]  in
                    FStar_Syntax_Subst.open_term uu____50938 p  in
                  (match uu____50933 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____50996 -> failwith "impossible"  in
                       let uu____51004 =
                         let uu____51006 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____51006
                          in
                       if uu____51004
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____51022 -> FStar_Pervasives_Native.None)
         | uu____51025 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51056 = head_and_args t  in
    match uu____51056 with
    | (head1,args) ->
        let uu____51107 =
          let uu____51122 =
            let uu____51123 = FStar_Syntax_Subst.compress head1  in
            uu____51123.FStar_Syntax_Syntax.n  in
          (uu____51122, args)  in
        (match uu____51107 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____51145;
               FStar_Syntax_Syntax.vars = uu____51146;_},u::[]),(t1,uu____51149)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____51196 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51231 = head_and_args t  in
    match uu____51231 with
    | (head1,args) ->
        let uu____51282 =
          let uu____51297 =
            let uu____51298 = FStar_Syntax_Subst.compress head1  in
            uu____51298.FStar_Syntax_Syntax.n  in
          (uu____51297, args)  in
        (match uu____51282 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____51320;
               FStar_Syntax_Syntax.vars = uu____51321;_},u::[]),(t1,uu____51324)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____51371 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____51399 =
      let uu____51416 = unmeta t  in head_and_args uu____51416  in
    match uu____51399 with
    | (head1,uu____51419) ->
        let uu____51444 =
          let uu____51445 = un_uinst head1  in
          uu____51445.FStar_Syntax_Syntax.n  in
        (match uu____51444 with
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
         | uu____51450 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____51470 =
      let uu____51483 =
        let uu____51484 = FStar_Syntax_Subst.compress t  in
        uu____51484.FStar_Syntax_Syntax.n  in
      match uu____51483 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____51614 =
            let uu____51625 =
              let uu____51626 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____51626  in
            (b, uu____51625)  in
          FStar_Pervasives_Native.Some uu____51614
      | uu____51643 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____51470
      (fun uu____51681  ->
         match uu____51681 with
         | (b,c) ->
             let uu____51718 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____51718 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____51781 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____51818 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____51818
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____51870 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____51913 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____51954 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____51993) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____52005) ->
          unmeta_monadic t
      | uu____52018 -> f2  in
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
      let aux f2 uu____52114 =
        match uu____52114 with
        | (lid,arity) ->
            let uu____52123 =
              let uu____52140 = unmeta_monadic f2  in
              head_and_args uu____52140  in
            (match uu____52123 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____52170 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____52170
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____52246 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____52246)
      | uu____52259 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____52326 = head_and_args t1  in
        match uu____52326 with
        | (t2,args) ->
            let uu____52381 = un_uinst t2  in
            let uu____52382 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____52423  ->
                      match uu____52423 with
                      | (t3,imp) ->
                          let uu____52442 = unascribe t3  in
                          (uu____52442, imp)))
               in
            (uu____52381, uu____52382)
         in
      let rec aux qopt out t1 =
        let uu____52493 = let uu____52517 = flat t1  in (qopt, uu____52517)
           in
        match uu____52493 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____52557;
                 FStar_Syntax_Syntax.vars = uu____52558;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____52561);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____52562;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____52563;_},uu____52564)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____52666;
                 FStar_Syntax_Syntax.vars = uu____52667;_},uu____52668::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____52671);
                  FStar_Syntax_Syntax.pos = uu____52672;
                  FStar_Syntax_Syntax.vars = uu____52673;_},uu____52674)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____52791;
               FStar_Syntax_Syntax.vars = uu____52792;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____52795);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____52796;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____52797;_},uu____52798)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____52891 =
              let uu____52895 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____52895  in
            aux uu____52891 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____52905;
               FStar_Syntax_Syntax.vars = uu____52906;_},uu____52907::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____52910);
                FStar_Syntax_Syntax.pos = uu____52911;
                FStar_Syntax_Syntax.vars = uu____52912;_},uu____52913)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____53022 =
              let uu____53026 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____53026  in
            aux uu____53022 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____53036) ->
            let bs = FStar_List.rev out  in
            let uu____53089 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____53089 with
             | (bs1,t2) ->
                 let uu____53098 = patterns t2  in
                 (match uu____53098 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____53148 -> FStar_Pervasives_Native.None  in
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
      let uu____53240 = un_squash t  in
      FStar_Util.bind_opt uu____53240
        (fun t1  ->
           let uu____53256 = head_and_args' t1  in
           match uu____53256 with
           | (hd1,args) ->
               let uu____53295 =
                 let uu____53301 =
                   let uu____53302 = un_uinst hd1  in
                   uu____53302.FStar_Syntax_Syntax.n  in
                 (uu____53301, (FStar_List.length args))  in
               (match uu____53295 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53318) when
                    (_53318 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53321) when
                    (_53321 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53324) when
                    (_53324 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53327) when
                    (_53327 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53330) when
                    (_53330 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53333) when
                    (_53333 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53336) when
                    (_53336 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_53339) when
                    (_53339 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____53340 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____53370 = un_squash t  in
      FStar_Util.bind_opt uu____53370
        (fun t1  ->
           let uu____53385 = arrow_one t1  in
           match uu____53385 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____53400 =
                 let uu____53402 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____53402  in
               if uu____53400
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____53412 = comp_to_comp_typ_nouniv c  in
                    uu____53412.FStar_Syntax_Syntax.result_typ  in
                  let uu____53413 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____53413
                  then
                    let uu____53420 = patterns q  in
                    match uu____53420 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____53483 =
                       let uu____53484 =
                         let uu____53489 =
                           let uu____53490 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____53501 =
                             let uu____53512 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____53512]  in
                           uu____53490 :: uu____53501  in
                         (FStar_Parser_Const.imp_lid, uu____53489)  in
                       BaseConn uu____53484  in
                     FStar_Pervasives_Native.Some uu____53483))
           | uu____53545 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____53553 = un_squash t  in
      FStar_Util.bind_opt uu____53553
        (fun t1  ->
           let uu____53584 = head_and_args' t1  in
           match uu____53584 with
           | (hd1,args) ->
               let uu____53623 =
                 let uu____53638 =
                   let uu____53639 = un_uinst hd1  in
                   uu____53639.FStar_Syntax_Syntax.n  in
                 (uu____53638, args)  in
               (match uu____53623 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____53656)::(a2,uu____53658)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____53709 =
                      let uu____53710 = FStar_Syntax_Subst.compress a2  in
                      uu____53710.FStar_Syntax_Syntax.n  in
                    (match uu____53709 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____53717) ->
                         let uu____53752 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____53752 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____53805 -> failwith "impossible"  in
                              let uu____53813 = patterns q1  in
                              (match uu____53813 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____53874 -> FStar_Pervasives_Native.None)
                | uu____53875 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____53898 = destruct_sq_forall phi  in
          (match uu____53898 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _53908  -> FStar_Pervasives_Native.Some _53908)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____53915 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____53921 = destruct_sq_exists phi  in
          (match uu____53921 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _53931  -> FStar_Pervasives_Native.Some _53931)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____53938 -> f1)
      | uu____53941 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____53945 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____53945
      (fun uu____53950  ->
         let uu____53951 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____53951
           (fun uu____53956  ->
              let uu____53957 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____53957
                (fun uu____53962  ->
                   let uu____53963 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____53963
                     (fun uu____53968  ->
                        let uu____53969 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____53969
                          (fun uu____53973  -> FStar_Pervasives_Native.None)))))
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____53991 =
            let uu____53996 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____53996  in
          let uu____53997 =
            let uu____53998 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____53998  in
          let uu____54001 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____53991 a.FStar_Syntax_Syntax.action_univs uu____53997
            FStar_Parser_Const.effect_Tot_lid uu____54001 [] pos
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
    let uu____54027 =
      let uu____54034 =
        let uu____54035 =
          let uu____54052 =
            let uu____54063 = FStar_Syntax_Syntax.as_arg t  in [uu____54063]
             in
          (reify_1, uu____54052)  in
        FStar_Syntax_Syntax.Tm_app uu____54035  in
      FStar_Syntax_Syntax.mk uu____54034  in
    uu____54027 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____54115 =
        let uu____54122 =
          let uu____54123 =
            let uu____54124 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____54124  in
          FStar_Syntax_Syntax.Tm_constant uu____54123  in
        FStar_Syntax_Syntax.mk uu____54122  in
      uu____54115 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____54126 =
      let uu____54133 =
        let uu____54134 =
          let uu____54151 =
            let uu____54162 = FStar_Syntax_Syntax.as_arg t  in [uu____54162]
             in
          (reflect_, uu____54151)  in
        FStar_Syntax_Syntax.Tm_app uu____54134  in
      FStar_Syntax_Syntax.mk uu____54133  in
    uu____54126 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____54206 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____54231 = unfold_lazy i  in delta_qualifier uu____54231
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____54233 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____54234 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____54235 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____54258 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____54271 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____54272 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____54279 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____54280 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____54296) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____54301;
           FStar_Syntax_Syntax.index = uu____54302;
           FStar_Syntax_Syntax.sort = t2;_},uu____54304)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____54313) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____54319,uu____54320) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____54362) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____54387,t2,uu____54389) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____54414,t2) -> delta_qualifier t2
  
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
    let uu____54453 = delta_qualifier t  in incr_delta_depth uu____54453
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____54461 =
      let uu____54462 = FStar_Syntax_Subst.compress t  in
      uu____54462.FStar_Syntax_Syntax.n  in
    match uu____54461 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____54467 -> false
  
let rec apply_last :
  'Auu____54476 .
    ('Auu____54476 -> 'Auu____54476) ->
      'Auu____54476 Prims.list -> 'Auu____54476 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____54502 = f a  in [uu____54502]
      | x::xs -> let uu____54507 = apply_last f xs  in x :: uu____54507
  
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
          let uu____54562 =
            let uu____54569 =
              let uu____54570 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____54570  in
            FStar_Syntax_Syntax.mk uu____54569  in
          uu____54562 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____54584 =
            let uu____54589 =
              let uu____54590 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____54590
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____54589 args  in
          uu____54584 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____54604 =
            let uu____54609 =
              let uu____54610 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____54610
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____54609 args  in
          uu____54604 FStar_Pervasives_Native.None pos  in
        let uu____54611 =
          let uu____54612 =
            let uu____54613 = FStar_Syntax_Syntax.iarg typ  in [uu____54613]
             in
          nil uu____54612 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____54647 =
                 let uu____54648 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____54657 =
                   let uu____54668 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____54677 =
                     let uu____54688 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____54688]  in
                   uu____54668 :: uu____54677  in
                 uu____54648 :: uu____54657  in
               cons1 uu____54647 t.FStar_Syntax_Syntax.pos) l uu____54611
  
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
        | uu____54797 -> false
  
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
          | uu____54911 -> false
  
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
        | uu____55077 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____55115 = FStar_ST.op_Bang debug_term_eq  in
          if uu____55115
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
        let t11 = let uu____55337 = unmeta_safe t1  in canon_app uu____55337
           in
        let t21 = let uu____55343 = unmeta_safe t2  in canon_app uu____55343
           in
        let uu____55346 =
          let uu____55351 =
            let uu____55352 =
              let uu____55355 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____55355  in
            uu____55352.FStar_Syntax_Syntax.n  in
          let uu____55356 =
            let uu____55357 =
              let uu____55360 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____55360  in
            uu____55357.FStar_Syntax_Syntax.n  in
          (uu____55351, uu____55356)  in
        match uu____55346 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____55362,uu____55363) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____55372,FStar_Syntax_Syntax.Tm_uinst uu____55373) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____55382,uu____55383) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____55408,FStar_Syntax_Syntax.Tm_delayed uu____55409) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____55434,uu____55435) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____55464,FStar_Syntax_Syntax.Tm_ascribed uu____55465) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____55504 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____55504
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____55509 = FStar_Const.eq_const c1 c2  in
            check "const" uu____55509
        | (FStar_Syntax_Syntax.Tm_type
           uu____55512,FStar_Syntax_Syntax.Tm_type uu____55513) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____55571 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____55571) &&
              (let uu____55581 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____55581)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____55630 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____55630) &&
              (let uu____55640 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____55640)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____55658 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____55658)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____55715 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____55715) &&
              (let uu____55719 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____55719)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____55808 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____55808) &&
              (let uu____55812 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____55812)
        | (FStar_Syntax_Syntax.Tm_lazy uu____55829,uu____55830) ->
            let uu____55831 =
              let uu____55833 = unlazy t11  in
              term_eq_dbg dbg uu____55833 t21  in
            check "lazy_l" uu____55831
        | (uu____55835,FStar_Syntax_Syntax.Tm_lazy uu____55836) ->
            let uu____55837 =
              let uu____55839 = unlazy t21  in
              term_eq_dbg dbg t11 uu____55839  in
            check "lazy_r" uu____55837
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____55884 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____55884))
              &&
              (let uu____55888 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____55888)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____55892),FStar_Syntax_Syntax.Tm_uvar (u2,uu____55894)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____55952 =
               let uu____55954 = eq_quoteinfo qi1 qi2  in uu____55954 = Equal
                in
             check "tm_quoted qi" uu____55952) &&
              (let uu____55957 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____55957)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____55987 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____55987) &&
                   (let uu____55991 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____55991)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____56010 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____56010) &&
                    (let uu____56014 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____56014))
                   &&
                   (let uu____56018 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____56018)
             | uu____56021 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____56027) -> fail "unk"
        | (uu____56029,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____56031,uu____56032) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____56034,uu____56035) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____56037,uu____56038) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____56040,uu____56041) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____56043,uu____56044) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____56046,uu____56047) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____56067,uu____56068) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____56084,uu____56085) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____56093,uu____56094) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____56112,uu____56113) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____56137,uu____56138) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____56153,uu____56154) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____56168,uu____56169) ->
            fail "bottom"
        | (uu____56177,FStar_Syntax_Syntax.Tm_bvar uu____56178) ->
            fail "bottom"
        | (uu____56180,FStar_Syntax_Syntax.Tm_name uu____56181) ->
            fail "bottom"
        | (uu____56183,FStar_Syntax_Syntax.Tm_fvar uu____56184) ->
            fail "bottom"
        | (uu____56186,FStar_Syntax_Syntax.Tm_constant uu____56187) ->
            fail "bottom"
        | (uu____56189,FStar_Syntax_Syntax.Tm_type uu____56190) ->
            fail "bottom"
        | (uu____56192,FStar_Syntax_Syntax.Tm_abs uu____56193) ->
            fail "bottom"
        | (uu____56213,FStar_Syntax_Syntax.Tm_arrow uu____56214) ->
            fail "bottom"
        | (uu____56230,FStar_Syntax_Syntax.Tm_refine uu____56231) ->
            fail "bottom"
        | (uu____56239,FStar_Syntax_Syntax.Tm_app uu____56240) ->
            fail "bottom"
        | (uu____56258,FStar_Syntax_Syntax.Tm_match uu____56259) ->
            fail "bottom"
        | (uu____56283,FStar_Syntax_Syntax.Tm_let uu____56284) ->
            fail "bottom"
        | (uu____56299,FStar_Syntax_Syntax.Tm_uvar uu____56300) ->
            fail "bottom"
        | (uu____56314,FStar_Syntax_Syntax.Tm_meta uu____56315) ->
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
               let uu____56350 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____56350)
          (fun q1  ->
             fun q2  ->
               let uu____56362 =
                 let uu____56364 = eq_aqual q1 q2  in uu____56364 = Equal  in
               check "arg qual" uu____56362) a1 a2

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
               let uu____56389 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____56389)
          (fun q1  ->
             fun q2  ->
               let uu____56401 =
                 let uu____56403 = eq_aqual q1 q2  in uu____56403 = Equal  in
               check "binder qual" uu____56401) b1 b2

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
        ((let uu____56423 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____56423) &&
           (let uu____56427 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____56427))
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
    fun uu____56437  ->
      fun uu____56438  ->
        match (uu____56437, uu____56438) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____56565 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____56565) &&
               (let uu____56569 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____56569))
              &&
              (let uu____56573 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____56615 -> false  in
               check "branch when" uu____56573)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____56636 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____56636) &&
           (let uu____56645 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____56645))
          &&
          (let uu____56649 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____56649)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____56666 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____56666 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____56720 ->
        let uu____56743 =
          let uu____56745 = FStar_Syntax_Subst.compress t  in
          sizeof uu____56745  in
        (Prims.parse_int "1") + uu____56743
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____56748 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____56748
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____56752 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____56752
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____56761 = sizeof t1  in (FStar_List.length us) + uu____56761
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____56765) ->
        let uu____56790 = sizeof t1  in
        let uu____56792 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____56807  ->
                 match uu____56807 with
                 | (bv,uu____56817) ->
                     let uu____56822 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____56822) (Prims.parse_int "0") bs
           in
        uu____56790 + uu____56792
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____56851 = sizeof hd1  in
        let uu____56853 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____56868  ->
                 match uu____56868 with
                 | (arg,uu____56878) ->
                     let uu____56883 = sizeof arg  in acc + uu____56883)
            (Prims.parse_int "0") args
           in
        uu____56851 + uu____56853
    | uu____56886 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____56900 =
        let uu____56901 = un_uinst t  in uu____56901.FStar_Syntax_Syntax.n
         in
      match uu____56900 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____56906 -> false
  
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
        let uu____56955 = FStar_Options.set_options t s  in
        match uu____56955 with
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
          ((let uu____56972 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____56972 (fun a1  -> ()));
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
          let uu____56987 = FStar_Options.internal_pop ()  in
          if uu____56987
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
    | FStar_Syntax_Syntax.Tm_delayed uu____57019 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____57046 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____57061 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____57062 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____57063 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____57072) ->
        let uu____57097 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____57097 with
         | (bs1,t2) ->
             let uu____57106 =
               FStar_List.collect
                 (fun uu____57118  ->
                    match uu____57118 with
                    | (b,uu____57128) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____57133 = unbound_variables t2  in
             FStar_List.append uu____57106 uu____57133)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____57158 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____57158 with
         | (bs1,c1) ->
             let uu____57167 =
               FStar_List.collect
                 (fun uu____57179  ->
                    match uu____57179 with
                    | (b,uu____57189) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____57194 = unbound_variables_comp c1  in
             FStar_List.append uu____57167 uu____57194)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____57203 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____57203 with
         | (bs,t2) ->
             let uu____57226 =
               FStar_List.collect
                 (fun uu____57238  ->
                    match uu____57238 with
                    | (b1,uu____57248) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____57253 = unbound_variables t2  in
             FStar_List.append uu____57226 uu____57253)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____57282 =
          FStar_List.collect
            (fun uu____57296  ->
               match uu____57296 with
               | (x,uu____57308) -> unbound_variables x) args
           in
        let uu____57317 = unbound_variables t1  in
        FStar_List.append uu____57282 uu____57317
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____57358 = unbound_variables t1  in
        let uu____57361 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____57376 = FStar_Syntax_Subst.open_branch br  in
                  match uu____57376 with
                  | (p,wopt,t2) ->
                      let uu____57398 = unbound_variables t2  in
                      let uu____57401 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____57398 uu____57401))
           in
        FStar_List.append uu____57358 uu____57361
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____57415) ->
        let uu____57456 = unbound_variables t1  in
        let uu____57459 =
          let uu____57462 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____57493 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____57462 uu____57493  in
        FStar_List.append uu____57456 uu____57459
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____57534 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____57537 =
          let uu____57540 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____57543 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____57548 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____57550 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____57550 with
                 | (uu____57571,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____57540 uu____57543  in
        FStar_List.append uu____57534 uu____57537
    | FStar_Syntax_Syntax.Tm_let ((uu____57573,lbs),t1) ->
        let uu____57593 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____57593 with
         | (lbs1,t2) ->
             let uu____57608 = unbound_variables t2  in
             let uu____57611 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____57618 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____57621 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____57618 uu____57621) lbs1
                in
             FStar_List.append uu____57608 uu____57611)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____57638 = unbound_variables t1  in
        let uu____57641 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____57680  ->
                      match uu____57680 with
                      | (a,uu____57692) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____57701,uu____57702,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____57708,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____57714 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____57723 -> []
          | FStar_Syntax_Syntax.Meta_named uu____57724 -> []  in
        FStar_List.append uu____57638 uu____57641

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____57731) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____57741) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____57751 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____57754 =
          FStar_List.collect
            (fun uu____57768  ->
               match uu____57768 with
               | (a,uu____57780) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____57751 uu____57754

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
            let uu____57895 = head_and_args h  in
            (match uu____57895 with
             | (head1,args) ->
                 let uu____57956 =
                   let uu____57957 = FStar_Syntax_Subst.compress head1  in
                   uu____57957.FStar_Syntax_Syntax.n  in
                 (match uu____57956 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____58010 -> aux (h :: acc) t))
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
      let uu____58034 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____58034 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2926_58076 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2926_58076.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2926_58076.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2926_58076.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2926_58076.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____58084 =
      let uu____58085 = FStar_Syntax_Subst.compress t  in
      uu____58085.FStar_Syntax_Syntax.n  in
    match uu____58084 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____58089,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____58117)::uu____58118 ->
                  let pats' = unmeta pats  in
                  let uu____58178 = head_and_args pats'  in
                  (match uu____58178 with
                   | (head1,uu____58197) ->
                       let uu____58222 =
                         let uu____58223 = un_uinst head1  in
                         uu____58223.FStar_Syntax_Syntax.n  in
                       (match uu____58222 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____58228 -> false))
              | uu____58230 -> false)
         | uu____58242 -> false)
    | uu____58244 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____58260 =
      let uu____58277 = unmeta e  in head_and_args uu____58277  in
    match uu____58260 with
    | (head1,args) ->
        let uu____58308 =
          let uu____58323 =
            let uu____58324 = un_uinst head1  in
            uu____58324.FStar_Syntax_Syntax.n  in
          (uu____58323, args)  in
        (match uu____58308 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____58342) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____58366::(hd1,uu____58368)::(tl1,uu____58370)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____58437 =
               let uu____58440 =
                 let uu____58443 = list_elements tl1  in
                 FStar_Util.must uu____58443  in
               hd1 :: uu____58440  in
             FStar_Pervasives_Native.Some uu____58437
         | uu____58452 -> FStar_Pervasives_Native.None)
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____58481 =
      let uu____58482 = FStar_Syntax_Subst.compress t  in
      uu____58482.FStar_Syntax_Syntax.n  in
    match uu____58481 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____58489) ->
        let uu____58524 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____58524 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____58558 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____58558
             then
               let uu____58565 =
                 let uu____58576 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____58576]  in
               mk_app t uu____58565
             else e1)
    | uu____58603 ->
        let uu____58604 =
          let uu____58615 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____58615]  in
        mk_app t uu____58604
  
let (smt_lemma_as_forall :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.universe Prims.list)
      -> FStar_Syntax_Syntax.term)
  =
  fun t  ->
    fun universe_of_binders  ->
      let list_elements1 e =
        let uu____58670 = list_elements e  in
        match uu____58670 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____58701 =
          let uu____58718 = unmeta p  in
          FStar_All.pipe_right uu____58718 head_and_args  in
        match uu____58701 with
        | (head1,args) ->
            let uu____58769 =
              let uu____58784 =
                let uu____58785 = un_uinst head1  in
                uu____58785.FStar_Syntax_Syntax.n  in
              (uu____58784, args)  in
            (match uu____58769 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____58807,uu____58808)::arg::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> arg
             | uu____58860 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____58915 =
            let uu____58932 = unmeta t1  in
            FStar_All.pipe_right uu____58932 head_and_args  in
          match uu____58915 with
          | (head1,args) ->
              let uu____58979 =
                let uu____58994 =
                  let uu____58995 = un_uinst head1  in
                  uu____58995.FStar_Syntax_Syntax.n  in
                (uu____58994, args)  in
              (match uu____58979 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____59014)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____59051 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____59081 = smt_pat_or1 t1  in
            (match uu____59081 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____59103 = list_elements1 e  in
                 FStar_All.pipe_right uu____59103
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____59133 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____59133
                           (FStar_List.map one_pat)))
             | uu____59156 ->
                 let uu____59161 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____59161])
        | uu____59212 ->
            let uu____59215 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____59215]
         in
      let uu____59266 =
        let uu____59299 =
          let uu____59300 = FStar_Syntax_Subst.compress t  in
          uu____59300.FStar_Syntax_Syntax.n  in
        match uu____59299 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____59357 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____59357 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____59428;
                        FStar_Syntax_Syntax.effect_name = uu____59429;
                        FStar_Syntax_Syntax.result_typ = uu____59430;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____59432)::(post,uu____59434)::(pats,uu____59436)::[];
                        FStar_Syntax_Syntax.flags = uu____59437;_}
                      ->
                      let uu____59498 = lemma_pats pats  in
                      (binders1, pre, post, uu____59498)
                  | uu____59535 -> failwith "impos"))
        | uu____59569 -> failwith "Impos"  in
      match uu____59266 with
      | (binders,pre,post,patterns) ->
          let post1 = unthunk_lemma_post post  in
          let body =
            let uu____59661 =
              let uu____59668 =
                let uu____59669 =
                  let uu____59676 = mk_imp pre post1  in
                  (uu____59676, (FStar_Syntax_Syntax.Meta_pattern patterns))
                   in
                FStar_Syntax_Syntax.Tm_meta uu____59669  in
              FStar_Syntax_Syntax.mk uu____59668  in
            uu____59661 FStar_Pervasives_Native.None
              t.FStar_Syntax_Syntax.pos
             in
          let quant =
            let uu____59682 = universe_of_binders binders  in
            FStar_List.fold_right2
              (fun b  ->
                 fun u  ->
                   fun out  ->
                     mk_forall u (FStar_Pervasives_Native.fst b) out) binders
              uu____59682 body
             in
          quant
  