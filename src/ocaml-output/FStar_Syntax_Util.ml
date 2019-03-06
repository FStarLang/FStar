open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____44954 = FStar_ST.op_Bang tts_f  in
    match uu____44954 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____45018 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____45018 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____45025 =
      let uu____45028 =
        let uu____45031 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____45031]  in
      FStar_List.append lid.FStar_Ident.ns uu____45028  in
    FStar_Ident.lid_of_ids uu____45025
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____45049 .
    (FStar_Syntax_Syntax.bv * 'Auu____45049) ->
      (FStar_Syntax_Syntax.term * 'Auu____45049)
  =
  fun uu____45062  ->
    match uu____45062 with
    | (b,imp) ->
        let uu____45069 = FStar_Syntax_Syntax.bv_to_name b  in
        (uu____45069, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____45121 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____45121
            then []
            else
              (let uu____45140 = arg_of_non_null_binder b  in [uu____45140])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____45175 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____45257 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45257
              then
                let b1 =
                  let uu____45283 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____45283, (FStar_Pervasives_Native.snd b))  in
                let uu____45290 = arg_of_non_null_binder b1  in
                (b1, uu____45290)
              else
                (let uu____45313 = arg_of_non_null_binder b  in
                 (b, uu____45313))))
       in
    FStar_All.pipe_right uu____45175 FStar_List.unzip
  
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
              let uu____45447 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45447
              then
                let uu____45456 = b  in
                match uu____45456 with
                | (a,imp) ->
                    let b1 =
                      let uu____45476 =
                        let uu____45478 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____45478  in
                      FStar_Ident.id_of_text uu____45476  in
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
        let uu____45523 =
          let uu____45530 =
            let uu____45531 =
              let uu____45546 = name_binders binders  in (uu____45546, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____45531  in
          FStar_Syntax_Syntax.mk uu____45530  in
        uu____45523 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____45568 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45605  ->
            match uu____45605 with
            | (t,imp) ->
                let uu____45616 =
                  let uu____45617 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____45617
                   in
                (uu____45616, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45672  ->
            match uu____45672 with
            | (t,imp) ->
                let uu____45689 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____45689, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____45702 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____45702
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____45714 . 'Auu____45714 -> 'Auu____45714 Prims.list =
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
          (fun uu____45840  ->
             fun uu____45841  ->
               match (uu____45840, uu____45841) with
               | ((x,uu____45867),(y,uu____45869)) ->
                   let uu____45890 =
                     let uu____45897 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____45897)  in
                   FStar_Syntax_Syntax.NT uu____45890) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____45913) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45919,uu____45920) ->
        unmeta e2
    | uu____45961 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____45975 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____45982 -> e1
         | uu____45991 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45993,uu____45994) ->
        unmeta_safe e2
    | uu____46035 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____46054 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____46057 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____46071 = univ_kernel u1  in
        (match uu____46071 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____46088 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____46097 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____46112 = univ_kernel u  in
    FStar_Pervasives_Native.snd uu____46112
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____46132,uu____46133) ->
          failwith "Impossible: compare_univs"
      | (uu____46137,FStar_Syntax_Syntax.U_bvar uu____46138) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____46143) ->
          ~- (Prims.parse_int "1")
      | (uu____46145,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____46148) -> ~- (Prims.parse_int "1")
      | (uu____46150,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____46154,FStar_Syntax_Syntax.U_unif
         uu____46155) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____46165,FStar_Syntax_Syntax.U_name
         uu____46166) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____46194 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____46196 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____46194 - uu____46196
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____46232 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____46232
                 (fun uu____46248  ->
                    match uu____46248 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____46276,uu____46277) ->
          ~- (Prims.parse_int "1")
      | (uu____46281,FStar_Syntax_Syntax.U_max uu____46282) ->
          (Prims.parse_int "1")
      | uu____46286 ->
          let uu____46291 = univ_kernel u1  in
          (match uu____46291 with
           | (k1,n1) ->
               let uu____46302 = univ_kernel u2  in
               (match uu____46302 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____46333 = compare_univs u1 u2  in
      uu____46333 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____46352 =
        let uu____46353 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____46353;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____46352
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____46373 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____46382 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____46405 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____46414 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____46441 =
          let uu____46442 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46442  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46441;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____46471 =
          let uu____46472 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46472  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46471;
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
      let uu___631_46508 = c  in
      let uu____46509 =
        let uu____46510 =
          let uu___633_46511 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___633_46511.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___633_46511.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___633_46511.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___633_46511.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____46510  in
      {
        FStar_Syntax_Syntax.n = uu____46509;
        FStar_Syntax_Syntax.pos = (uu___631_46508.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___631_46508.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____46537 -> c
        | FStar_Syntax_Syntax.GTotal uu____46546 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___645_46557 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___645_46557.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___645_46557.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___645_46557.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___645_46557.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___648_46558 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___648_46558.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___648_46558.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____46561  ->
           let uu____46562 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____46562)
  
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
    | uu____46602 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____46617 -> true
    | FStar_Syntax_Syntax.GTotal uu____46627 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___402_46652  ->
               match uu___402_46652 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46656 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___403_46669  ->
               match uu___403_46669 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46673 -> false)))
  
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
            (fun uu___404_46686  ->
               match uu___404_46686 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46690 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___405_46707  ->
            match uu___405_46707 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46711 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___406_46724  ->
            match uu___406_46724 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46728 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____46760 -> true
    | FStar_Syntax_Syntax.GTotal uu____46770 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___407_46785  ->
                   match uu___407_46785 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____46788 -> false)))
  
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
            (fun uu___408_46833  ->
               match uu___408_46833 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____46836 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46852 =
      let uu____46853 = FStar_Syntax_Subst.compress t  in
      uu____46853.FStar_Syntax_Syntax.n  in
    match uu____46852 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46857,c) -> is_pure_or_ghost_comp c
    | uu____46879 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____46894 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46903 =
      let uu____46904 = FStar_Syntax_Subst.compress t  in
      uu____46904.FStar_Syntax_Syntax.n  in
    match uu____46903 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46908,c) -> is_lemma_comp c
    | uu____46930 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____46938 =
      let uu____46939 = FStar_Syntax_Subst.compress t  in
      uu____46939.FStar_Syntax_Syntax.n  in
    match uu____46938 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____46943) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____46969) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____47006,t1,uu____47008) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____47034,uu____47035) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____47077) -> head_of t1
    | uu____47082 -> t
  
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
    | uu____47160 -> (t1, [])
  
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
        let uu____47242 = head_and_args' head1  in
        (match uu____47242 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____47311 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____47338) ->
        FStar_Syntax_Subst.compress t2
    | uu____47343 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____47351 =
      let uu____47352 = FStar_Syntax_Subst.compress t  in
      uu____47352.FStar_Syntax_Syntax.n  in
    match uu____47351 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____47356,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____47384)::uu____47385 ->
                  let pats' = unmeta pats  in
                  let uu____47445 = head_and_args pats'  in
                  (match uu____47445 with
                   | (head1,uu____47464) ->
                       let uu____47489 =
                         let uu____47490 = un_uinst head1  in
                         uu____47490.FStar_Syntax_Syntax.n  in
                       (match uu____47489 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____47495 -> false))
              | uu____47497 -> false)
         | uu____47509 -> false)
    | uu____47511 -> false
  
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
                (fun uu___409_47530  ->
                   match uu___409_47530 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____47533 -> false)))
    | uu____47535 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____47552) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____47562) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____47591 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____47600 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___827_47612 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___827_47612.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___827_47612.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___827_47612.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___827_47612.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____47626  ->
           let uu____47627 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____47627 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_47645  ->
            match uu___410_47645 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____47649 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____47657 -> []
    | FStar_Syntax_Syntax.GTotal uu____47674 -> []
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
    | uu____47718 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____47728,uu____47729) ->
        unascribe e2
    | uu____47770 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____47823,uu____47824) ->
          ascribe t' k
      | uu____47865 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____47892 =
      let uu____47901 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____47901  in
    uu____47892 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47957 =
      let uu____47958 = FStar_Syntax_Subst.compress t  in
      uu____47958.FStar_Syntax_Syntax.n  in
    match uu____47957 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____47962 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____47962
    | uu____47963 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47970 =
      let uu____47971 = FStar_Syntax_Subst.compress t  in
      uu____47971.FStar_Syntax_Syntax.n  in
    match uu____47970 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____47975 ->
             let uu____47984 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____47984
         | uu____47985 -> t)
    | uu____47986 -> t
  
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
      | uu____48010 -> false
  
let rec unlazy_as_t :
  'Auu____48023 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____48023
  =
  fun k  ->
    fun t  ->
      let uu____48034 =
        let uu____48035 = FStar_Syntax_Subst.compress t  in
        uu____48035.FStar_Syntax_Syntax.n  in
      match uu____48034 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____48040;
            FStar_Syntax_Syntax.rng = uu____48041;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____48044 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____48085 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____48085;
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
    let uu____48098 =
      let uu____48113 = unascribe t  in head_and_args' uu____48113  in
    match uu____48098 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____48147 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____48158 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____48169 -> false
  
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
      | (NotEqual ,uu____48219) -> NotEqual
      | (uu____48220,NotEqual ) -> NotEqual
      | (Unknown ,uu____48221) -> Unknown
      | (uu____48222,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_48343 = if uu___411_48343 then Equal else Unknown
         in
      let equal_iff uu___412_48354 =
        if uu___412_48354 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____48375 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____48397 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____48397
        then
          let uu____48401 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____48478  ->
                    match uu____48478 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____48519 = eq_tm a1 a2  in
                        eq_inj acc uu____48519) Equal) uu____48401
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____48533 =
          let uu____48550 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____48550 head_and_args  in
        match uu____48533 with
        | (head1,args1) ->
            let uu____48603 =
              let uu____48620 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____48620 head_and_args  in
            (match uu____48603 with
             | (head2,args2) ->
                 let uu____48673 =
                   let uu____48678 =
                     let uu____48679 = un_uinst head1  in
                     uu____48679.FStar_Syntax_Syntax.n  in
                   let uu____48682 =
                     let uu____48683 = un_uinst head2  in
                     uu____48683.FStar_Syntax_Syntax.n  in
                   (uu____48678, uu____48682)  in
                 (match uu____48673 with
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
                  | uu____48710 -> FStar_Pervasives_Native.None))
         in
      let uu____48723 =
        let uu____48728 =
          let uu____48729 = unmeta t11  in uu____48729.FStar_Syntax_Syntax.n
           in
        let uu____48732 =
          let uu____48733 = unmeta t21  in uu____48733.FStar_Syntax_Syntax.n
           in
        (uu____48728, uu____48732)  in
      match uu____48723 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____48739,uu____48740) ->
          let uu____48741 = unlazy t11  in eq_tm uu____48741 t21
      | (uu____48742,FStar_Syntax_Syntax.Tm_lazy uu____48743) ->
          let uu____48744 = unlazy t21  in eq_tm t11 uu____48744
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____48747 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____48771 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____48771
            (fun uu____48819  ->
               match uu____48819 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____48834 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____48834
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____48848 = eq_tm f g  in
          eq_and uu____48848
            (fun uu____48851  ->
               let uu____48852 = eq_univs_list us vs  in equal_if uu____48852)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48854),uu____48855) -> Unknown
      | (uu____48856,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48857)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____48860 = FStar_Const.eq_const c d  in
          equal_iff uu____48860
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____48863)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____48865))) ->
          let uu____48894 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____48894
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____48948 =
            let uu____48953 =
              let uu____48954 = un_uinst h1  in
              uu____48954.FStar_Syntax_Syntax.n  in
            let uu____48957 =
              let uu____48958 = un_uinst h2  in
              uu____48958.FStar_Syntax_Syntax.n  in
            (uu____48953, uu____48957)  in
          (match uu____48948 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____48964 =
                    let uu____48966 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____48966  in
                  FStar_List.mem uu____48964 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____48968 ->
               let uu____48973 = eq_tm h1 h2  in
               eq_and uu____48973 (fun uu____48975  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____49081 = FStar_List.zip bs1 bs2  in
            let uu____49144 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____49181  ->
                 fun a  ->
                   match uu____49181 with
                   | (b1,b2) ->
                       eq_and a (fun uu____49274  -> branch_matches b1 b2))
              uu____49081 uu____49144
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____49279 = eq_univs u v1  in equal_if uu____49279
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____49293 = eq_quoteinfo q1 q2  in
          eq_and uu____49293 (fun uu____49295  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____49308 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____49308 (fun uu____49310  -> eq_tm phi1 phi2)
      | uu____49311 -> Unknown

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
      | ([],uu____49383) -> NotEqual
      | (uu____49414,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____49506 = eq_tm t1 t2  in
             match uu____49506 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____49507 = eq_antiquotes a11 a21  in
                 (match uu____49507 with
                  | NotEqual  -> NotEqual
                  | uu____49508 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____49523) -> NotEqual
      | (uu____49530,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____49560 -> NotEqual

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
        | (uu____49652,uu____49653) -> false  in
      let uu____49663 = b1  in
      match uu____49663 with
      | (p1,w1,t1) ->
          let uu____49697 = b2  in
          (match uu____49697 with
           | (p2,w2,t2) ->
               let uu____49731 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____49731
               then
                 let uu____49734 =
                   (let uu____49738 = eq_tm t1 t2  in uu____49738 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____49747 = eq_tm t11 t21  in
                             uu____49747 = Equal) w1 w2)
                    in
                 (if uu____49734 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____49812)::a11,(b,uu____49815)::b1) ->
          let uu____49889 = eq_tm a b  in
          (match uu____49889 with
           | Equal  -> eq_args a11 b1
           | uu____49890 -> Unknown)
      | uu____49891 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____49927) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____49933,uu____49934) ->
        unrefine t2
    | uu____49975 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49983 =
      let uu____49984 = FStar_Syntax_Subst.compress t  in
      uu____49984.FStar_Syntax_Syntax.n  in
    match uu____49983 with
    | FStar_Syntax_Syntax.Tm_uvar uu____49988 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50003) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____50008 ->
        let uu____50025 =
          let uu____50026 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____50026 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____50025 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____50089,uu____50090) ->
        is_uvar t1
    | uu____50131 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50140 =
      let uu____50141 = unrefine t  in uu____50141.FStar_Syntax_Syntax.n  in
    match uu____50140 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50147) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50173) -> is_unit t1
    | uu____50178 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50187 =
      let uu____50188 = FStar_Syntax_Subst.compress t  in
      uu____50188.FStar_Syntax_Syntax.n  in
    match uu____50187 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____50193 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50202 =
      let uu____50203 = unrefine t  in uu____50203.FStar_Syntax_Syntax.n  in
    match uu____50202 with
    | FStar_Syntax_Syntax.Tm_type uu____50207 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50211) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50237) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____50242,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____50264 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____50273 =
      let uu____50274 = FStar_Syntax_Subst.compress e  in
      uu____50274.FStar_Syntax_Syntax.n  in
    match uu____50273 with
    | FStar_Syntax_Syntax.Tm_abs uu____50278 -> true
    | uu____50298 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50307 =
      let uu____50308 = FStar_Syntax_Subst.compress t  in
      uu____50308.FStar_Syntax_Syntax.n  in
    match uu____50307 with
    | FStar_Syntax_Syntax.Tm_arrow uu____50312 -> true
    | uu____50328 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____50338) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____50344,uu____50345) ->
        pre_typ t2
    | uu____50386 -> t1
  
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
      let uu____50411 =
        let uu____50412 = un_uinst typ1  in uu____50412.FStar_Syntax_Syntax.n
         in
      match uu____50411 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____50477 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____50507 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____50528,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____50535) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____50540,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____50551,uu____50552,uu____50553,uu____50554,uu____50555) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____50565,uu____50566,uu____50567,uu____50568) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____50574,uu____50575,uu____50576,uu____50577,uu____50578) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____50586,uu____50587) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____50589,uu____50590) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____50593 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____50594 -> []
    | FStar_Syntax_Syntax.Sig_main uu____50595 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____50609 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_50635  ->
    match uu___413_50635 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____50649 'Auu____50650 .
    ('Auu____50649 FStar_Syntax_Syntax.syntax * 'Auu____50650) ->
      FStar_Range.range
  =
  fun uu____50661  ->
    match uu____50661 with | (hd1,uu____50669) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____50683 'Auu____50684 .
    ('Auu____50683 FStar_Syntax_Syntax.syntax * 'Auu____50684) Prims.list ->
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
      | uu____50782 ->
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
      let uu____50841 =
        FStar_List.map
          (fun uu____50868  ->
             match uu____50868 with
             | (bv,aq) ->
                 let uu____50887 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____50887, aq)) bs
         in
      mk_app f uu____50841
  
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
          let uu____50937 = FStar_Ident.range_of_lid l  in
          let uu____50938 =
            let uu____50947 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____50947  in
          uu____50938 FStar_Pervasives_Native.None uu____50937
      | uu____50955 ->
          let e =
            let uu____50969 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____50969 args  in
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
          let uu____51046 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____51046
          then
            let uu____51049 =
              let uu____51055 =
                let uu____51057 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____51057  in
              let uu____51060 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____51055, uu____51060)  in
            FStar_Ident.mk_ident uu____51049
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1421_51065 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1421_51065.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1421_51065.FStar_Syntax_Syntax.sort)
          }  in
        let uu____51066 = mk_field_projector_name_from_ident lid nm  in
        (uu____51066, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____51078) -> ses
    | uu____51087 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____51098 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____51111 = FStar_Syntax_Unionfind.find uv  in
      match uu____51111 with
      | FStar_Pervasives_Native.Some uu____51114 ->
          let uu____51115 =
            let uu____51117 =
              let uu____51119 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____51119  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____51117  in
          failwith uu____51115
      | uu____51124 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____51207 -> q1 = q2
  
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
              let uu____51253 =
                let uu___1482_51254 = rc  in
                let uu____51255 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1482_51254.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____51255;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1482_51254.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____51253
           in
        match bs with
        | [] -> t
        | uu____51272 ->
            let body =
              let uu____51274 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____51274  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____51304 =
                   let uu____51311 =
                     let uu____51312 =
                       let uu____51331 =
                         let uu____51340 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____51340 bs'  in
                       let uu____51355 = close_lopt lopt'  in
                       (uu____51331, t1, uu____51355)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51312  in
                   FStar_Syntax_Syntax.mk uu____51311  in
                 uu____51304 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____51373 ->
                 let uu____51374 =
                   let uu____51381 =
                     let uu____51382 =
                       let uu____51401 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____51410 = close_lopt lopt  in
                       (uu____51401, body, uu____51410)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51382  in
                   FStar_Syntax_Syntax.mk uu____51381  in
                 uu____51374 FStar_Pervasives_Native.None
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
      | uu____51469 ->
          let uu____51478 =
            let uu____51485 =
              let uu____51486 =
                let uu____51501 = FStar_Syntax_Subst.close_binders bs  in
                let uu____51510 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____51501, uu____51510)  in
              FStar_Syntax_Syntax.Tm_arrow uu____51486  in
            FStar_Syntax_Syntax.mk uu____51485  in
          uu____51478 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____51562 =
        let uu____51563 = FStar_Syntax_Subst.compress t  in
        uu____51563.FStar_Syntax_Syntax.n  in
      match uu____51562 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____51593) ->
               let uu____51602 =
                 let uu____51603 = FStar_Syntax_Subst.compress tres  in
                 uu____51603.FStar_Syntax_Syntax.n  in
               (match uu____51602 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____51646 -> t)
           | uu____51647 -> t)
      | uu____51648 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____51666 =
        let uu____51667 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____51667 t.FStar_Syntax_Syntax.pos  in
      let uu____51668 =
        let uu____51675 =
          let uu____51676 =
            let uu____51683 =
              let uu____51686 =
                let uu____51687 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____51687]  in
              FStar_Syntax_Subst.close uu____51686 t  in
            (b, uu____51683)  in
          FStar_Syntax_Syntax.Tm_refine uu____51676  in
        FStar_Syntax_Syntax.mk uu____51675  in
      uu____51668 FStar_Pervasives_Native.None uu____51666
  
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
        let uu____51770 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____51770 with
         | (bs1,c1) ->
             let uu____51789 = is_total_comp c1  in
             if uu____51789
             then
               let uu____51804 = arrow_formals_comp (comp_result c1)  in
               (match uu____51804 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____51871;
           FStar_Syntax_Syntax.index = uu____51872;
           FStar_Syntax_Syntax.sort = s;_},uu____51874)
        ->
        let rec aux s1 k2 =
          let uu____51905 =
            let uu____51906 = FStar_Syntax_Subst.compress s1  in
            uu____51906.FStar_Syntax_Syntax.n  in
          match uu____51905 with
          | FStar_Syntax_Syntax.Tm_arrow uu____51921 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____51936;
                 FStar_Syntax_Syntax.index = uu____51937;
                 FStar_Syntax_Syntax.sort = s2;_},uu____51939)
              -> aux s2 k2
          | uu____51947 ->
              let uu____51948 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____51948)
           in
        aux s k1
    | uu____51963 ->
        let uu____51964 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____51964)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____51999 = arrow_formals_comp k  in
    match uu____51999 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____52141 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____52141 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____52165 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_52174  ->
                         match uu___414_52174 with
                         | FStar_Syntax_Syntax.DECREASES uu____52176 -> true
                         | uu____52180 -> false))
                  in
               (match uu____52165 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____52215 ->
                    let uu____52218 = is_total_comp c1  in
                    if uu____52218
                    then
                      let uu____52237 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____52237 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____52330;
             FStar_Syntax_Syntax.index = uu____52331;
             FStar_Syntax_Syntax.sort = k2;_},uu____52333)
          -> arrow_until_decreases k2
      | uu____52341 -> ([], FStar_Pervasives_Native.None)  in
    let uu____52362 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____52362 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____52416 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____52437 =
                 FStar_Common.tabulate n_univs (fun uu____52447  -> false)
                  in
               let uu____52450 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____52475  ->
                         match uu____52475 with
                         | (x,uu____52484) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____52437 uu____52450)
           in
        ((n_univs + (FStar_List.length bs)), uu____52416)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____52546 =
            let uu___1604_52547 = rc  in
            let uu____52548 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1604_52547.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____52548;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1604_52547.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____52546
      | uu____52557 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____52591 =
        let uu____52592 =
          let uu____52595 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____52595  in
        uu____52592.FStar_Syntax_Syntax.n  in
      match uu____52591 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____52641 = aux t2 what  in
          (match uu____52641 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____52713 -> ([], t1, abs_body_lcomp)  in
    let uu____52730 = aux t FStar_Pervasives_Native.None  in
    match uu____52730 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____52778 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____52778 with
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
                    | (FStar_Pervasives_Native.None ,uu____52941) -> def
                    | (uu____52952,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____52964) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _52980  ->
                                  FStar_Syntax_Syntax.U_name _52980))
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
            let uu____53062 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____53062 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____53097 ->
            let t' = arrow binders c  in
            let uu____53109 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____53109 with
             | (uvs1,t'1) ->
                 let uu____53130 =
                   let uu____53131 = FStar_Syntax_Subst.compress t'1  in
                   uu____53131.FStar_Syntax_Syntax.n  in
                 (match uu____53130 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____53180 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____53205 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____53216 -> false
  
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
      let uu____53279 =
        let uu____53280 = pre_typ t  in uu____53280.FStar_Syntax_Syntax.n  in
      match uu____53279 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____53285 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____53299 =
        let uu____53300 = pre_typ t  in uu____53300.FStar_Syntax_Syntax.n  in
      match uu____53299 with
      | FStar_Syntax_Syntax.Tm_fvar uu____53304 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____53306) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____53332) ->
          is_constructed_typ t1 lid
      | uu____53337 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____53350 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____53351 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____53352 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____53354) -> get_tycon t2
    | uu____53379 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____53387 =
      let uu____53388 = un_uinst t  in uu____53388.FStar_Syntax_Syntax.n  in
    match uu____53387 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____53393 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____53407 =
        let uu____53411 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____53411  in
      match uu____53407 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____53443 -> false
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
  fun uu____53462  ->
    let u =
      let uu____53468 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _53485  -> FStar_Syntax_Syntax.U_unif _53485)
        uu____53468
       in
    let uu____53486 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____53486, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____53499 = eq_tm a a'  in
      match uu____53499 with | Equal  -> true | uu____53502 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____53507 =
    let uu____53514 =
      let uu____53515 =
        let uu____53516 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____53516
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____53515  in
    FStar_Syntax_Syntax.mk uu____53514  in
  uu____53507 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____53631 =
            let uu____53634 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____53635 =
              let uu____53642 =
                let uu____53643 =
                  let uu____53660 =
                    let uu____53671 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____53680 =
                      let uu____53691 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____53691]  in
                    uu____53671 :: uu____53680  in
                  (tand, uu____53660)  in
                FStar_Syntax_Syntax.Tm_app uu____53643  in
              FStar_Syntax_Syntax.mk uu____53642  in
            uu____53635 FStar_Pervasives_Native.None uu____53634  in
          FStar_Pervasives_Native.Some uu____53631
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____53771 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____53772 =
          let uu____53779 =
            let uu____53780 =
              let uu____53797 =
                let uu____53808 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____53817 =
                  let uu____53828 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____53828]  in
                uu____53808 :: uu____53817  in
              (op_t, uu____53797)  in
            FStar_Syntax_Syntax.Tm_app uu____53780  in
          FStar_Syntax_Syntax.mk uu____53779  in
        uu____53772 FStar_Pervasives_Native.None uu____53771
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____53888 =
      let uu____53895 =
        let uu____53896 =
          let uu____53913 =
            let uu____53924 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____53924]  in
          (t_not, uu____53913)  in
        FStar_Syntax_Syntax.Tm_app uu____53896  in
      FStar_Syntax_Syntax.mk uu____53895  in
    uu____53888 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____54124 =
      let uu____54131 =
        let uu____54132 =
          let uu____54149 =
            let uu____54160 = FStar_Syntax_Syntax.as_arg e  in [uu____54160]
             in
          (b2t_v, uu____54149)  in
        FStar_Syntax_Syntax.Tm_app uu____54132  in
      FStar_Syntax_Syntax.mk uu____54131  in
    uu____54124 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____54207 =
      let uu____54208 = unmeta t  in uu____54208.FStar_Syntax_Syntax.n  in
    match uu____54207 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____54213 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54236 = is_t_true t1  in
      if uu____54236
      then t2
      else
        (let uu____54243 = is_t_true t2  in
         if uu____54243 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54271 = is_t_true t1  in
      if uu____54271
      then t_true
      else
        (let uu____54278 = is_t_true t2  in
         if uu____54278 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____54307 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____54308 =
        let uu____54315 =
          let uu____54316 =
            let uu____54333 =
              let uu____54344 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____54353 =
                let uu____54364 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____54364]  in
              uu____54344 :: uu____54353  in
            (teq, uu____54333)  in
          FStar_Syntax_Syntax.Tm_app uu____54316  in
        FStar_Syntax_Syntax.mk uu____54315  in
      uu____54308 FStar_Pervasives_Native.None uu____54307
  
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
          let uu____54434 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____54435 =
            let uu____54442 =
              let uu____54443 =
                let uu____54460 =
                  let uu____54471 = FStar_Syntax_Syntax.iarg t  in
                  let uu____54480 =
                    let uu____54491 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____54500 =
                      let uu____54511 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____54511]  in
                    uu____54491 :: uu____54500  in
                  uu____54471 :: uu____54480  in
                (eq_inst, uu____54460)  in
              FStar_Syntax_Syntax.Tm_app uu____54443  in
            FStar_Syntax_Syntax.mk uu____54442  in
          uu____54435 FStar_Pervasives_Native.None uu____54434
  
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
        let uu____54591 =
          let uu____54598 =
            let uu____54599 =
              let uu____54616 =
                let uu____54627 = FStar_Syntax_Syntax.iarg t  in
                let uu____54636 =
                  let uu____54647 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____54656 =
                    let uu____54667 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____54667]  in
                  uu____54647 :: uu____54656  in
                uu____54627 :: uu____54636  in
              (t_has_type1, uu____54616)  in
            FStar_Syntax_Syntax.Tm_app uu____54599  in
          FStar_Syntax_Syntax.mk uu____54598  in
        uu____54591 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____54747 =
          let uu____54754 =
            let uu____54755 =
              let uu____54772 =
                let uu____54783 = FStar_Syntax_Syntax.iarg t  in
                let uu____54792 =
                  let uu____54803 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____54803]  in
                uu____54783 :: uu____54792  in
              (t_with_type1, uu____54772)  in
            FStar_Syntax_Syntax.Tm_app uu____54755  in
          FStar_Syntax_Syntax.mk uu____54754  in
        uu____54747 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____54853 =
    let uu____54860 =
      let uu____54861 =
        let uu____54868 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____54868, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____54861  in
    FStar_Syntax_Syntax.mk uu____54860  in
  uu____54853 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____54886 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____54899 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____54910 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____54886 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____54931  -> c0)
  
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
        let uu____55014 =
          let uu____55021 =
            let uu____55022 =
              let uu____55039 =
                let uu____55050 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____55059 =
                  let uu____55070 =
                    let uu____55079 =
                      let uu____55080 =
                        let uu____55081 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____55081]  in
                      abs uu____55080 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____55079  in
                  [uu____55070]  in
                uu____55050 :: uu____55059  in
              (fa, uu____55039)  in
            FStar_Syntax_Syntax.Tm_app uu____55022  in
          FStar_Syntax_Syntax.mk uu____55021  in
        uu____55014 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____55211 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____55211
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____55230 -> true
    | uu____55232 -> false
  
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
          let uu____55279 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____55279, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____55308 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____55308, FStar_Pervasives_Native.None, t2)  in
        let uu____55322 =
          let uu____55323 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____55323  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____55322
  
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
      let uu____55399 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55402 =
        let uu____55413 = FStar_Syntax_Syntax.as_arg p  in [uu____55413]  in
      mk_app uu____55399 uu____55402
  
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
      let uu____55453 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55456 =
        let uu____55467 = FStar_Syntax_Syntax.as_arg p  in [uu____55467]  in
      mk_app uu____55453 uu____55456
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55502 = head_and_args t  in
    match uu____55502 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____55551 =
          let uu____55566 =
            let uu____55567 = FStar_Syntax_Subst.compress head3  in
            uu____55567.FStar_Syntax_Syntax.n  in
          (uu____55566, args)  in
        (match uu____55551 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____55586)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____55652 =
                    let uu____55657 =
                      let uu____55658 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____55658]  in
                    FStar_Syntax_Subst.open_term uu____55657 p  in
                  (match uu____55652 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____55715 -> failwith "impossible"  in
                       let uu____55723 =
                         let uu____55725 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____55725
                          in
                       if uu____55723
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____55741 -> FStar_Pervasives_Native.None)
         | uu____55744 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55775 = head_and_args t  in
    match uu____55775 with
    | (head1,args) ->
        let uu____55826 =
          let uu____55841 =
            let uu____55842 = FStar_Syntax_Subst.compress head1  in
            uu____55842.FStar_Syntax_Syntax.n  in
          (uu____55841, args)  in
        (match uu____55826 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____55864;
               FStar_Syntax_Syntax.vars = uu____55865;_},u::[]),(t1,uu____55868)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____55915 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55950 = head_and_args t  in
    match uu____55950 with
    | (head1,args) ->
        let uu____56001 =
          let uu____56016 =
            let uu____56017 = FStar_Syntax_Subst.compress head1  in
            uu____56017.FStar_Syntax_Syntax.n  in
          (uu____56016, args)  in
        (match uu____56001 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____56039;
               FStar_Syntax_Syntax.vars = uu____56040;_},u::[]),(t1,uu____56043)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____56090 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____56118 =
      let uu____56135 = unmeta t  in head_and_args uu____56135  in
    match uu____56118 with
    | (head1,uu____56138) ->
        let uu____56163 =
          let uu____56164 = un_uinst head1  in
          uu____56164.FStar_Syntax_Syntax.n  in
        (match uu____56163 with
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
         | uu____56169 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____56189 =
      let uu____56202 =
        let uu____56203 = FStar_Syntax_Subst.compress t  in
        uu____56203.FStar_Syntax_Syntax.n  in
      match uu____56202 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____56333 =
            let uu____56344 =
              let uu____56345 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____56345  in
            (b, uu____56344)  in
          FStar_Pervasives_Native.Some uu____56333
      | uu____56362 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____56189
      (fun uu____56400  ->
         match uu____56400 with
         | (b,c) ->
             let uu____56437 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____56437 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____56500 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____56537 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____56537
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____56589 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____56633 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____56675 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____56715) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____56727) ->
          unmeta_monadic t
      | uu____56740 -> f2  in
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
      let aux f2 uu____56836 =
        match uu____56836 with
        | (lid,arity) ->
            let uu____56845 =
              let uu____56862 = unmeta_monadic f2  in
              head_and_args uu____56862  in
            (match uu____56845 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____56892 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____56892
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____56972 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____56972)
      | uu____56985 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____57052 = head_and_args t1  in
        match uu____57052 with
        | (t2,args) ->
            let uu____57107 = un_uinst t2  in
            let uu____57108 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____57149  ->
                      match uu____57149 with
                      | (t3,imp) ->
                          let uu____57168 = unascribe t3  in
                          (uu____57168, imp)))
               in
            (uu____57107, uu____57108)
         in
      let rec aux qopt out t1 =
        let uu____57219 = let uu____57243 = flat t1  in (qopt, uu____57243)
           in
        match uu____57219 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57283;
                 FStar_Syntax_Syntax.vars = uu____57284;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____57287);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____57288;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____57289;_},uu____57290)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57392;
                 FStar_Syntax_Syntax.vars = uu____57393;_},uu____57394::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____57397);
                  FStar_Syntax_Syntax.pos = uu____57398;
                  FStar_Syntax_Syntax.vars = uu____57399;_},uu____57400)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57517;
               FStar_Syntax_Syntax.vars = uu____57518;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____57521);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____57522;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____57523;_},uu____57524)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57617 =
              let uu____57621 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57621  in
            aux uu____57617 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57631;
               FStar_Syntax_Syntax.vars = uu____57632;_},uu____57633::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____57636);
                FStar_Syntax_Syntax.pos = uu____57637;
                FStar_Syntax_Syntax.vars = uu____57638;_},uu____57639)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57748 =
              let uu____57752 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57752  in
            aux uu____57748 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____57762) ->
            let bs = FStar_List.rev out  in
            let uu____57815 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____57815 with
             | (bs1,t2) ->
                 let uu____57824 = patterns t2  in
                 (match uu____57824 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____57874 -> FStar_Pervasives_Native.None  in
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
      let uu____57966 = un_squash t  in
      FStar_Util.bind_opt uu____57966
        (fun t1  ->
           let uu____57982 = head_and_args' t1  in
           match uu____57982 with
           | (hd1,args) ->
               let uu____58021 =
                 let uu____58027 =
                   let uu____58028 = un_uinst hd1  in
                   uu____58028.FStar_Syntax_Syntax.n  in
                 (uu____58027, (FStar_List.length args))  in
               (match uu____58021 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58044) when
                    (_58044 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58047) when
                    (_58047 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58050) when
                    (_58050 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58053) when
                    (_58053 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58056) when
                    (_58056 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58059) when
                    (_58059 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58062) when
                    (_58062 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_58065) when
                    (_58065 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____58066 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____58096 = un_squash t  in
      FStar_Util.bind_opt uu____58096
        (fun t1  ->
           let uu____58111 = arrow_one t1  in
           match uu____58111 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____58126 =
                 let uu____58128 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____58128  in
               if uu____58126
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____58138 = comp_to_comp_typ_nouniv c  in
                    uu____58138.FStar_Syntax_Syntax.result_typ  in
                  let uu____58139 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____58139
                  then
                    let uu____58146 = patterns q  in
                    match uu____58146 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____58209 =
                       let uu____58210 =
                         let uu____58215 =
                           let uu____58216 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____58227 =
                             let uu____58238 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____58238]  in
                           uu____58216 :: uu____58227  in
                         (FStar_Parser_Const.imp_lid, uu____58215)  in
                       BaseConn uu____58210  in
                     FStar_Pervasives_Native.Some uu____58209))
           | uu____58271 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____58279 = un_squash t  in
      FStar_Util.bind_opt uu____58279
        (fun t1  ->
           let uu____58310 = head_and_args' t1  in
           match uu____58310 with
           | (hd1,args) ->
               let uu____58349 =
                 let uu____58364 =
                   let uu____58365 = un_uinst hd1  in
                   uu____58365.FStar_Syntax_Syntax.n  in
                 (uu____58364, args)  in
               (match uu____58349 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____58382)::(a2,uu____58384)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____58435 =
                      let uu____58436 = FStar_Syntax_Subst.compress a2  in
                      uu____58436.FStar_Syntax_Syntax.n  in
                    (match uu____58435 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____58443) ->
                         let uu____58478 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____58478 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____58531 -> failwith "impossible"  in
                              let uu____58539 = patterns q1  in
                              (match uu____58539 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____58600 -> FStar_Pervasives_Native.None)
                | uu____58601 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____58624 = destruct_sq_forall phi  in
          (match uu____58624 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58634  -> FStar_Pervasives_Native.Some _58634)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58641 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____58647 = destruct_sq_exists phi  in
          (match uu____58647 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58657  -> FStar_Pervasives_Native.Some _58657)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58664 -> f1)
      | uu____58667 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____58671 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____58671
      (fun uu____58676  ->
         let uu____58677 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____58677
           (fun uu____58682  ->
              let uu____58683 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____58683
                (fun uu____58688  ->
                   let uu____58689 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____58689
                     (fun uu____58694  ->
                        let uu____58695 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____58695
                          (fun uu____58699  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____58712 =
      let uu____58713 = FStar_Syntax_Subst.compress t  in
      uu____58713.FStar_Syntax_Syntax.n  in
    match uu____58712 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____58720) ->
        let uu____58755 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____58755 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____58789 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____58789
             then
               let uu____58796 =
                 let uu____58807 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____58807]  in
               mk_app t uu____58796
             else e1)
    | uu____58834 ->
        let uu____58835 =
          let uu____58846 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____58846]  in
        mk_app t uu____58835
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____58888 =
            let uu____58893 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____58893  in
          let uu____58894 =
            let uu____58895 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____58895  in
          let uu____58898 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____58888 a.FStar_Syntax_Syntax.action_univs uu____58894
            FStar_Parser_Const.effect_Tot_lid uu____58898 [] pos
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
    let uu____58924 =
      let uu____58931 =
        let uu____58932 =
          let uu____58949 =
            let uu____58960 = FStar_Syntax_Syntax.as_arg t  in [uu____58960]
             in
          (reify_1, uu____58949)  in
        FStar_Syntax_Syntax.Tm_app uu____58932  in
      FStar_Syntax_Syntax.mk uu____58931  in
    uu____58924 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____59015 =
        let uu____59022 =
          let uu____59023 =
            let uu____59024 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____59024  in
          FStar_Syntax_Syntax.Tm_constant uu____59023  in
        FStar_Syntax_Syntax.mk uu____59022  in
      uu____59015 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____59029 =
      let uu____59036 =
        let uu____59037 =
          let uu____59054 =
            let uu____59065 = FStar_Syntax_Syntax.as_arg t  in [uu____59065]
             in
          (reflect_, uu____59054)  in
        FStar_Syntax_Syntax.Tm_app uu____59037  in
      FStar_Syntax_Syntax.mk uu____59036  in
    uu____59029 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____59112 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____59137 = unfold_lazy i  in delta_qualifier uu____59137
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____59139 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____59140 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____59141 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____59164 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____59177 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____59178 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____59185 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____59186 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____59202) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____59207;
           FStar_Syntax_Syntax.index = uu____59208;
           FStar_Syntax_Syntax.sort = t2;_},uu____59210)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____59219) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____59225,uu____59226) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____59268) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____59293,t2,uu____59295) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____59320,t2) -> delta_qualifier t2
  
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
    let uu____59359 = delta_qualifier t  in incr_delta_depth uu____59359
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____59367 =
      let uu____59368 = FStar_Syntax_Subst.compress t  in
      uu____59368.FStar_Syntax_Syntax.n  in
    match uu____59367 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____59373 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____59389 =
      let uu____59406 = unmeta e  in head_and_args uu____59406  in
    match uu____59389 with
    | (head1,args) ->
        let uu____59437 =
          let uu____59452 =
            let uu____59453 = un_uinst head1  in
            uu____59453.FStar_Syntax_Syntax.n  in
          (uu____59452, args)  in
        (match uu____59437 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____59471) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____59495::(hd1,uu____59497)::(tl1,uu____59499)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____59566 =
               let uu____59569 =
                 let uu____59572 = list_elements tl1  in
                 FStar_Util.must uu____59572  in
               hd1 :: uu____59569  in
             FStar_Pervasives_Native.Some uu____59566
         | uu____59581 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____59605 .
    ('Auu____59605 -> 'Auu____59605) ->
      'Auu____59605 Prims.list -> 'Auu____59605 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____59631 = f a  in [uu____59631]
      | x::xs -> let uu____59636 = apply_last f xs  in x :: uu____59636
  
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
          let uu____59691 =
            let uu____59698 =
              let uu____59699 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____59699  in
            FStar_Syntax_Syntax.mk uu____59698  in
          uu____59691 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____59716 =
            let uu____59721 =
              let uu____59722 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59722
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59721 args  in
          uu____59716 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____59738 =
            let uu____59743 =
              let uu____59744 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59744
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59743 args  in
          uu____59738 FStar_Pervasives_Native.None pos  in
        let uu____59747 =
          let uu____59748 =
            let uu____59749 = FStar_Syntax_Syntax.iarg typ  in [uu____59749]
             in
          nil uu____59748 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____59783 =
                 let uu____59784 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____59793 =
                   let uu____59804 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____59813 =
                     let uu____59824 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____59824]  in
                   uu____59804 :: uu____59813  in
                 uu____59784 :: uu____59793  in
               cons1 uu____59783 t.FStar_Syntax_Syntax.pos) l uu____59747
  
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
        | uu____59933 -> false
  
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
          | uu____60047 -> false
  
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
        | uu____60213 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____60262 = FStar_ST.op_Bang debug_term_eq  in
          if uu____60262
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
        let t11 = let uu____60484 = unmeta_safe t1  in canon_app uu____60484
           in
        let t21 = let uu____60490 = unmeta_safe t2  in canon_app uu____60490
           in
        let uu____60493 =
          let uu____60498 =
            let uu____60499 =
              let uu____60502 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____60502  in
            uu____60499.FStar_Syntax_Syntax.n  in
          let uu____60503 =
            let uu____60504 =
              let uu____60507 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____60507  in
            uu____60504.FStar_Syntax_Syntax.n  in
          (uu____60498, uu____60503)  in
        match uu____60493 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____60509,uu____60510) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60519,FStar_Syntax_Syntax.Tm_uinst uu____60520) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____60529,uu____60530) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60555,FStar_Syntax_Syntax.Tm_delayed uu____60556) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____60581,uu____60582) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60611,FStar_Syntax_Syntax.Tm_ascribed uu____60612) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____60651 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____60651
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____60656 = FStar_Const.eq_const c1 c2  in
            check "const" uu____60656
        | (FStar_Syntax_Syntax.Tm_type
           uu____60659,FStar_Syntax_Syntax.Tm_type uu____60660) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____60718 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____60718) &&
              (let uu____60728 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____60728)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____60777 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____60777) &&
              (let uu____60787 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____60787)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____60805 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____60805)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____60862 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____60862) &&
              (let uu____60866 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____60866)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____60955 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____60955) &&
              (let uu____60959 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____60959)
        | (FStar_Syntax_Syntax.Tm_lazy uu____60976,uu____60977) ->
            let uu____60978 =
              let uu____60980 = unlazy t11  in
              term_eq_dbg dbg uu____60980 t21  in
            check "lazy_l" uu____60978
        | (uu____60982,FStar_Syntax_Syntax.Tm_lazy uu____60983) ->
            let uu____60984 =
              let uu____60986 = unlazy t21  in
              term_eq_dbg dbg t11 uu____60986  in
            check "lazy_r" uu____60984
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____61031 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____61031))
              &&
              (let uu____61035 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____61035)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____61039),FStar_Syntax_Syntax.Tm_uvar (u2,uu____61041)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____61099 =
               let uu____61101 = eq_quoteinfo qi1 qi2  in uu____61101 = Equal
                in
             check "tm_quoted qi" uu____61099) &&
              (let uu____61104 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____61104)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____61134 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____61134) &&
                   (let uu____61138 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____61138)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____61157 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____61157) &&
                    (let uu____61161 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____61161))
                   &&
                   (let uu____61165 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____61165)
             | uu____61168 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____61174) -> fail "unk"
        | (uu____61176,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____61178,uu____61179) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____61181,uu____61182) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____61184,uu____61185) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____61187,uu____61188) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____61190,uu____61191) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____61193,uu____61194) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____61214,uu____61215) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____61231,uu____61232) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____61240,uu____61241) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____61259,uu____61260) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____61284,uu____61285) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____61300,uu____61301) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____61315,uu____61316) ->
            fail "bottom"
        | (uu____61324,FStar_Syntax_Syntax.Tm_bvar uu____61325) ->
            fail "bottom"
        | (uu____61327,FStar_Syntax_Syntax.Tm_name uu____61328) ->
            fail "bottom"
        | (uu____61330,FStar_Syntax_Syntax.Tm_fvar uu____61331) ->
            fail "bottom"
        | (uu____61333,FStar_Syntax_Syntax.Tm_constant uu____61334) ->
            fail "bottom"
        | (uu____61336,FStar_Syntax_Syntax.Tm_type uu____61337) ->
            fail "bottom"
        | (uu____61339,FStar_Syntax_Syntax.Tm_abs uu____61340) ->
            fail "bottom"
        | (uu____61360,FStar_Syntax_Syntax.Tm_arrow uu____61361) ->
            fail "bottom"
        | (uu____61377,FStar_Syntax_Syntax.Tm_refine uu____61378) ->
            fail "bottom"
        | (uu____61386,FStar_Syntax_Syntax.Tm_app uu____61387) ->
            fail "bottom"
        | (uu____61405,FStar_Syntax_Syntax.Tm_match uu____61406) ->
            fail "bottom"
        | (uu____61430,FStar_Syntax_Syntax.Tm_let uu____61431) ->
            fail "bottom"
        | (uu____61446,FStar_Syntax_Syntax.Tm_uvar uu____61447) ->
            fail "bottom"
        | (uu____61461,FStar_Syntax_Syntax.Tm_meta uu____61462) ->
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
               let uu____61497 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____61497)
          (fun q1  ->
             fun q2  ->
               let uu____61509 =
                 let uu____61511 = eq_aqual q1 q2  in uu____61511 = Equal  in
               check "arg qual" uu____61509) a1 a2

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
               let uu____61536 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____61536)
          (fun q1  ->
             fun q2  ->
               let uu____61548 =
                 let uu____61550 = eq_aqual q1 q2  in uu____61550 = Equal  in
               check "binder qual" uu____61548) b1 b2

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
        ((let uu____61570 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____61570) &&
           (let uu____61574 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____61574))
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
    fun uu____61584  ->
      fun uu____61585  ->
        match (uu____61584, uu____61585) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____61712 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____61712) &&
               (let uu____61716 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____61716))
              &&
              (let uu____61720 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____61762 -> false  in
               check "branch when" uu____61720)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____61783 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____61783) &&
           (let uu____61792 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____61792))
          &&
          (let uu____61796 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____61796)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____61813 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____61813 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____61867 ->
        let uu____61890 =
          let uu____61892 = FStar_Syntax_Subst.compress t  in
          sizeof uu____61892  in
        (Prims.parse_int "1") + uu____61890
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____61895 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61895
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____61899 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61899
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____61908 = sizeof t1  in (FStar_List.length us) + uu____61908
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____61912) ->
        let uu____61937 = sizeof t1  in
        let uu____61939 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____61954  ->
                 match uu____61954 with
                 | (bv,uu____61964) ->
                     let uu____61969 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____61969) (Prims.parse_int "0") bs
           in
        uu____61937 + uu____61939
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____61998 = sizeof hd1  in
        let uu____62000 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____62015  ->
                 match uu____62015 with
                 | (arg,uu____62025) ->
                     let uu____62030 = sizeof arg  in acc + uu____62030)
            (Prims.parse_int "0") args
           in
        uu____61998 + uu____62000
    | uu____62033 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____62047 =
        let uu____62048 = un_uinst t  in uu____62048.FStar_Syntax_Syntax.n
         in
      match uu____62047 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____62053 -> false
  
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
        let uu____62102 = FStar_Options.set_options t s  in
        match uu____62102 with
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
          ((let uu____62119 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____62119 (fun a1  -> ()));
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
          let uu____62134 = FStar_Options.internal_pop ()  in
          if uu____62134
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
    | FStar_Syntax_Syntax.Tm_delayed uu____62166 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____62193 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____62208 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____62209 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____62210 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____62219) ->
        let uu____62244 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____62244 with
         | (bs1,t2) ->
             let uu____62253 =
               FStar_List.collect
                 (fun uu____62265  ->
                    match uu____62265 with
                    | (b,uu____62275) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62280 = unbound_variables t2  in
             FStar_List.append uu____62253 uu____62280)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____62305 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____62305 with
         | (bs1,c1) ->
             let uu____62314 =
               FStar_List.collect
                 (fun uu____62326  ->
                    match uu____62326 with
                    | (b,uu____62336) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62341 = unbound_variables_comp c1  in
             FStar_List.append uu____62314 uu____62341)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____62350 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____62350 with
         | (bs,t2) ->
             let uu____62373 =
               FStar_List.collect
                 (fun uu____62385  ->
                    match uu____62385 with
                    | (b1,uu____62395) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____62400 = unbound_variables t2  in
             FStar_List.append uu____62373 uu____62400)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____62429 =
          FStar_List.collect
            (fun uu____62443  ->
               match uu____62443 with
               | (x,uu____62455) -> unbound_variables x) args
           in
        let uu____62464 = unbound_variables t1  in
        FStar_List.append uu____62429 uu____62464
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____62505 = unbound_variables t1  in
        let uu____62508 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____62523 = FStar_Syntax_Subst.open_branch br  in
                  match uu____62523 with
                  | (p,wopt,t2) ->
                      let uu____62545 = unbound_variables t2  in
                      let uu____62548 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____62545 uu____62548))
           in
        FStar_List.append uu____62505 uu____62508
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____62562) ->
        let uu____62603 = unbound_variables t1  in
        let uu____62606 =
          let uu____62609 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____62640 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____62609 uu____62640  in
        FStar_List.append uu____62603 uu____62606
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____62681 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____62684 =
          let uu____62687 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____62690 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____62695 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____62697 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____62697 with
                 | (uu____62718,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____62687 uu____62690  in
        FStar_List.append uu____62681 uu____62684
    | FStar_Syntax_Syntax.Tm_let ((uu____62720,lbs),t1) ->
        let uu____62740 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____62740 with
         | (lbs1,t2) ->
             let uu____62755 = unbound_variables t2  in
             let uu____62758 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____62765 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____62768 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____62765 uu____62768) lbs1
                in
             FStar_List.append uu____62755 uu____62758)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____62785 = unbound_variables t1  in
        let uu____62788 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____62827  ->
                      match uu____62827 with
                      | (a,uu____62839) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____62848,uu____62849,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____62855,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____62861 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____62870 -> []
          | FStar_Syntax_Syntax.Meta_named uu____62871 -> []  in
        FStar_List.append uu____62785 uu____62788

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____62878) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____62888) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____62898 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____62901 =
          FStar_List.collect
            (fun uu____62915  ->
               match uu____62915 with
               | (a,uu____62927) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____62898 uu____62901

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
            let uu____63042 = head_and_args h  in
            (match uu____63042 with
             | (head1,args) ->
                 let uu____63103 =
                   let uu____63104 = FStar_Syntax_Subst.compress head1  in
                   uu____63104.FStar_Syntax_Syntax.n  in
                 (match uu____63103 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____63157 -> aux (h :: acc) t))
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
      let uu____63181 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____63181 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2985_63223 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2985_63223.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2985_63223.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2985_63223.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2985_63223.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  