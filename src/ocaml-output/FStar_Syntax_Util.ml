open Prims
let (tts_f :
  (FStar_Syntax_Syntax.term -> Prims.string) FStar_Pervasives_Native.option
    FStar_ST.ref)
  = FStar_Util.mk_ref FStar_Pervasives_Native.None 
let (tts : FStar_Syntax_Syntax.term -> Prims.string) =
  fun t  ->
    let uu____44884 = FStar_ST.op_Bang tts_f  in
    match uu____44884 with
    | FStar_Pervasives_Native.None  -> "<<hook unset>>"
    | FStar_Pervasives_Native.Some f -> f t
  
let (qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident)
  =
  fun lid  ->
    fun id1  ->
      let uu____44948 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id1])
         in
      FStar_Ident.set_lid_range uu____44948 id1.FStar_Ident.idRange
  
let (mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident) =
  fun lid  ->
    let uu____44955 =
      let uu____44958 =
        let uu____44961 =
          FStar_Ident.mk_ident
            ((Prims.op_Hat FStar_Ident.reserved_prefix
                (Prims.op_Hat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))
           in
        [uu____44961]  in
      FStar_List.append lid.FStar_Ident.ns uu____44958  in
    FStar_Ident.lid_of_ids uu____44955
  
let (is_name : FStar_Ident.lident -> Prims.bool) =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder :
  'Auu____44979 .
    (FStar_Syntax_Syntax.bv * 'Auu____44979) ->
      (FStar_Syntax_Syntax.term * 'Auu____44979)
  =
  fun uu____44992  ->
    match uu____44992 with
    | (b,imp) ->
        let uu____44999 = FStar_Syntax_Syntax.bv_to_name b  in
        (uu____44999, imp)
  
let (args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list)
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____45051 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____45051
            then []
            else
              (let uu____45070 = arg_of_non_null_binder b  in [uu____45070])))
  
let (args_of_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.args))
  =
  fun binders  ->
    let uu____45105 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____45187 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45187
              then
                let b1 =
                  let uu____45213 =
                    FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                      (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____45213, (FStar_Pervasives_Native.snd b))  in
                let uu____45220 = arg_of_non_null_binder b1  in
                (b1, uu____45220)
              else
                (let uu____45243 = arg_of_non_null_binder b  in
                 (b, uu____45243))))
       in
    FStar_All.pipe_right uu____45105 FStar_List.unzip
  
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
              let uu____45377 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____45377
              then
                let uu____45386 = b  in
                match uu____45386 with
                | (a,imp) ->
                    let b1 =
                      let uu____45406 =
                        let uu____45408 = FStar_Util.string_of_int i  in
                        Prims.op_Hat "_" uu____45408  in
                      FStar_Ident.id_of_text uu____45406  in
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
        let uu____45453 =
          let uu____45460 =
            let uu____45461 =
              let uu____45476 = name_binders binders  in (uu____45476, comp)
               in
            FStar_Syntax_Syntax.Tm_arrow uu____45461  in
          FStar_Syntax_Syntax.mk uu____45460  in
        uu____45453 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
    | uu____45498 -> t
  
let (null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45535  ->
            match uu____45535 with
            | (t,imp) ->
                let uu____45546 =
                  let uu____45547 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives_Native.fst uu____45547
                   in
                (uu____45546, imp)))
  
let (binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.binders)
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____45602  ->
            match uu____45602 with
            | (t,imp) ->
                let uu____45619 =
                  FStar_Syntax_Syntax.new_bv
                    (FStar_Pervasives_Native.Some (t.FStar_Syntax_Syntax.pos))
                    t
                   in
                (uu____45619, imp)))
  
let (binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list)
  =
  fun fvs  ->
    let uu____45632 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____45632
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst : 'Auu____45644 . 'Auu____45644 -> 'Auu____45644 Prims.list =
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
          (fun uu____45770  ->
             fun uu____45771  ->
               match (uu____45770, uu____45771) with
               | ((x,uu____45797),(y,uu____45799)) ->
                   let uu____45820 =
                     let uu____45827 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____45827)  in
                   FStar_Syntax_Syntax.NT uu____45820) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec (unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____45843) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45849,uu____45850) ->
        unmeta e2
    | uu____45891 -> e1
  
let rec (unmeta_safe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e',m) ->
        (match m with
         | FStar_Syntax_Syntax.Meta_monadic uu____45905 -> e1
         | FStar_Syntax_Syntax.Meta_monadic_lift uu____45912 -> e1
         | uu____45921 -> unmeta_safe e')
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____45923,uu____45924) ->
        unmeta_safe e2
    | uu____45965 -> e1
  
let rec (univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int))
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____45984 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____45987 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____46001 = univ_kernel u1  in
        (match uu____46001 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____46018 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____46027 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let (constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int) =
  fun u  ->
    let uu____46042 = univ_kernel u  in
    FStar_Pervasives_Native.snd uu____46042
  
let rec (compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int)
  =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____46062,uu____46063) ->
          failwith "Impossible: compare_univs"
      | (uu____46067,FStar_Syntax_Syntax.U_bvar uu____46068) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____46073) ->
          ~- (Prims.parse_int "1")
      | (uu____46075,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____46078) -> ~- (Prims.parse_int "1")
      | (uu____46080,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____46084,FStar_Syntax_Syntax.U_unif
         uu____46085) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____46095,FStar_Syntax_Syntax.U_name
         uu____46096) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____46124 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____46126 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____46124 - uu____46126
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____46162 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____46162
                 (fun uu____46178  ->
                    match uu____46178 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0")
                        then FStar_Pervasives_Native.Some c
                        else FStar_Pervasives_Native.None)
                in
             match copt with
             | FStar_Pervasives_Native.None  -> (Prims.parse_int "0")
             | FStar_Pervasives_Native.Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____46206,uu____46207) ->
          ~- (Prims.parse_int "1")
      | (uu____46211,FStar_Syntax_Syntax.U_max uu____46212) ->
          (Prims.parse_int "1")
      | uu____46216 ->
          let uu____46221 = univ_kernel u1  in
          (match uu____46221 with
           | (k1,n1) ->
               let uu____46232 = univ_kernel u2  in
               (match uu____46232 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let (eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool)
  =
  fun u1  ->
    fun u2  ->
      let uu____46263 = compare_univs u1 u2  in
      uu____46263 = (Prims.parse_int "0")
  
let (ml_comp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp)
  =
  fun t  ->
    fun r  ->
      let uu____46282 =
        let uu____46283 =
          FStar_Ident.set_lid_range FStar_Parser_Const.effect_ML_lid r  in
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_zero];
          FStar_Syntax_Syntax.effect_name = uu____46283;
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____46282
  
let (comp_effect_name :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> FStar_Ident.lident)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
    | FStar_Syntax_Syntax.Total uu____46303 ->
        FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.GTotal uu____46312 ->
        FStar_Parser_Const.effect_GTot_lid
  
let (comp_flags :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____46335 -> [FStar_Syntax_Syntax.TOTAL]
    | FStar_Syntax_Syntax.GTotal uu____46344 ->
        [FStar_Syntax_Syntax.SOMETRIVIAL]
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags
  
let (comp_to_comp_typ_nouniv :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,u_opt) ->
        let uu____46371 =
          let uu____46372 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46372  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46371;
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
        let uu____46401 =
          let uu____46402 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
          FStar_Util.dflt [] uu____46402  in
        {
          FStar_Syntax_Syntax.comp_univs = uu____46401;
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
      let uu___631_46438 = c  in
      let uu____46439 =
        let uu____46440 =
          let uu___633_46441 = comp_to_comp_typ_nouniv c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___633_46441.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___633_46441.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___633_46441.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___633_46441.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____46440  in
      {
        FStar_Syntax_Syntax.n = uu____46439;
        FStar_Syntax_Syntax.pos = (uu___631_46438.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___631_46438.FStar_Syntax_Syntax.vars)
      }
  
let (lcomp_set_flags :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.cflag Prims.list -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun fs  ->
      let comp_typ_set_flags c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total uu____46467 -> c
        | FStar_Syntax_Syntax.GTotal uu____46476 -> c
        | FStar_Syntax_Syntax.Comp ct ->
            let ct1 =
              let uu___645_46487 = ct  in
              {
                FStar_Syntax_Syntax.comp_univs =
                  (uu___645_46487.FStar_Syntax_Syntax.comp_univs);
                FStar_Syntax_Syntax.effect_name =
                  (uu___645_46487.FStar_Syntax_Syntax.effect_name);
                FStar_Syntax_Syntax.result_typ =
                  (uu___645_46487.FStar_Syntax_Syntax.result_typ);
                FStar_Syntax_Syntax.effect_args =
                  (uu___645_46487.FStar_Syntax_Syntax.effect_args);
                FStar_Syntax_Syntax.flags = fs
              }  in
            let uu___648_46488 = c  in
            {
              FStar_Syntax_Syntax.n = (FStar_Syntax_Syntax.Comp ct1);
              FStar_Syntax_Syntax.pos =
                (uu___648_46488.FStar_Syntax_Syntax.pos);
              FStar_Syntax_Syntax.vars =
                (uu___648_46488.FStar_Syntax_Syntax.vars)
            }
         in
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name
        lc.FStar_Syntax_Syntax.res_typ fs
        (fun uu____46491  ->
           let uu____46492 = FStar_Syntax_Syntax.lcomp_comp lc  in
           comp_typ_set_flags uu____46492)
  
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
    | uu____46532 ->
        failwith "Assertion failed: Computation type without universe"
  
let (is_named_tot :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 ->
        FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Tot_lid
    | FStar_Syntax_Syntax.Total uu____46547 -> true
    | FStar_Syntax_Syntax.GTotal uu____46557 -> false
  
let (is_total_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals (comp_effect_name c)
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right (comp_flags c)
         (FStar_Util.for_some
            (fun uu___402_46582  ->
               match uu___402_46582 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46586 -> false)))
  
let (is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Parser_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___403_46599  ->
               match uu___403_46599 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46603 -> false)))
  
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
            (fun uu___404_46616  ->
               match uu___404_46616 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____46620 -> false)))
  
let (is_partial_return :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___405_46637  ->
            match uu___405_46637 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46641 -> false))
  
let (is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___406_46654  ->
            match uu___406_46654 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____46658 -> false))
  
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
    | FStar_Syntax_Syntax.Total uu____46690 -> true
    | FStar_Syntax_Syntax.GTotal uu____46700 -> false
    | FStar_Syntax_Syntax.Comp ct ->
        ((is_total_comp c) ||
           (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
          ||
          (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
             (FStar_Util.for_some
                (fun uu___407_46715  ->
                   match uu___407_46715 with
                   | FStar_Syntax_Syntax.LEMMA  -> true
                   | uu____46718 -> false)))
  
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
            (fun uu___408_46763  ->
               match uu___408_46763 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____46766 -> false)))
  
let (is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool) =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let (is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46782 =
      let uu____46783 = FStar_Syntax_Subst.compress t  in
      uu____46783.FStar_Syntax_Syntax.n  in
    match uu____46782 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46787,c) -> is_pure_or_ghost_comp c
    | uu____46809 -> true
  
let (is_lemma_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp ct ->
        FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
          FStar_Parser_Const.effect_Lemma_lid
    | uu____46824 -> false
  
let (is_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____46833 =
      let uu____46834 = FStar_Syntax_Subst.compress t  in
      uu____46834.FStar_Syntax_Syntax.n  in
    match uu____46833 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____46838,c) -> is_lemma_comp c
    | uu____46860 -> false
  
let rec (head_of : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____46868 =
      let uu____46869 = FStar_Syntax_Subst.compress t  in
      uu____46869.FStar_Syntax_Syntax.n  in
    match uu____46868 with
    | FStar_Syntax_Syntax.Tm_app (t1,uu____46873) -> head_of t1
    | FStar_Syntax_Syntax.Tm_match (t1,uu____46899) -> head_of t1
    | FStar_Syntax_Syntax.Tm_abs (uu____46936,t1,uu____46938) -> head_of t1
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____46964,uu____46965) ->
        head_of t1
    | FStar_Syntax_Syntax.Tm_meta (t1,uu____47007) -> head_of t1
    | uu____47012 -> t
  
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
    | uu____47090 -> (t1, [])
  
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
        let uu____47172 = head_and_args' head1  in
        (match uu____47172 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____47241 -> (t1, [])
  
let (un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____47268) ->
        FStar_Syntax_Subst.compress t2
    | uu____47273 -> t1
  
let (is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____47281 =
      let uu____47282 = FStar_Syntax_Subst.compress t  in
      uu____47282.FStar_Syntax_Syntax.n  in
    match uu____47281 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____47286,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Parser_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____47314)::uu____47315 ->
                  let pats' = unmeta pats  in
                  let uu____47375 = head_and_args pats'  in
                  (match uu____47375 with
                   | (head1,uu____47394) ->
                       let uu____47419 =
                         let uu____47420 = un_uinst head1  in
                         uu____47420.FStar_Syntax_Syntax.n  in
                       (match uu____47419 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.cons_lid
                        | uu____47425 -> false))
              | uu____47427 -> false)
         | uu____47439 -> false)
    | uu____47441 -> false
  
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
                (fun uu___409_47460  ->
                   match uu___409_47460 with
                   | FStar_Syntax_Syntax.MLEFFECT  -> true
                   | uu____47463 -> false)))
    | uu____47465 -> false
  
let (comp_result :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total (t,uu____47482) -> t
    | FStar_Syntax_Syntax.GTotal (t,uu____47492) -> t
    | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
  
let (set_result_typ :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp)
  =
  fun c  ->
    fun t  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____47521 ->
          FStar_Syntax_Syntax.mk_Total t
      | FStar_Syntax_Syntax.GTotal uu____47530 ->
          FStar_Syntax_Syntax.mk_GTotal t
      | FStar_Syntax_Syntax.Comp ct ->
          FStar_Syntax_Syntax.mk_Comp
            (let uu___827_47542 = ct  in
             {
               FStar_Syntax_Syntax.comp_univs =
                 (uu___827_47542.FStar_Syntax_Syntax.comp_univs);
               FStar_Syntax_Syntax.effect_name =
                 (uu___827_47542.FStar_Syntax_Syntax.effect_name);
               FStar_Syntax_Syntax.result_typ = t;
               FStar_Syntax_Syntax.effect_args =
                 (uu___827_47542.FStar_Syntax_Syntax.effect_args);
               FStar_Syntax_Syntax.flags =
                 (uu___827_47542.FStar_Syntax_Syntax.flags)
             })
  
let (set_result_typ_lc :
  FStar_Syntax_Syntax.lcomp ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.lcomp)
  =
  fun lc  ->
    fun t  ->
      FStar_Syntax_Syntax.mk_lcomp lc.FStar_Syntax_Syntax.eff_name t
        lc.FStar_Syntax_Syntax.cflags
        (fun uu____47556  ->
           let uu____47557 = FStar_Syntax_Syntax.lcomp_comp lc  in
           set_result_typ uu____47557 t)
  
let (is_trivial_wp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> Prims.bool) =
  fun c  ->
    FStar_All.pipe_right (comp_flags c)
      (FStar_Util.for_some
         (fun uu___410_47575  ->
            match uu___410_47575 with
            | FStar_Syntax_Syntax.TOTAL  -> true
            | FStar_Syntax_Syntax.RETURN  -> true
            | uu____47579 -> false))
  
let (comp_effect_args : FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.args)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Total uu____47587 -> []
    | FStar_Syntax_Syntax.GTotal uu____47604 -> []
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
    | uu____47648 -> false
  
let rec (unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____47658,uu____47659) ->
        unascribe e2
    | uu____47700 -> e1
  
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
      | FStar_Syntax_Syntax.Tm_ascribed (t',uu____47753,uu____47754) ->
          ascribe t' k
      | uu____47795 ->
          FStar_Syntax_Syntax.mk
            (FStar_Syntax_Syntax.Tm_ascribed
               (t, k, FStar_Pervasives_Native.None))
            FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (unfold_lazy : FStar_Syntax_Syntax.lazyinfo -> FStar_Syntax_Syntax.term)
  =
  fun i  ->
    let uu____47822 =
      let uu____47831 = FStar_ST.op_Bang FStar_Syntax_Syntax.lazy_chooser  in
      FStar_Util.must uu____47831  in
    uu____47822 i.FStar_Syntax_Syntax.lkind i
  
let rec (unlazy : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47887 =
      let uu____47888 = FStar_Syntax_Subst.compress t  in
      uu____47888.FStar_Syntax_Syntax.n  in
    match uu____47887 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____47892 = unfold_lazy i  in
        FStar_All.pipe_left unlazy uu____47892
    | uu____47893 -> t
  
let rec (unlazy_emb : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____47900 =
      let uu____47901 = FStar_Syntax_Subst.compress t  in
      uu____47901.FStar_Syntax_Syntax.n  in
    match uu____47900 with
    | FStar_Syntax_Syntax.Tm_lazy i ->
        (match i.FStar_Syntax_Syntax.lkind with
         | FStar_Syntax_Syntax.Lazy_embedding uu____47905 ->
             let uu____47914 = unfold_lazy i  in
             FStar_All.pipe_left unlazy uu____47914
         | uu____47915 -> t)
    | uu____47916 -> t
  
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
      | uu____47940 -> false
  
let rec unlazy_as_t :
  'Auu____47953 .
    FStar_Syntax_Syntax.lazy_kind ->
      FStar_Syntax_Syntax.term -> 'Auu____47953
  =
  fun k  ->
    fun t  ->
      let uu____47964 =
        let uu____47965 = FStar_Syntax_Subst.compress t  in
        uu____47965.FStar_Syntax_Syntax.n  in
      match uu____47964 with
      | FStar_Syntax_Syntax.Tm_lazy
          { FStar_Syntax_Syntax.blob = v1; FStar_Syntax_Syntax.lkind = k';
            FStar_Syntax_Syntax.ltyp = uu____47970;
            FStar_Syntax_Syntax.rng = uu____47971;_}
          when eq_lazy_kind k k' -> FStar_Dyn.undyn v1
      | uu____47974 -> failwith "Not a Tm_lazy of the expected kind"
  
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
            let uu____48015 = FStar_Dyn.mkdyn t  in
            {
              FStar_Syntax_Syntax.blob = uu____48015;
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
    let uu____48028 =
      let uu____48043 = unascribe t  in head_and_args' uu____48043  in
    match uu____48028 with
    | (hd1,args) ->
        FStar_Syntax_Syntax.mk_Tm_app hd1 args FStar_Pervasives_Native.None
          t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let (uu___is_Equal : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____48077 -> false
  
let (uu___is_NotEqual : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____48088 -> false
  
let (uu___is_Unknown : eq_result -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____48099 -> false
  
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
      | (NotEqual ,uu____48149) -> NotEqual
      | (uu____48150,NotEqual ) -> NotEqual
      | (Unknown ,uu____48151) -> Unknown
      | (uu____48152,Unknown ) -> Unknown
  
let rec (eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result) =
  fun t1  ->
    fun t2  ->
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___411_48273 = if uu___411_48273 then Equal else Unknown
         in
      let equal_iff uu___412_48284 =
        if uu___412_48284 then Equal else NotEqual  in
      let eq_and f g = match f with | Equal  -> g () | uu____48305 -> Unknown
         in
      let equal_data f1 args1 f2 args2 =
        let uu____48327 = FStar_Syntax_Syntax.fv_eq f1 f2  in
        if uu____48327
        then
          let uu____48331 = FStar_List.zip args1 args2  in
          FStar_All.pipe_left
            (FStar_List.fold_left
               (fun acc  ->
                  fun uu____48408  ->
                    match uu____48408 with
                    | ((a1,q1),(a2,q2)) ->
                        let uu____48449 = eq_tm a1 a2  in
                        eq_inj acc uu____48449) Equal) uu____48331
        else NotEqual  in
      let heads_and_args_in_case_both_data =
        let uu____48463 =
          let uu____48480 = FStar_All.pipe_right t11 unmeta  in
          FStar_All.pipe_right uu____48480 head_and_args  in
        match uu____48463 with
        | (head1,args1) ->
            let uu____48533 =
              let uu____48550 = FStar_All.pipe_right t21 unmeta  in
              FStar_All.pipe_right uu____48550 head_and_args  in
            (match uu____48533 with
             | (head2,args2) ->
                 let uu____48603 =
                   let uu____48608 =
                     let uu____48609 = un_uinst head1  in
                     uu____48609.FStar_Syntax_Syntax.n  in
                   let uu____48612 =
                     let uu____48613 = un_uinst head2  in
                     uu____48613.FStar_Syntax_Syntax.n  in
                   (uu____48608, uu____48612)  in
                 (match uu____48603 with
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
                  | uu____48640 -> FStar_Pervasives_Native.None))
         in
      let uu____48653 =
        let uu____48658 =
          let uu____48659 = unmeta t11  in uu____48659.FStar_Syntax_Syntax.n
           in
        let uu____48662 =
          let uu____48663 = unmeta t21  in uu____48663.FStar_Syntax_Syntax.n
           in
        (uu____48658, uu____48662)  in
      match uu____48653 with
      | (FStar_Syntax_Syntax.Tm_bvar bv1,FStar_Syntax_Syntax.Tm_bvar bv2) ->
          equal_if
            (bv1.FStar_Syntax_Syntax.index = bv2.FStar_Syntax_Syntax.index)
      | (FStar_Syntax_Syntax.Tm_lazy uu____48669,uu____48670) ->
          let uu____48671 = unlazy t11  in eq_tm uu____48671 t21
      | (uu____48672,FStar_Syntax_Syntax.Tm_lazy uu____48673) ->
          let uu____48674 = unlazy t21  in eq_tm t11 uu____48674
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | uu____48677 when
          FStar_All.pipe_right heads_and_args_in_case_both_data
            FStar_Util.is_some
          ->
          let uu____48701 =
            FStar_All.pipe_right heads_and_args_in_case_both_data
              FStar_Util.must
             in
          FStar_All.pipe_right uu____48701
            (fun uu____48749  ->
               match uu____48749 with
               | (f,args1,g,args2) -> equal_data f args1 g args2)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____48764 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____48764
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____48778 = eq_tm f g  in
          eq_and uu____48778
            (fun uu____48781  ->
               let uu____48782 = eq_univs_list us vs  in equal_if uu____48782)
      | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48784),uu____48785) -> Unknown
      | (uu____48786,FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
         uu____48787)) -> Unknown
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____48790 = FStar_Const.eq_const c d  in
          equal_iff uu____48790
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,([],uu____48793)),FStar_Syntax_Syntax.Tm_uvar
         (u2,([],uu____48795))) ->
          let uu____48824 =
            FStar_Syntax_Unionfind.equiv u1.FStar_Syntax_Syntax.ctx_uvar_head
              u2.FStar_Syntax_Syntax.ctx_uvar_head
             in
          equal_if uu____48824
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____48878 =
            let uu____48883 =
              let uu____48884 = un_uinst h1  in
              uu____48884.FStar_Syntax_Syntax.n  in
            let uu____48887 =
              let uu____48888 = un_uinst h2  in
              uu____48888.FStar_Syntax_Syntax.n  in
            (uu____48883, uu____48887)  in
          (match uu____48878 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (FStar_Syntax_Syntax.fv_eq f1 f2) &&
                 (let uu____48894 =
                    let uu____48896 = FStar_Syntax_Syntax.lid_of_fv f1  in
                    FStar_Ident.string_of_lid uu____48896  in
                  FStar_List.mem uu____48894 injectives)
               -> equal_data f1 args1 f2 args2
           | uu____48898 ->
               let uu____48903 = eq_tm h1 h2  in
               eq_and uu____48903 (fun uu____48905  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) ->
          if (FStar_List.length bs1) = (FStar_List.length bs2)
          then
            let uu____49011 = FStar_List.zip bs1 bs2  in
            let uu____49074 = eq_tm t12 t22  in
            FStar_List.fold_right
              (fun uu____49111  ->
                 fun a  ->
                   match uu____49111 with
                   | (b1,b2) ->
                       eq_and a (fun uu____49204  -> branch_matches b1 b2))
              uu____49011 uu____49074
          else Unknown
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____49209 = eq_univs u v1  in equal_if uu____49209
      | (FStar_Syntax_Syntax.Tm_quoted (t12,q1),FStar_Syntax_Syntax.Tm_quoted
         (t22,q2)) ->
          let uu____49223 = eq_quoteinfo q1 q2  in
          eq_and uu____49223 (fun uu____49225  -> eq_tm t12 t22)
      | (FStar_Syntax_Syntax.Tm_refine
         (t12,phi1),FStar_Syntax_Syntax.Tm_refine (t22,phi2)) ->
          let uu____49238 =
            eq_tm t12.FStar_Syntax_Syntax.sort t22.FStar_Syntax_Syntax.sort
             in
          eq_and uu____49238 (fun uu____49240  -> eq_tm phi1 phi2)
      | uu____49241 -> Unknown

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
      | ([],uu____49313) -> NotEqual
      | (uu____49344,[]) -> NotEqual
      | ((x1,t1)::a11,(x2,t2)::a21) ->
          if Prims.op_Negation (FStar_Syntax_Syntax.bv_eq x1 x2)
          then NotEqual
          else
            (let uu____49436 = eq_tm t1 t2  in
             match uu____49436 with
             | NotEqual  -> NotEqual
             | Unknown  ->
                 let uu____49437 = eq_antiquotes a11 a21  in
                 (match uu____49437 with
                  | NotEqual  -> NotEqual
                  | uu____49438 -> Unknown)
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
      | (FStar_Pervasives_Native.None ,uu____49453) -> NotEqual
      | (uu____49460,FStar_Pervasives_Native.None ) -> NotEqual
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit
         b1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit b2))
          when b1 = b2 -> Equal
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta
         t1),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Meta t2)) ->
          eq_tm t1 t2
      | (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality
         ),FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality )) ->
          Equal
      | uu____49490 -> NotEqual

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
        | (uu____49582,uu____49583) -> false  in
      let uu____49593 = b1  in
      match uu____49593 with
      | (p1,w1,t1) ->
          let uu____49627 = b2  in
          (match uu____49627 with
           | (p2,w2,t2) ->
               let uu____49661 = FStar_Syntax_Syntax.eq_pat p1 p2  in
               if uu____49661
               then
                 let uu____49664 =
                   (let uu____49668 = eq_tm t1 t2  in uu____49668 = Equal) &&
                     (related_by
                        (fun t11  ->
                           fun t21  ->
                             let uu____49677 = eq_tm t11 t21  in
                             uu____49677 = Equal) w1 w2)
                    in
                 (if uu____49664 then Equal else Unknown)
               else Unknown)

and (eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____49742)::a11,(b,uu____49745)::b1) ->
          let uu____49819 = eq_tm a b  in
          (match uu____49819 with
           | Equal  -> eq_args a11 b1
           | uu____49820 -> Unknown)
      | uu____49821 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____49857) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____49863,uu____49864) ->
        unrefine t2
    | uu____49905 -> t1
  
let rec (is_uvar : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____49913 =
      let uu____49914 = FStar_Syntax_Subst.compress t  in
      uu____49914.FStar_Syntax_Syntax.n  in
    match uu____49913 with
    | FStar_Syntax_Syntax.Tm_uvar uu____49918 -> true
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____49933) -> is_uvar t1
    | FStar_Syntax_Syntax.Tm_app uu____49938 ->
        let uu____49955 =
          let uu____49956 = FStar_All.pipe_right t head_and_args  in
          FStar_All.pipe_right uu____49956 FStar_Pervasives_Native.fst  in
        FStar_All.pipe_right uu____49955 is_uvar
    | FStar_Syntax_Syntax.Tm_ascribed (t1,uu____50019,uu____50020) ->
        is_uvar t1
    | uu____50061 -> false
  
let rec (is_unit : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50070 =
      let uu____50071 = unrefine t  in uu____50071.FStar_Syntax_Syntax.n  in
    match uu____50070 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv
             FStar_Parser_Const.auto_squash_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50077) -> is_unit head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50103) -> is_unit t1
    | uu____50108 -> false
  
let (is_eqtype_no_unrefine : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50117 =
      let uu____50118 = FStar_Syntax_Subst.compress t  in
      uu____50118.FStar_Syntax_Syntax.n  in
    match uu____50117 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.eqtype_lid
    | uu____50123 -> false
  
let rec (non_informative : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50132 =
      let uu____50133 = unrefine t  in uu____50133.FStar_Syntax_Syntax.n  in
    match uu____50132 with
    | FStar_Syntax_Syntax.Tm_type uu____50137 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____50141) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____50167) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____50172,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____50194 -> false
  
let (is_fun : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun e  ->
    let uu____50203 =
      let uu____50204 = FStar_Syntax_Subst.compress e  in
      uu____50204.FStar_Syntax_Syntax.n  in
    match uu____50203 with
    | FStar_Syntax_Syntax.Tm_abs uu____50208 -> true
    | uu____50228 -> false
  
let (is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____50237 =
      let uu____50238 = FStar_Syntax_Subst.compress t  in
      uu____50238.FStar_Syntax_Syntax.n  in
    match uu____50237 with
    | FStar_Syntax_Syntax.Tm_arrow uu____50242 -> true
    | uu____50258 -> false
  
let rec (pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____50268) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____50274,uu____50275) ->
        pre_typ t2
    | uu____50316 -> t1
  
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
      let uu____50341 =
        let uu____50342 = un_uinst typ1  in uu____50342.FStar_Syntax_Syntax.n
         in
      match uu____50341 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid ->
               FStar_Pervasives_Native.Some args
           | uu____50407 -> FStar_Pervasives_Native.None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid ->
          FStar_Pervasives_Native.Some []
      | uu____50437 -> FStar_Pervasives_Native.None
  
let (lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____50458,lids) -> lids
    | FStar_Syntax_Syntax.Sig_splice (lids,uu____50465) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____50470,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____50481,uu____50482,uu____50483,uu____50484,uu____50485) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____50495,uu____50496,uu____50497,uu____50498) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____50504,uu____50505,uu____50506,uu____50507,uu____50508) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____50516,uu____50517) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____50519,uu____50520) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____50523 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____50524 -> []
    | FStar_Syntax_Syntax.Sig_main uu____50525 -> []
  
let (lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Ident.lident FStar_Pervasives_Native.option)
  =
  fun se  ->
    match lids_of_sigelt se with
    | l::[] -> FStar_Pervasives_Native.Some l
    | uu____50539 -> FStar_Pervasives_Native.None
  
let (quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let (range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range) =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let (range_of_lbname :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Range.range)
  =
  fun uu___413_50565  ->
    match uu___413_50565 with
    | FStar_Util.Inl x -> FStar_Syntax_Syntax.range_of_bv x
    | FStar_Util.Inr fv ->
        FStar_Ident.range_of_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  
let range_of_arg :
  'Auu____50579 'Auu____50580 .
    ('Auu____50579 FStar_Syntax_Syntax.syntax * 'Auu____50580) ->
      FStar_Range.range
  =
  fun uu____50591  ->
    match uu____50591 with | (hd1,uu____50599) -> hd1.FStar_Syntax_Syntax.pos
  
let range_of_args :
  'Auu____50613 'Auu____50614 .
    ('Auu____50613 FStar_Syntax_Syntax.syntax * 'Auu____50614) Prims.list ->
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
      | uu____50712 ->
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
      let uu____50771 =
        FStar_List.map
          (fun uu____50798  ->
             match uu____50798 with
             | (bv,aq) ->
                 let uu____50817 = FStar_Syntax_Syntax.bv_to_name bv  in
                 (uu____50817, aq)) bs
         in
      mk_app f uu____50771
  
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
          let uu____50867 = FStar_Ident.range_of_lid l  in
          let uu____50868 =
            let uu____50877 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            FStar_Syntax_Syntax.mk uu____50877  in
          uu____50868 FStar_Pervasives_Native.None uu____50867
      | uu____50885 ->
          let e =
            let uu____50899 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.delta_constant
                (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
               in
            mk_app uu____50899 args  in
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
          let uu____50976 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____50976
          then
            let uu____50979 =
              let uu____50985 =
                let uu____50987 = FStar_Util.string_of_int i  in
                Prims.op_Hat "_" uu____50987  in
              let uu____50990 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____50985, uu____50990)  in
            FStar_Ident.mk_ident uu____50979
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___1421_50995 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___1421_50995.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___1421_50995.FStar_Syntax_Syntax.sort)
          }  in
        let uu____50996 = mk_field_projector_name_from_ident lid nm  in
        (uu____50996, y)
  
let (ses_of_sigbundle :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_bundle (ses,uu____51008) -> ses
    | uu____51017 -> failwith "ses_of_sigbundle: not a Sig_bundle"
  
let (eff_decl_of_new_effect :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.eff_decl) =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_new_effect ne -> ne
    | uu____51028 -> failwith "eff_decl_of_new_effect: not a Sig_new_effect"
  
let (set_uvar : FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> unit)
  =
  fun uv  ->
    fun t  ->
      let uu____51041 = FStar_Syntax_Unionfind.find uv  in
      match uu____51041 with
      | FStar_Pervasives_Native.Some uu____51044 ->
          let uu____51045 =
            let uu____51047 =
              let uu____51049 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____51049  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____51047  in
          failwith uu____51045
      | uu____51054 -> FStar_Syntax_Unionfind.change uv t
  
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
      | uu____51137 -> q1 = q2
  
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
              let uu____51183 =
                let uu___1482_51184 = rc  in
                let uu____51185 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___1482_51184.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____51185;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___1482_51184.FStar_Syntax_Syntax.residual_flags)
                }  in
              FStar_Pervasives_Native.Some uu____51183
           in
        match bs with
        | [] -> t
        | uu____51202 ->
            let body =
              let uu____51204 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____51204  in
            (match body.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt') ->
                 let uu____51234 =
                   let uu____51241 =
                     let uu____51242 =
                       let uu____51261 =
                         let uu____51270 =
                           FStar_Syntax_Subst.close_binders bs  in
                         FStar_List.append uu____51270 bs'  in
                       let uu____51285 = close_lopt lopt'  in
                       (uu____51261, t1, uu____51285)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51242  in
                   FStar_Syntax_Syntax.mk uu____51241  in
                 uu____51234 FStar_Pervasives_Native.None
                   t1.FStar_Syntax_Syntax.pos
             | uu____51303 ->
                 let uu____51304 =
                   let uu____51311 =
                     let uu____51312 =
                       let uu____51331 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____51340 = close_lopt lopt  in
                       (uu____51331, body, uu____51340)  in
                     FStar_Syntax_Syntax.Tm_abs uu____51312  in
                   FStar_Syntax_Syntax.mk uu____51311  in
                 uu____51304 FStar_Pervasives_Native.None
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
      | uu____51399 ->
          let uu____51408 =
            let uu____51415 =
              let uu____51416 =
                let uu____51431 = FStar_Syntax_Subst.close_binders bs  in
                let uu____51440 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____51431, uu____51440)  in
              FStar_Syntax_Syntax.Tm_arrow uu____51416  in
            FStar_Syntax_Syntax.mk uu____51415  in
          uu____51408 FStar_Pervasives_Native.None c.FStar_Syntax_Syntax.pos
  
let (flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
    FStar_Pervasives_Native.option) Prims.list ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____51492 =
        let uu____51493 = FStar_Syntax_Subst.compress t  in
        uu____51493.FStar_Syntax_Syntax.n  in
      match uu____51492 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____51523) ->
               let uu____51532 =
                 let uu____51533 = FStar_Syntax_Subst.compress tres  in
                 uu____51533.FStar_Syntax_Syntax.n  in
               (match uu____51532 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c'))
                      FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
                | uu____51576 -> t)
           | uu____51577 -> t)
      | uu____51578 -> t
  
let (refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun b  ->
    fun t  ->
      let uu____51596 =
        let uu____51597 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____51597 t.FStar_Syntax_Syntax.pos  in
      let uu____51598 =
        let uu____51605 =
          let uu____51606 =
            let uu____51613 =
              let uu____51616 =
                let uu____51617 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____51617]  in
              FStar_Syntax_Subst.close uu____51616 t  in
            (b, uu____51613)  in
          FStar_Syntax_Syntax.Tm_refine uu____51606  in
        FStar_Syntax_Syntax.mk uu____51605  in
      uu____51598 FStar_Pervasives_Native.None uu____51596
  
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
        let uu____51700 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____51700 with
         | (bs1,c1) ->
             let uu____51719 = is_total_comp c1  in
             if uu____51719
             then
               let uu____51734 = arrow_formals_comp (comp_result c1)  in
               (match uu____51734 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____51801;
           FStar_Syntax_Syntax.index = uu____51802;
           FStar_Syntax_Syntax.sort = s;_},uu____51804)
        ->
        let rec aux s1 k2 =
          let uu____51835 =
            let uu____51836 = FStar_Syntax_Subst.compress s1  in
            uu____51836.FStar_Syntax_Syntax.n  in
          match uu____51835 with
          | FStar_Syntax_Syntax.Tm_arrow uu____51851 -> arrow_formals_comp s1
          | FStar_Syntax_Syntax.Tm_refine
              ({ FStar_Syntax_Syntax.ppname = uu____51866;
                 FStar_Syntax_Syntax.index = uu____51867;
                 FStar_Syntax_Syntax.sort = s2;_},uu____51869)
              -> aux s2 k2
          | uu____51877 ->
              let uu____51878 = FStar_Syntax_Syntax.mk_Total k2  in
              ([], uu____51878)
           in
        aux s k1
    | uu____51893 ->
        let uu____51894 = FStar_Syntax_Syntax.mk_Total k1  in
        ([], uu____51894)
  
let rec (arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
      FStar_Pervasives_Native.option) Prims.list * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax))
  =
  fun k  ->
    let uu____51929 = arrow_formals_comp k  in
    match uu____51929 with | (bs,c) -> (bs, (comp_result c))
  
let (let_rec_arity :
  FStar_Syntax_Syntax.letbinding ->
    (Prims.int * Prims.bool Prims.list FStar_Pervasives_Native.option))
  =
  fun lb  ->
    let rec arrow_until_decreases k =
      let k1 = FStar_Syntax_Subst.compress k  in
      match k1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let uu____52071 = FStar_Syntax_Subst.open_comp bs c  in
          (match uu____52071 with
           | (bs1,c1) ->
               let ct = comp_to_comp_typ c1  in
               let uu____52095 =
                 FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                   (FStar_Util.find_opt
                      (fun uu___414_52104  ->
                         match uu___414_52104 with
                         | FStar_Syntax_Syntax.DECREASES uu____52106 -> true
                         | uu____52110 -> false))
                  in
               (match uu____52095 with
                | FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.DECREASES
                    d) -> (bs1, (FStar_Pervasives_Native.Some d))
                | uu____52145 ->
                    let uu____52148 = is_total_comp c1  in
                    if uu____52148
                    then
                      let uu____52167 =
                        arrow_until_decreases (comp_result c1)  in
                      (match uu____52167 with
                       | (bs',d) -> ((FStar_List.append bs1 bs'), d))
                    else (bs1, FStar_Pervasives_Native.None)))
      | FStar_Syntax_Syntax.Tm_refine
          ({ FStar_Syntax_Syntax.ppname = uu____52260;
             FStar_Syntax_Syntax.index = uu____52261;
             FStar_Syntax_Syntax.sort = k2;_},uu____52263)
          -> arrow_until_decreases k2
      | uu____52271 -> ([], FStar_Pervasives_Native.None)  in
    let uu____52292 = arrow_until_decreases lb.FStar_Syntax_Syntax.lbtyp  in
    match uu____52292 with
    | (bs,dopt) ->
        let n_univs = FStar_List.length lb.FStar_Syntax_Syntax.lbunivs  in
        let uu____52346 =
          FStar_Util.map_opt dopt
            (fun d  ->
               let d_bvs = FStar_Syntax_Free.names d  in
               let uu____52367 =
                 FStar_Common.tabulate n_univs (fun uu____52377  -> false)
                  in
               let uu____52380 =
                 FStar_All.pipe_right bs
                   (FStar_List.map
                      (fun uu____52405  ->
                         match uu____52405 with
                         | (x,uu____52414) -> FStar_Util.set_mem x d_bvs))
                  in
               FStar_List.append uu____52367 uu____52380)
           in
        ((n_univs + (FStar_List.length bs)), uu____52346)
  
let (abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | FStar_Pervasives_Native.Some rc ->
          let uu____52476 =
            let uu___1604_52477 = rc  in
            let uu____52478 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1604_52477.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____52478;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1604_52477.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____52476
      | uu____52487 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____52521 =
        let uu____52522 =
          let uu____52525 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____52525  in
        uu____52522.FStar_Syntax_Syntax.n  in
      match uu____52521 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____52571 = aux t2 what  in
          (match uu____52571 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____52643 -> ([], t1, abs_body_lcomp)  in
    let uu____52660 = aux t FStar_Pervasives_Native.None  in
    match uu____52660 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____52708 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____52708 with
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
                    | (FStar_Pervasives_Native.None ,uu____52871) -> def
                    | (uu____52882,[]) -> def
                    | (FStar_Pervasives_Native.Some fvs,uu____52894) ->
                        let universes =
                          FStar_All.pipe_right univ_vars
                            (FStar_List.map
                               (fun _52910  ->
                                  FStar_Syntax_Syntax.U_name _52910))
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
            let uu____52992 = FStar_Syntax_Subst.open_univ_vars_comp uvs c
               in
            (match uu____52992 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____53027 ->
            let t' = arrow binders c  in
            let uu____53039 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____53039 with
             | (uvs1,t'1) ->
                 let uu____53060 =
                   let uu____53061 = FStar_Syntax_Subst.compress t'1  in
                   uu____53061.FStar_Syntax_Syntax.n  in
                 (match uu____53060 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____53110 -> failwith "Impossible"))
  
let (is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____53135 -> false
  
let (is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Parser_Const.is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____53146 -> false
  
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
      let uu____53209 =
        let uu____53210 = pre_typ t  in uu____53210.FStar_Syntax_Syntax.n  in
      match uu____53209 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____53215 -> false
  
let rec (is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool) =
  fun t  ->
    fun lid  ->
      let uu____53229 =
        let uu____53230 = pre_typ t  in uu____53230.FStar_Syntax_Syntax.n  in
      match uu____53229 with
      | FStar_Syntax_Syntax.Tm_fvar uu____53234 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____53236) ->
          is_constructed_typ t1 lid
      | FStar_Syntax_Syntax.Tm_uinst (t1,uu____53262) ->
          is_constructed_typ t1 lid
      | uu____53267 -> false
  
let rec (get_tycon :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____53280 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_name uu____53281 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____53282 ->
        FStar_Pervasives_Native.Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____53284) -> get_tycon t2
    | uu____53309 -> FStar_Pervasives_Native.None
  
let (is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____53317 =
      let uu____53318 = un_uinst t  in uu____53318.FStar_Syntax_Syntax.n  in
    match uu____53317 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.by_tactic_lid
    | uu____53323 -> false
  
let (is_builtin_tactic : FStar_Ident.lident -> Prims.bool) =
  fun md  ->
    let path = FStar_Ident.path_of_lid md  in
    if (FStar_List.length path) > (Prims.parse_int "2")
    then
      let uu____53337 =
        let uu____53341 = FStar_List.splitAt (Prims.parse_int "2") path  in
        FStar_Pervasives_Native.fst uu____53341  in
      match uu____53337 with
      | "FStar"::"Tactics"::[] -> true
      | "FStar"::"Reflection"::[] -> true
      | uu____53373 -> false
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
  fun uu____53392  ->
    let u =
      let uu____53398 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _53415  -> FStar_Syntax_Syntax.U_unif _53415)
        uu____53398
       in
    let uu____53416 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
        FStar_Pervasives_Native.None FStar_Range.dummyRange
       in
    (uu____53416, u)
  
let (attr_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun a  ->
    fun a'  ->
      let uu____53429 = eq_tm a a'  in
      match uu____53429 with | Equal  -> true | uu____53432 -> false
  
let (attr_substitute : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  let uu____53437 =
    let uu____53444 =
      let uu____53445 =
        let uu____53446 =
          FStar_Ident.lid_of_path ["FStar"; "Pervasives"; "Substitute"]
            FStar_Range.dummyRange
           in
        FStar_Syntax_Syntax.lid_as_fv uu____53446
          FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
         in
      FStar_Syntax_Syntax.Tm_fvar uu____53445  in
    FStar_Syntax_Syntax.mk uu____53444  in
  uu____53437 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
          let uu____53561 =
            let uu____53564 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____53565 =
              let uu____53572 =
                let uu____53573 =
                  let uu____53590 =
                    let uu____53601 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____53610 =
                      let uu____53621 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____53621]  in
                    uu____53601 :: uu____53610  in
                  (tand, uu____53590)  in
                FStar_Syntax_Syntax.Tm_app uu____53573  in
              FStar_Syntax_Syntax.mk uu____53572  in
            uu____53565 FStar_Pervasives_Native.None uu____53564  in
          FStar_Pervasives_Native.Some uu____53561
  
let (mk_binop :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun op_t  ->
    fun phi1  ->
      fun phi2  ->
        let uu____53701 =
          FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
            phi2.FStar_Syntax_Syntax.pos
           in
        let uu____53702 =
          let uu____53709 =
            let uu____53710 =
              let uu____53727 =
                let uu____53738 = FStar_Syntax_Syntax.as_arg phi1  in
                let uu____53747 =
                  let uu____53758 = FStar_Syntax_Syntax.as_arg phi2  in
                  [uu____53758]  in
                uu____53738 :: uu____53747  in
              (op_t, uu____53727)  in
            FStar_Syntax_Syntax.Tm_app uu____53710  in
          FStar_Syntax_Syntax.mk uu____53709  in
        uu____53702 FStar_Pervasives_Native.None uu____53701
  
let (mk_neg :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun phi  ->
    let uu____53818 =
      let uu____53825 =
        let uu____53826 =
          let uu____53843 =
            let uu____53854 = FStar_Syntax_Syntax.as_arg phi  in
            [uu____53854]  in
          (t_not, uu____53843)  in
        FStar_Syntax_Syntax.Tm_app uu____53826  in
      FStar_Syntax_Syntax.mk uu____53825  in
    uu____53818 FStar_Pervasives_Native.None phi.FStar_Syntax_Syntax.pos
  
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
    let uu____54054 =
      let uu____54061 =
        let uu____54062 =
          let uu____54079 =
            let uu____54090 = FStar_Syntax_Syntax.as_arg e  in [uu____54090]
             in
          (b2t_v, uu____54079)  in
        FStar_Syntax_Syntax.Tm_app uu____54062  in
      FStar_Syntax_Syntax.mk uu____54061  in
    uu____54054 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos
  
let (is_t_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____54137 =
      let uu____54138 = unmeta t  in uu____54138.FStar_Syntax_Syntax.n  in
    match uu____54137 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
    | uu____54143 -> false
  
let (mk_conj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54166 = is_t_true t1  in
      if uu____54166
      then t2
      else
        (let uu____54173 = is_t_true t2  in
         if uu____54173 then t1 else mk_conj t1 t2)
  
let (mk_disj_simp :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      let uu____54201 = is_t_true t1  in
      if uu____54201
      then t_true
      else
        (let uu____54208 = is_t_true t2  in
         if uu____54208 then t_true else mk_disj t1 t2)
  
let (teq : FStar_Syntax_Syntax.term) = fvar_const FStar_Parser_Const.eq2_lid 
let (mk_untyped_eq2 :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun e1  ->
    fun e2  ->
      let uu____54237 =
        FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
          e2.FStar_Syntax_Syntax.pos
         in
      let uu____54238 =
        let uu____54245 =
          let uu____54246 =
            let uu____54263 =
              let uu____54274 = FStar_Syntax_Syntax.as_arg e1  in
              let uu____54283 =
                let uu____54294 = FStar_Syntax_Syntax.as_arg e2  in
                [uu____54294]  in
              uu____54274 :: uu____54283  in
            (teq, uu____54263)  in
          FStar_Syntax_Syntax.Tm_app uu____54246  in
        FStar_Syntax_Syntax.mk uu____54245  in
      uu____54238 FStar_Pervasives_Native.None uu____54237
  
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
          let uu____54364 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____54365 =
            let uu____54372 =
              let uu____54373 =
                let uu____54390 =
                  let uu____54401 = FStar_Syntax_Syntax.iarg t  in
                  let uu____54410 =
                    let uu____54421 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____54430 =
                      let uu____54441 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____54441]  in
                    uu____54421 :: uu____54430  in
                  uu____54401 :: uu____54410  in
                (eq_inst, uu____54390)  in
              FStar_Syntax_Syntax.Tm_app uu____54373  in
            FStar_Syntax_Syntax.mk uu____54372  in
          uu____54365 FStar_Pervasives_Native.None uu____54364
  
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
        let uu____54521 =
          let uu____54528 =
            let uu____54529 =
              let uu____54546 =
                let uu____54557 = FStar_Syntax_Syntax.iarg t  in
                let uu____54566 =
                  let uu____54577 = FStar_Syntax_Syntax.as_arg x  in
                  let uu____54586 =
                    let uu____54597 = FStar_Syntax_Syntax.as_arg t'  in
                    [uu____54597]  in
                  uu____54577 :: uu____54586  in
                uu____54557 :: uu____54566  in
              (t_has_type1, uu____54546)  in
            FStar_Syntax_Syntax.Tm_app uu____54529  in
          FStar_Syntax_Syntax.mk uu____54528  in
        uu____54521 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
        let uu____54677 =
          let uu____54684 =
            let uu____54685 =
              let uu____54702 =
                let uu____54713 = FStar_Syntax_Syntax.iarg t  in
                let uu____54722 =
                  let uu____54733 = FStar_Syntax_Syntax.as_arg e  in
                  [uu____54733]  in
                uu____54713 :: uu____54722  in
              (t_with_type1, uu____54702)  in
            FStar_Syntax_Syntax.Tm_app uu____54685  in
          FStar_Syntax_Syntax.mk uu____54684  in
        uu____54677 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (lex_t : FStar_Syntax_Syntax.term) =
  fvar_const FStar_Parser_Const.lex_t_lid 
let (lex_top : FStar_Syntax_Syntax.term) =
  let uu____54783 =
    let uu____54790 =
      let uu____54791 =
        let uu____54798 =
          FStar_Syntax_Syntax.fvar FStar_Parser_Const.lextop_lid
            FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        (uu____54798, [FStar_Syntax_Syntax.U_zero])  in
      FStar_Syntax_Syntax.Tm_uinst uu____54791  in
    FStar_Syntax_Syntax.mk uu____54790  in
  uu____54783 FStar_Pervasives_Native.None FStar_Range.dummyRange 
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
    let uu____54816 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____54829 ->
          (FStar_Parser_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____54840 ->
          (FStar_Parser_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____54816 with
    | (eff_name,flags) ->
        FStar_Syntax_Syntax.mk_lcomp eff_name (comp_result c0) flags
          (fun uu____54861  -> c0)
  
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
        let uu____54944 =
          let uu____54951 =
            let uu____54952 =
              let uu____54969 =
                let uu____54980 =
                  FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
                let uu____54989 =
                  let uu____55000 =
                    let uu____55009 =
                      let uu____55010 =
                        let uu____55011 = FStar_Syntax_Syntax.mk_binder x  in
                        [uu____55011]  in
                      abs uu____55010 body
                        (FStar_Pervasives_Native.Some (residual_tot ktype0))
                       in
                    FStar_Syntax_Syntax.as_arg uu____55009  in
                  [uu____55000]  in
                uu____54980 :: uu____54989  in
              (fa, uu____54969)  in
            FStar_Syntax_Syntax.Tm_app uu____54952  in
          FStar_Syntax_Syntax.mk uu____54951  in
        uu____54944 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
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
             let uu____55141 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____55141
             then f1
             else mk_forall_no_univ (FStar_Pervasives_Native.fst b) f1) bs f
  
let rec (is_wild_pat :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t -> Prims.bool) =
  fun p  ->
    match p.FStar_Syntax_Syntax.v with
    | FStar_Syntax_Syntax.Pat_wild uu____55160 -> true
    | uu____55162 -> false
  
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
          let uu____55209 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
              t1.FStar_Syntax_Syntax.pos
             in
          (uu____55209, FStar_Pervasives_Native.None, t1)  in
        let else_branch =
          let uu____55238 =
            FStar_Syntax_Syntax.withinfo
              (FStar_Syntax_Syntax.Pat_constant
                 (FStar_Const.Const_bool false)) t2.FStar_Syntax_Syntax.pos
             in
          (uu____55238, FStar_Pervasives_Native.None, t2)  in
        let uu____55252 =
          let uu____55253 =
            FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
              t2.FStar_Syntax_Syntax.pos
             in
          FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____55253  in
        FStar_Syntax_Syntax.mk
          (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch]))
          FStar_Pervasives_Native.None uu____55252
  
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
      let uu____55329 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55332 =
        let uu____55343 = FStar_Syntax_Syntax.as_arg p  in [uu____55343]  in
      mk_app uu____55329 uu____55332
  
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
      let uu____55383 = FStar_Syntax_Syntax.mk_Tm_uinst sq [u]  in
      let uu____55386 =
        let uu____55397 = FStar_Syntax_Syntax.as_arg p  in [uu____55397]  in
      mk_app uu____55383 uu____55386
  
let (un_squash :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55432 = head_and_args t  in
    match uu____55432 with
    | (head1,args) ->
        let head2 = unascribe head1  in
        let head3 = un_uinst head2  in
        let uu____55481 =
          let uu____55496 =
            let uu____55497 = FStar_Syntax_Subst.compress head3  in
            uu____55497.FStar_Syntax_Syntax.n  in
          (uu____55496, args)  in
        (match uu____55481 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____55516)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.unit_lid
                  ->
                  let uu____55582 =
                    let uu____55587 =
                      let uu____55588 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____55588]  in
                    FStar_Syntax_Subst.open_term uu____55587 p  in
                  (match uu____55582 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____55645 -> failwith "impossible"  in
                       let uu____55653 =
                         let uu____55655 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (FStar_Pervasives_Native.fst b1)
                           uu____55655
                          in
                       if uu____55653
                       then FStar_Pervasives_Native.None
                       else FStar_Pervasives_Native.Some p1)
              | uu____55671 -> FStar_Pervasives_Native.None)
         | uu____55674 -> FStar_Pervasives_Native.None)
  
let (is_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55705 = head_and_args t  in
    match uu____55705 with
    | (head1,args) ->
        let uu____55756 =
          let uu____55771 =
            let uu____55772 = FStar_Syntax_Subst.compress head1  in
            uu____55772.FStar_Syntax_Syntax.n  in
          (uu____55771, args)  in
        (match uu____55756 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____55794;
               FStar_Syntax_Syntax.vars = uu____55795;_},u::[]),(t1,uu____55798)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____55845 -> FStar_Pervasives_Native.None)
  
let (is_auto_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.term'
      FStar_Syntax_Syntax.syntax) FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____55880 = head_and_args t  in
    match uu____55880 with
    | (head1,args) ->
        let uu____55931 =
          let uu____55946 =
            let uu____55947 = FStar_Syntax_Subst.compress head1  in
            uu____55947.FStar_Syntax_Syntax.n  in
          (uu____55946, args)  in
        (match uu____55931 with
         | (FStar_Syntax_Syntax.Tm_uinst
            ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
               FStar_Syntax_Syntax.pos = uu____55969;
               FStar_Syntax_Syntax.vars = uu____55970;_},u::[]),(t1,uu____55973)::[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv
               FStar_Parser_Const.auto_squash_lid
             -> FStar_Pervasives_Native.Some (u, t1)
         | uu____56020 -> FStar_Pervasives_Native.None)
  
let (is_sub_singleton : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____56048 =
      let uu____56065 = unmeta t  in head_and_args uu____56065  in
    match uu____56048 with
    | (head1,uu____56068) ->
        let uu____56093 =
          let uu____56094 = un_uinst head1  in
          uu____56094.FStar_Syntax_Syntax.n  in
        (match uu____56093 with
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
         | uu____56099 -> false)
  
let (arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.option)
  =
  fun t  ->
    let uu____56119 =
      let uu____56132 =
        let uu____56133 = FStar_Syntax_Subst.compress t  in
        uu____56133.FStar_Syntax_Syntax.n  in
      match uu____56132 with
      | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
          failwith "fatal: empty binders on arrow?"
      | FStar_Syntax_Syntax.Tm_arrow (b::[],c) ->
          FStar_Pervasives_Native.Some (b, c)
      | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
          let uu____56263 =
            let uu____56274 =
              let uu____56275 = arrow bs c  in
              FStar_Syntax_Syntax.mk_Total uu____56275  in
            (b, uu____56274)  in
          FStar_Pervasives_Native.Some uu____56263
      | uu____56292 -> FStar_Pervasives_Native.None  in
    FStar_Util.bind_opt uu____56119
      (fun uu____56330  ->
         match uu____56330 with
         | (b,c) ->
             let uu____56367 = FStar_Syntax_Subst.open_comp [b] c  in
             (match uu____56367 with
              | (bs,c1) ->
                  let b1 =
                    match bs with
                    | b1::[] -> b1
                    | uu____56430 ->
                        failwith
                          "impossible: open_comp returned different amount of binders"
                     in
                  FStar_Pervasives_Native.Some (b1, c1)))
  
let (is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv  ->
    fun t  ->
      let uu____56467 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____56467
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____56519 -> false
  
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____56563 -> false
  
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____56605 -> false
  
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
          (t,FStar_Syntax_Syntax.Meta_monadic uu____56645) ->
          unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____56657) ->
          unmeta_monadic t
      | uu____56670 -> f2  in
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
      let aux f2 uu____56766 =
        match uu____56766 with
        | (lid,arity) ->
            let uu____56775 =
              let uu____56792 = unmeta_monadic f2  in
              head_and_args uu____56792  in
            (match uu____56775 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____56822 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____56822
                 then FStar_Pervasives_Native.Some (BaseConn (lid, args))
                 else FStar_Pervasives_Native.None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____56902 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____56902)
      | uu____56915 -> ([], t1)  in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____56982 = head_and_args t1  in
        match uu____56982 with
        | (t2,args) ->
            let uu____57037 = un_uinst t2  in
            let uu____57038 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____57079  ->
                      match uu____57079 with
                      | (t3,imp) ->
                          let uu____57098 = unascribe t3  in
                          (uu____57098, imp)))
               in
            (uu____57037, uu____57038)
         in
      let rec aux qopt out t1 =
        let uu____57149 = let uu____57173 = flat t1  in (qopt, uu____57173)
           in
        match uu____57149 with
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57213;
                 FStar_Syntax_Syntax.vars = uu____57214;_},({
                                                              FStar_Syntax_Syntax.n
                                                                =
                                                                FStar_Syntax_Syntax.Tm_abs
                                                                (b::[],t2,uu____57217);
                                                              FStar_Syntax_Syntax.pos
                                                                = uu____57218;
                                                              FStar_Syntax_Syntax.vars
                                                                = uu____57219;_},uu____57220)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.pos = uu____57322;
                 FStar_Syntax_Syntax.vars = uu____57323;_},uu____57324::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____57327);
                  FStar_Syntax_Syntax.pos = uu____57328;
                  FStar_Syntax_Syntax.vars = uu____57329;_},uu____57330)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57447;
               FStar_Syntax_Syntax.vars = uu____57448;_},({
                                                            FStar_Syntax_Syntax.n
                                                              =
                                                              FStar_Syntax_Syntax.Tm_abs
                                                              (b::[],t2,uu____57451);
                                                            FStar_Syntax_Syntax.pos
                                                              = uu____57452;
                                                            FStar_Syntax_Syntax.vars
                                                              = uu____57453;_},uu____57454)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57547 =
              let uu____57551 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57551  in
            aux uu____57547 (b :: out) t2
        | (FStar_Pervasives_Native.None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.pos = uu____57561;
               FStar_Syntax_Syntax.vars = uu____57562;_},uu____57563::
             ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                  (b::[],t2,uu____57566);
                FStar_Syntax_Syntax.pos = uu____57567;
                FStar_Syntax_Syntax.vars = uu____57568;_},uu____57569)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            let uu____57678 =
              let uu____57682 =
                is_forall
                  (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              FStar_Pervasives_Native.Some uu____57682  in
            aux uu____57678 (b :: out) t2
        | (FStar_Pervasives_Native.Some b,uu____57692) ->
            let bs = FStar_List.rev out  in
            let uu____57745 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____57745 with
             | (bs1,t2) ->
                 let uu____57754 = patterns t2  in
                 (match uu____57754 with
                  | (pats,body) ->
                      if b
                      then
                        FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                      else
                        FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
        | uu____57804 -> FStar_Pervasives_Native.None  in
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
      let uu____57896 = un_squash t  in
      FStar_Util.bind_opt uu____57896
        (fun t1  ->
           let uu____57912 = head_and_args' t1  in
           match uu____57912 with
           | (hd1,args) ->
               let uu____57951 =
                 let uu____57957 =
                   let uu____57958 = un_uinst hd1  in
                   uu____57958.FStar_Syntax_Syntax.n  in
                 (uu____57957, (FStar_List.length args))  in
               (match uu____57951 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57974) when
                    (_57974 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_and_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57977) when
                    (_57977 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_or_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57980) when
                    (_57980 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57983) when
                    (_57983 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq2_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57986) when
                    (_57986 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57989) when
                    (_57989 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_eq3_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.c_eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57992) when
                    (_57992 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_true_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_57995) when
                    (_57995 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.c_false_lid)
                    ->
                    FStar_Pervasives_Native.Some
                      (BaseConn (FStar_Parser_Const.false_lid, args))
                | uu____57996 -> FStar_Pervasives_Native.None))
       in
    let rec destruct_sq_forall t =
      let uu____58026 = un_squash t  in
      FStar_Util.bind_opt uu____58026
        (fun t1  ->
           let uu____58041 = arrow_one t1  in
           match uu____58041 with
           | FStar_Pervasives_Native.Some (b,c) ->
               let uu____58056 =
                 let uu____58058 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____58058  in
               if uu____58056
               then FStar_Pervasives_Native.None
               else
                 (let q =
                    let uu____58068 = comp_to_comp_typ_nouniv c  in
                    uu____58068.FStar_Syntax_Syntax.result_typ  in
                  let uu____58069 =
                    is_free_in (FStar_Pervasives_Native.fst b) q  in
                  if uu____58069
                  then
                    let uu____58076 = patterns q  in
                    match uu____58076 with
                    | (pats,q1) ->
                        FStar_All.pipe_left maybe_collect
                          (FStar_Pervasives_Native.Some
                             (QAll ([b], pats, q1)))
                  else
                    (let uu____58139 =
                       let uu____58140 =
                         let uu____58145 =
                           let uu____58146 =
                             FStar_Syntax_Syntax.as_arg
                               (FStar_Pervasives_Native.fst b).FStar_Syntax_Syntax.sort
                              in
                           let uu____58157 =
                             let uu____58168 = FStar_Syntax_Syntax.as_arg q
                                in
                             [uu____58168]  in
                           uu____58146 :: uu____58157  in
                         (FStar_Parser_Const.imp_lid, uu____58145)  in
                       BaseConn uu____58140  in
                     FStar_Pervasives_Native.Some uu____58139))
           | uu____58201 -> FStar_Pervasives_Native.None)
    
    and destruct_sq_exists t =
      let uu____58209 = un_squash t  in
      FStar_Util.bind_opt uu____58209
        (fun t1  ->
           let uu____58240 = head_and_args' t1  in
           match uu____58240 with
           | (hd1,args) ->
               let uu____58279 =
                 let uu____58294 =
                   let uu____58295 = un_uinst hd1  in
                   uu____58295.FStar_Syntax_Syntax.n  in
                 (uu____58294, args)  in
               (match uu____58279 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____58312)::(a2,uu____58314)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.dtuple2_lid
                    ->
                    let uu____58365 =
                      let uu____58366 = FStar_Syntax_Subst.compress a2  in
                      uu____58366.FStar_Syntax_Syntax.n  in
                    (match uu____58365 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____58373) ->
                         let uu____58408 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____58408 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____58461 -> failwith "impossible"  in
                              let uu____58469 = patterns q1  in
                              (match uu____58469 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (FStar_Pervasives_Native.Some
                                        (QEx ([b1], pats, q2)))))
                     | uu____58530 -> FStar_Pervasives_Native.None)
                | uu____58531 -> FStar_Pervasives_Native.None))
    
    and maybe_collect f1 =
      match f1 with
      | FStar_Pervasives_Native.Some (QAll (bs,pats,phi)) ->
          let uu____58554 = destruct_sq_forall phi  in
          (match uu____58554 with
           | FStar_Pervasives_Native.Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58564  -> FStar_Pervasives_Native.Some _58564)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58571 -> f1)
      | FStar_Pervasives_Native.Some (QEx (bs,pats,phi)) ->
          let uu____58577 = destruct_sq_exists phi  in
          (match uu____58577 with
           | FStar_Pervasives_Native.Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left
                 (fun _58587  -> FStar_Pervasives_Native.Some _58587)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____58594 -> f1)
      | uu____58597 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____58601 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____58601
      (fun uu____58606  ->
         let uu____58607 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____58607
           (fun uu____58612  ->
              let uu____58613 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____58613
                (fun uu____58618  ->
                   let uu____58619 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____58619
                     (fun uu____58624  ->
                        let uu____58625 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____58625
                          (fun uu____58629  -> FStar_Pervasives_Native.None)))))
  
let (unthunk_lemma_post :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let uu____58642 =
      let uu____58643 = FStar_Syntax_Subst.compress t  in
      uu____58643.FStar_Syntax_Syntax.n  in
    match uu____58642 with
    | FStar_Syntax_Syntax.Tm_abs (b::[],e,uu____58650) ->
        let uu____58685 = FStar_Syntax_Subst.open_term [b] e  in
        (match uu____58685 with
         | (bs,e1) ->
             let b1 = FStar_List.hd bs  in
             let uu____58719 = is_free_in (FStar_Pervasives_Native.fst b1) e1
                in
             if uu____58719
             then
               let uu____58726 =
                 let uu____58737 = FStar_Syntax_Syntax.as_arg exp_unit  in
                 [uu____58737]  in
               mk_app t uu____58726
             else e1)
    | uu____58764 ->
        let uu____58765 =
          let uu____58776 = FStar_Syntax_Syntax.as_arg exp_unit  in
          [uu____58776]  in
        mk_app t uu____58765
  
let (action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action ->
      FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun eff_lid  ->
    fun a  ->
      fun pos  ->
        let lb =
          let uu____58818 =
            let uu____58823 =
              FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
                FStar_Syntax_Syntax.delta_equational
                FStar_Pervasives_Native.None
               in
            FStar_Util.Inr uu____58823  in
          let uu____58824 =
            let uu____58825 =
              FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ
               in
            arrow a.FStar_Syntax_Syntax.action_params uu____58825  in
          let uu____58828 =
            abs a.FStar_Syntax_Syntax.action_params
              a.FStar_Syntax_Syntax.action_defn FStar_Pervasives_Native.None
             in
          close_univs_and_mk_letbinding FStar_Pervasives_Native.None
            uu____58818 a.FStar_Syntax_Syntax.action_univs uu____58824
            FStar_Parser_Const.effect_Tot_lid uu____58828 [] pos
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
    let uu____58854 =
      let uu____58861 =
        let uu____58862 =
          let uu____58879 =
            let uu____58890 = FStar_Syntax_Syntax.as_arg t  in [uu____58890]
             in
          (reify_1, uu____58879)  in
        FStar_Syntax_Syntax.Tm_app uu____58862  in
      FStar_Syntax_Syntax.mk uu____58861  in
    uu____58854 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let (mk_reflect :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t  ->
    let reflect_ =
      let uu____58945 =
        let uu____58952 =
          let uu____58953 =
            let uu____58954 = FStar_Ident.lid_of_str "Bogus.Effect"  in
            FStar_Const.Const_reflect uu____58954  in
          FStar_Syntax_Syntax.Tm_constant uu____58953  in
        FStar_Syntax_Syntax.mk uu____58952  in
      uu____58945 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos  in
    let uu____58959 =
      let uu____58966 =
        let uu____58967 =
          let uu____58984 =
            let uu____58995 = FStar_Syntax_Syntax.as_arg t  in [uu____58995]
             in
          (reflect_, uu____58984)  in
        FStar_Syntax_Syntax.Tm_app uu____58967  in
      FStar_Syntax_Syntax.mk uu____58966  in
    uu____58959 FStar_Pervasives_Native.None t.FStar_Syntax_Syntax.pos
  
let rec (delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth) =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____59042 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_lazy i ->
        let uu____59067 = unfold_lazy i  in delta_qualifier uu____59067
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____59069 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____59070 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____59071 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____59094 ->
        FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____59107 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_quoted uu____59108 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____59115 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____59116 ->
        FStar_Syntax_Syntax.delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____59132) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____59137;
           FStar_Syntax_Syntax.index = uu____59138;
           FStar_Syntax_Syntax.sort = t2;_},uu____59140)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____59149) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____59155,uu____59156) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____59198) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____59223,t2,uu____59225) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____59250,t2) -> delta_qualifier t2
  
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
    let uu____59289 = delta_qualifier t  in incr_delta_depth uu____59289
  
let (is_unknown : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let uu____59297 =
      let uu____59298 = FStar_Syntax_Subst.compress t  in
      uu____59298.FStar_Syntax_Syntax.n  in
    match uu____59297 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____59303 -> false
  
let rec (list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list FStar_Pervasives_Native.option)
  =
  fun e  ->
    let uu____59319 =
      let uu____59336 = unmeta e  in head_and_args uu____59336  in
    match uu____59319 with
    | (head1,args) ->
        let uu____59367 =
          let uu____59382 =
            let uu____59383 = un_uinst head1  in
            uu____59383.FStar_Syntax_Syntax.n  in
          (uu____59382, args)  in
        (match uu____59367 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____59401) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
             FStar_Pervasives_Native.Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____59425::(hd1,uu____59427)::(tl1,uu____59429)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid ->
             let uu____59496 =
               let uu____59499 =
                 let uu____59502 = list_elements tl1  in
                 FStar_Util.must uu____59502  in
               hd1 :: uu____59499  in
             FStar_Pervasives_Native.Some uu____59496
         | uu____59511 -> FStar_Pervasives_Native.None)
  
let rec apply_last :
  'Auu____59535 .
    ('Auu____59535 -> 'Auu____59535) ->
      'Auu____59535 Prims.list -> 'Auu____59535 Prims.list
  =
  fun f  ->
    fun l  ->
      match l with
      | [] -> failwith "apply_last: got empty list"
      | a::[] -> let uu____59561 = f a  in [uu____59561]
      | x::xs -> let uu____59566 = apply_last f xs  in x :: uu____59566
  
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
          let uu____59621 =
            let uu____59628 =
              let uu____59629 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.delta_constant
                  (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____59629  in
            FStar_Syntax_Syntax.mk uu____59628  in
          uu____59621 FStar_Pervasives_Native.None rng  in
        let cons1 args pos =
          let uu____59646 =
            let uu____59651 =
              let uu____59652 = ctor FStar_Parser_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59652
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59651 args  in
          uu____59646 FStar_Pervasives_Native.None pos  in
        let nil args pos =
          let uu____59668 =
            let uu____59673 =
              let uu____59674 = ctor FStar_Parser_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____59674
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____59673 args  in
          uu____59668 FStar_Pervasives_Native.None pos  in
        let uu____59677 =
          let uu____59678 =
            let uu____59679 = FStar_Syntax_Syntax.iarg typ  in [uu____59679]
             in
          nil uu____59678 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____59713 =
                 let uu____59714 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____59723 =
                   let uu____59734 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____59743 =
                     let uu____59754 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____59754]  in
                   uu____59734 :: uu____59743  in
                 uu____59714 :: uu____59723  in
               cons1 uu____59713 t.FStar_Syntax_Syntax.pos) l uu____59677
  
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
        | uu____59863 -> false
  
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
          | uu____59977 -> false
  
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
        | uu____60143 -> false
  
let (debug_term_eq : Prims.bool FStar_ST.ref) = FStar_Util.mk_ref false 
let (check : Prims.string -> Prims.bool -> Prims.bool) =
  fun msg  ->
    fun cond  ->
      if cond
      then true
      else
        ((let uu____60192 = FStar_ST.op_Bang debug_term_eq  in
          if uu____60192
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
        let t11 = let uu____60414 = unmeta_safe t1  in canon_app uu____60414
           in
        let t21 = let uu____60420 = unmeta_safe t2  in canon_app uu____60420
           in
        let uu____60423 =
          let uu____60428 =
            let uu____60429 =
              let uu____60432 = un_uinst t11  in
              FStar_Syntax_Subst.compress uu____60432  in
            uu____60429.FStar_Syntax_Syntax.n  in
          let uu____60433 =
            let uu____60434 =
              let uu____60437 = un_uinst t21  in
              FStar_Syntax_Subst.compress uu____60437  in
            uu____60434.FStar_Syntax_Syntax.n  in
          (uu____60428, uu____60433)  in
        match uu____60423 with
        | (FStar_Syntax_Syntax.Tm_uinst uu____60439,uu____60440) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60449,FStar_Syntax_Syntax.Tm_uinst uu____60450) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_delayed uu____60459,uu____60460) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60485,FStar_Syntax_Syntax.Tm_delayed uu____60486) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_ascribed uu____60511,uu____60512) ->
            failwith "term_eq: impossible, should have been removed"
        | (uu____60541,FStar_Syntax_Syntax.Tm_ascribed uu____60542) ->
            failwith "term_eq: impossible, should have been removed"
        | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
            check "bvar"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
            check "name"
              (x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index)
        | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
            let uu____60581 = FStar_Syntax_Syntax.fv_eq x y  in
            check "fvar" uu____60581
        | (FStar_Syntax_Syntax.Tm_constant c1,FStar_Syntax_Syntax.Tm_constant
           c2) ->
            let uu____60586 = FStar_Const.eq_const c1 c2  in
            check "const" uu____60586
        | (FStar_Syntax_Syntax.Tm_type
           uu____60589,FStar_Syntax_Syntax.Tm_type uu____60590) -> true
        | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
           (b2,t22,k2)) ->
            (let uu____60648 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "abs binders" uu____60648) &&
              (let uu____60658 = term_eq_dbg dbg t12 t22  in
               check "abs bodies" uu____60658)
        | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
           (b2,c2)) ->
            (let uu____60707 = eqlist (binder_eq_dbg dbg) b1 b2  in
             check "arrow binders" uu____60707) &&
              (let uu____60717 = comp_eq_dbg dbg c1 c2  in
               check "arrow comp" uu____60717)
        | (FStar_Syntax_Syntax.Tm_refine
           (b1,t12),FStar_Syntax_Syntax.Tm_refine (b2,t22)) ->
            (check "refine bv"
               (b1.FStar_Syntax_Syntax.index = b2.FStar_Syntax_Syntax.index))
              &&
              (let uu____60735 = term_eq_dbg dbg t12 t22  in
               check "refine formula" uu____60735)
        | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
           (f2,a2)) ->
            (let uu____60792 = term_eq_dbg dbg f1 f2  in
             check "app head" uu____60792) &&
              (let uu____60796 = eqlist (arg_eq_dbg dbg) a1 a2  in
               check "app args" uu____60796)
        | (FStar_Syntax_Syntax.Tm_match
           (t12,bs1),FStar_Syntax_Syntax.Tm_match (t22,bs2)) ->
            (let uu____60885 = term_eq_dbg dbg t12 t22  in
             check "match head" uu____60885) &&
              (let uu____60889 = eqlist (branch_eq_dbg dbg) bs1 bs2  in
               check "match branches" uu____60889)
        | (FStar_Syntax_Syntax.Tm_lazy uu____60906,uu____60907) ->
            let uu____60908 =
              let uu____60910 = unlazy t11  in
              term_eq_dbg dbg uu____60910 t21  in
            check "lazy_l" uu____60908
        | (uu____60912,FStar_Syntax_Syntax.Tm_lazy uu____60913) ->
            let uu____60914 =
              let uu____60916 = unlazy t21  in
              term_eq_dbg dbg t11 uu____60916  in
            check "lazy_r" uu____60914
        | (FStar_Syntax_Syntax.Tm_let
           ((b1,lbs1),t12),FStar_Syntax_Syntax.Tm_let ((b2,lbs2),t22)) ->
            ((check "let flag" (b1 = b2)) &&
               (let uu____60961 = eqlist (letbinding_eq_dbg dbg) lbs1 lbs2
                   in
                check "let lbs" uu____60961))
              &&
              (let uu____60965 = term_eq_dbg dbg t12 t22  in
               check "let body" uu____60965)
        | (FStar_Syntax_Syntax.Tm_uvar
           (u1,uu____60969),FStar_Syntax_Syntax.Tm_uvar (u2,uu____60971)) ->
            check "uvar"
              (u1.FStar_Syntax_Syntax.ctx_uvar_head =
                 u2.FStar_Syntax_Syntax.ctx_uvar_head)
        | (FStar_Syntax_Syntax.Tm_quoted
           (qt1,qi1),FStar_Syntax_Syntax.Tm_quoted (qt2,qi2)) ->
            (let uu____61029 =
               let uu____61031 = eq_quoteinfo qi1 qi2  in uu____61031 = Equal
                in
             check "tm_quoted qi" uu____61029) &&
              (let uu____61034 = term_eq_dbg dbg qt1 qt2  in
               check "tm_quoted payload" uu____61034)
        | (FStar_Syntax_Syntax.Tm_meta (t12,m1),FStar_Syntax_Syntax.Tm_meta
           (t22,m2)) ->
            (match (m1, m2) with
             | (FStar_Syntax_Syntax.Meta_monadic
                (n1,ty1),FStar_Syntax_Syntax.Meta_monadic (n2,ty2)) ->
                 (let uu____61064 = FStar_Ident.lid_equals n1 n2  in
                  check "meta_monadic lid" uu____61064) &&
                   (let uu____61068 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic type" uu____61068)
             | (FStar_Syntax_Syntax.Meta_monadic_lift
                (s1,t13,ty1),FStar_Syntax_Syntax.Meta_monadic_lift
                (s2,t23,ty2)) ->
                 ((let uu____61087 = FStar_Ident.lid_equals s1 s2  in
                   check "meta_monadic_lift src" uu____61087) &&
                    (let uu____61091 = FStar_Ident.lid_equals t13 t23  in
                     check "meta_monadic_lift tgt" uu____61091))
                   &&
                   (let uu____61095 = term_eq_dbg dbg ty1 ty2  in
                    check "meta_monadic_lift type" uu____61095)
             | uu____61098 -> fail "metas")
        | (FStar_Syntax_Syntax.Tm_unknown ,uu____61104) -> fail "unk"
        | (uu____61106,FStar_Syntax_Syntax.Tm_unknown ) -> fail "unk"
        | (FStar_Syntax_Syntax.Tm_bvar uu____61108,uu____61109) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_name uu____61111,uu____61112) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_fvar uu____61114,uu____61115) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_constant uu____61117,uu____61118) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_type uu____61120,uu____61121) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_abs uu____61123,uu____61124) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_arrow uu____61144,uu____61145) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_refine uu____61161,uu____61162) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_app uu____61170,uu____61171) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_match uu____61189,uu____61190) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_let uu____61214,uu____61215) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_uvar uu____61230,uu____61231) ->
            fail "bottom"
        | (FStar_Syntax_Syntax.Tm_meta uu____61245,uu____61246) ->
            fail "bottom"
        | (uu____61254,FStar_Syntax_Syntax.Tm_bvar uu____61255) ->
            fail "bottom"
        | (uu____61257,FStar_Syntax_Syntax.Tm_name uu____61258) ->
            fail "bottom"
        | (uu____61260,FStar_Syntax_Syntax.Tm_fvar uu____61261) ->
            fail "bottom"
        | (uu____61263,FStar_Syntax_Syntax.Tm_constant uu____61264) ->
            fail "bottom"
        | (uu____61266,FStar_Syntax_Syntax.Tm_type uu____61267) ->
            fail "bottom"
        | (uu____61269,FStar_Syntax_Syntax.Tm_abs uu____61270) ->
            fail "bottom"
        | (uu____61290,FStar_Syntax_Syntax.Tm_arrow uu____61291) ->
            fail "bottom"
        | (uu____61307,FStar_Syntax_Syntax.Tm_refine uu____61308) ->
            fail "bottom"
        | (uu____61316,FStar_Syntax_Syntax.Tm_app uu____61317) ->
            fail "bottom"
        | (uu____61335,FStar_Syntax_Syntax.Tm_match uu____61336) ->
            fail "bottom"
        | (uu____61360,FStar_Syntax_Syntax.Tm_let uu____61361) ->
            fail "bottom"
        | (uu____61376,FStar_Syntax_Syntax.Tm_uvar uu____61377) ->
            fail "bottom"
        | (uu____61391,FStar_Syntax_Syntax.Tm_meta uu____61392) ->
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
               let uu____61427 = term_eq_dbg dbg t1 t2  in
               check "arg tm" uu____61427)
          (fun q1  ->
             fun q2  ->
               let uu____61439 =
                 let uu____61441 = eq_aqual q1 q2  in uu____61441 = Equal  in
               check "arg qual" uu____61439) a1 a2

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
               let uu____61466 =
                 term_eq_dbg dbg b11.FStar_Syntax_Syntax.sort
                   b21.FStar_Syntax_Syntax.sort
                  in
               check "binder sort" uu____61466)
          (fun q1  ->
             fun q2  ->
               let uu____61478 =
                 let uu____61480 = eq_aqual q1 q2  in uu____61480 = Equal  in
               check "binder qual" uu____61478) b1 b2

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
        ((let uu____61500 =
            FStar_Ident.lid_equals c11.FStar_Syntax_Syntax.effect_name
              c21.FStar_Syntax_Syntax.effect_name
             in
          check "comp eff" uu____61500) &&
           (let uu____61504 =
              term_eq_dbg dbg c11.FStar_Syntax_Syntax.result_typ
                c21.FStar_Syntax_Syntax.result_typ
               in
            check "comp result typ" uu____61504))
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
    fun uu____61514  ->
      fun uu____61515  ->
        match (uu____61514, uu____61515) with
        | ((p1,w1,t1),(p2,w2,t2)) ->
            ((let uu____61642 = FStar_Syntax_Syntax.eq_pat p1 p2  in
              check "branch pat" uu____61642) &&
               (let uu____61646 = term_eq_dbg dbg t1 t2  in
                check "branch body" uu____61646))
              &&
              (let uu____61650 =
                 match (w1, w2) with
                 | (FStar_Pervasives_Native.Some
                    x,FStar_Pervasives_Native.Some y) -> term_eq_dbg dbg x y
                 | (FStar_Pervasives_Native.None
                    ,FStar_Pervasives_Native.None ) -> true
                 | uu____61692 -> false  in
               check "branch when" uu____61650)

and (letbinding_eq_dbg :
  Prims.bool ->
    FStar_Syntax_Syntax.letbinding ->
      FStar_Syntax_Syntax.letbinding -> Prims.bool)
  =
  fun dbg  ->
    fun lb1  ->
      fun lb2  ->
        ((let uu____61713 =
            eqsum (fun bv1  -> fun bv2  -> true) FStar_Syntax_Syntax.fv_eq
              lb1.FStar_Syntax_Syntax.lbname lb2.FStar_Syntax_Syntax.lbname
             in
          check "lb bv" uu____61713) &&
           (let uu____61722 =
              term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbtyp
                lb2.FStar_Syntax_Syntax.lbtyp
               in
            check "lb typ" uu____61722))
          &&
          (let uu____61726 =
             term_eq_dbg dbg lb1.FStar_Syntax_Syntax.lbdef
               lb2.FStar_Syntax_Syntax.lbdef
              in
           check "lb def" uu____61726)

let (term_eq :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t1  ->
    fun t2  ->
      let r =
        let uu____61743 = FStar_ST.op_Bang debug_term_eq  in
        term_eq_dbg uu____61743 t1 t2  in
      FStar_ST.op_Colon_Equals debug_term_eq false; r
  
let rec (sizeof : FStar_Syntax_Syntax.term -> Prims.int) =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____61797 ->
        let uu____61820 =
          let uu____61822 = FStar_Syntax_Subst.compress t  in
          sizeof uu____61822  in
        (Prims.parse_int "1") + uu____61820
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____61825 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61825
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____61829 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____61829
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____61838 = sizeof t1  in (FStar_List.length us) + uu____61838
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____61842) ->
        let uu____61867 = sizeof t1  in
        let uu____61869 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____61884  ->
                 match uu____61884 with
                 | (bv,uu____61894) ->
                     let uu____61899 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____61899) (Prims.parse_int "0") bs
           in
        uu____61867 + uu____61869
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____61928 = sizeof hd1  in
        let uu____61930 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____61945  ->
                 match uu____61945 with
                 | (arg,uu____61955) ->
                     let uu____61960 = sizeof arg  in acc + uu____61960)
            (Prims.parse_int "0") args
           in
        uu____61928 + uu____61930
    | uu____61963 -> (Prims.parse_int "1")
  
let (is_fvar : FStar_Ident.lident -> FStar_Syntax_Syntax.term -> Prims.bool)
  =
  fun lid  ->
    fun t  ->
      let uu____61977 =
        let uu____61978 = un_uinst t  in uu____61978.FStar_Syntax_Syntax.n
         in
      match uu____61977 with
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Syntax_Syntax.fv_eq_lid fv lid
      | uu____61983 -> false
  
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
        let uu____62032 = FStar_Options.set_options t s  in
        match uu____62032 with
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
          ((let uu____62049 = FStar_Options.restore_cmd_line_options false
               in
            FStar_All.pipe_right uu____62049 (fun a1  -> ()));
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
          let uu____62064 = FStar_Options.internal_pop ()  in
          if uu____62064
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
    | FStar_Syntax_Syntax.Tm_delayed uu____62096 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_name x -> []
    | FStar_Syntax_Syntax.Tm_uvar uu____62123 -> []
    | FStar_Syntax_Syntax.Tm_type u -> []
    | FStar_Syntax_Syntax.Tm_bvar x -> [x]
    | FStar_Syntax_Syntax.Tm_fvar uu____62138 -> []
    | FStar_Syntax_Syntax.Tm_constant uu____62139 -> []
    | FStar_Syntax_Syntax.Tm_lazy uu____62140 -> []
    | FStar_Syntax_Syntax.Tm_unknown  -> []
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) -> unbound_variables t1
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____62149) ->
        let uu____62174 = FStar_Syntax_Subst.open_term bs t1  in
        (match uu____62174 with
         | (bs1,t2) ->
             let uu____62183 =
               FStar_List.collect
                 (fun uu____62195  ->
                    match uu____62195 with
                    | (b,uu____62205) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62210 = unbound_variables t2  in
             FStar_List.append uu____62183 uu____62210)
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____62235 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____62235 with
         | (bs1,c1) ->
             let uu____62244 =
               FStar_List.collect
                 (fun uu____62256  ->
                    match uu____62256 with
                    | (b,uu____62266) ->
                        unbound_variables b.FStar_Syntax_Syntax.sort) bs1
                in
             let uu____62271 = unbound_variables_comp c1  in
             FStar_List.append uu____62244 uu____62271)
    | FStar_Syntax_Syntax.Tm_refine (b,t1) ->
        let uu____62280 =
          FStar_Syntax_Subst.open_term [(b, FStar_Pervasives_Native.None)] t1
           in
        (match uu____62280 with
         | (bs,t2) ->
             let uu____62303 =
               FStar_List.collect
                 (fun uu____62315  ->
                    match uu____62315 with
                    | (b1,uu____62325) ->
                        unbound_variables b1.FStar_Syntax_Syntax.sort) bs
                in
             let uu____62330 = unbound_variables t2  in
             FStar_List.append uu____62303 uu____62330)
    | FStar_Syntax_Syntax.Tm_app (t1,args) ->
        let uu____62359 =
          FStar_List.collect
            (fun uu____62373  ->
               match uu____62373 with
               | (x,uu____62385) -> unbound_variables x) args
           in
        let uu____62394 = unbound_variables t1  in
        FStar_List.append uu____62359 uu____62394
    | FStar_Syntax_Syntax.Tm_match (t1,pats) ->
        let uu____62435 = unbound_variables t1  in
        let uu____62438 =
          FStar_All.pipe_right pats
            (FStar_List.collect
               (fun br  ->
                  let uu____62453 = FStar_Syntax_Subst.open_branch br  in
                  match uu____62453 with
                  | (p,wopt,t2) ->
                      let uu____62475 = unbound_variables t2  in
                      let uu____62478 =
                        match wopt with
                        | FStar_Pervasives_Native.None  -> []
                        | FStar_Pervasives_Native.Some t3 ->
                            unbound_variables t3
                         in
                      FStar_List.append uu____62475 uu____62478))
           in
        FStar_List.append uu____62435 uu____62438
    | FStar_Syntax_Syntax.Tm_ascribed (t1,asc,uu____62492) ->
        let uu____62533 = unbound_variables t1  in
        let uu____62536 =
          let uu____62539 =
            match FStar_Pervasives_Native.fst asc with
            | FStar_Util.Inl t2 -> unbound_variables t2
            | FStar_Util.Inr c2 -> unbound_variables_comp c2  in
          let uu____62570 =
            match FStar_Pervasives_Native.snd asc with
            | FStar_Pervasives_Native.None  -> []
            | FStar_Pervasives_Native.Some tac -> unbound_variables tac  in
          FStar_List.append uu____62539 uu____62570  in
        FStar_List.append uu____62533 uu____62536
    | FStar_Syntax_Syntax.Tm_let ((false ,lb::[]),t1) ->
        let uu____62611 = unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
        let uu____62614 =
          let uu____62617 = unbound_variables lb.FStar_Syntax_Syntax.lbdef
             in
          let uu____62620 =
            match lb.FStar_Syntax_Syntax.lbname with
            | FStar_Util.Inr uu____62625 -> unbound_variables t1
            | FStar_Util.Inl bv ->
                let uu____62627 =
                  FStar_Syntax_Subst.open_term
                    [(bv, FStar_Pervasives_Native.None)] t1
                   in
                (match uu____62627 with
                 | (uu____62648,t2) -> unbound_variables t2)
             in
          FStar_List.append uu____62617 uu____62620  in
        FStar_List.append uu____62611 uu____62614
    | FStar_Syntax_Syntax.Tm_let ((uu____62650,lbs),t1) ->
        let uu____62670 = FStar_Syntax_Subst.open_let_rec lbs t1  in
        (match uu____62670 with
         | (lbs1,t2) ->
             let uu____62685 = unbound_variables t2  in
             let uu____62688 =
               FStar_List.collect
                 (fun lb  ->
                    let uu____62695 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbtyp  in
                    let uu____62698 =
                      unbound_variables lb.FStar_Syntax_Syntax.lbdef  in
                    FStar_List.append uu____62695 uu____62698) lbs1
                in
             FStar_List.append uu____62685 uu____62688)
    | FStar_Syntax_Syntax.Tm_quoted (tm1,qi) ->
        (match qi.FStar_Syntax_Syntax.qkind with
         | FStar_Syntax_Syntax.Quote_static  -> []
         | FStar_Syntax_Syntax.Quote_dynamic  -> unbound_variables tm1)
    | FStar_Syntax_Syntax.Tm_meta (t1,m) ->
        let uu____62715 = unbound_variables t1  in
        let uu____62718 =
          match m with
          | FStar_Syntax_Syntax.Meta_pattern args ->
              FStar_List.collect
                (FStar_List.collect
                   (fun uu____62757  ->
                      match uu____62757 with
                      | (a,uu____62769) -> unbound_variables a)) args
          | FStar_Syntax_Syntax.Meta_monadic_lift
              (uu____62778,uu____62779,t') -> unbound_variables t'
          | FStar_Syntax_Syntax.Meta_monadic (uu____62785,t') ->
              unbound_variables t'
          | FStar_Syntax_Syntax.Meta_labeled uu____62791 -> []
          | FStar_Syntax_Syntax.Meta_desugared uu____62800 -> []
          | FStar_Syntax_Syntax.Meta_named uu____62801 -> []  in
        FStar_List.append uu____62715 uu____62718

and (unbound_variables_comp :
  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.bv Prims.list)
  =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.GTotal (t,uu____62808) -> unbound_variables t
    | FStar_Syntax_Syntax.Total (t,uu____62818) -> unbound_variables t
    | FStar_Syntax_Syntax.Comp ct ->
        let uu____62828 = unbound_variables ct.FStar_Syntax_Syntax.result_typ
           in
        let uu____62831 =
          FStar_List.collect
            (fun uu____62845  ->
               match uu____62845 with
               | (a,uu____62857) -> unbound_variables a)
            ct.FStar_Syntax_Syntax.effect_args
           in
        FStar_List.append uu____62828 uu____62831

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
            let uu____62972 = head_and_args h  in
            (match uu____62972 with
             | (head1,args) ->
                 let uu____63033 =
                   let uu____63034 = FStar_Syntax_Subst.compress head1  in
                   uu____63034.FStar_Syntax_Syntax.n  in
                 (match uu____63033 with
                  | FStar_Syntax_Syntax.Tm_fvar fv when
                      FStar_Syntax_Syntax.fv_eq_lid fv attr_lid ->
                      let attrs' = FStar_List.rev_acc acc t  in
                      FStar_Pervasives_Native.Some (attrs', args)
                  | uu____63087 -> aux (h :: acc) t))
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
      let uu____63111 =
        extract_attr' attr_lid se.FStar_Syntax_Syntax.sigattrs  in
      match uu____63111 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (attrs',t) ->
          FStar_Pervasives_Native.Some
            ((let uu___2985_63153 = se  in
              {
                FStar_Syntax_Syntax.sigel =
                  (uu___2985_63153.FStar_Syntax_Syntax.sigel);
                FStar_Syntax_Syntax.sigrng =
                  (uu___2985_63153.FStar_Syntax_Syntax.sigrng);
                FStar_Syntax_Syntax.sigquals =
                  (uu___2985_63153.FStar_Syntax_Syntax.sigquals);
                FStar_Syntax_Syntax.sigmeta =
                  (uu___2985_63153.FStar_Syntax_Syntax.sigmeta);
                FStar_Syntax_Syntax.sigattrs = attrs'
              }), t)
  