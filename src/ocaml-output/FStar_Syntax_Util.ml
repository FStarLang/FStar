open Prims
let qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun id  ->
      let uu____9 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id])
         in
      FStar_Ident.set_lid_range uu____9 id.FStar_Ident.idRange
  
let mk_discriminator : FStar_Ident.lident -> FStar_Ident.lident =
  fun lid  ->
    FStar_Ident.lid_of_ids
      (FStar_List.append lid.FStar_Ident.ns
         [FStar_Ident.mk_ident
            ((Prims.strcat FStar_Ident.reserved_prefix
                (Prims.strcat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))])
  
let is_name : FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0")
       in
    FStar_Util.is_upper c
  
let arg_of_non_null_binder uu____31 =
  match uu____31 with
  | (b,imp) ->
      let uu____36 = FStar_Syntax_Syntax.bv_to_name b  in (uu____36, imp)
  
let args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____50 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____50
            then []
            else (let uu____57 = arg_of_non_null_binder b  in [uu____57])))
  
let args_of_binders :
  FStar_Syntax_Syntax.binders ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun binders  ->
    let uu____72 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____94 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____94
              then
                let b1 =
                  let uu____104 =
                    FStar_Syntax_Syntax.new_bv None
                      (fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____104, (snd b))  in
                let uu____105 = arg_of_non_null_binder b1  in (b1, uu____105)
              else
                (let uu____113 = arg_of_non_null_binder b  in (b, uu____113))))
       in
    FStar_All.pipe_right uu____72 FStar_List.unzip
  
let name_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____154 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____154
              then
                let uu____157 = b  in
                match uu____157 with
                | (a,imp) ->
                    let b1 =
                      let uu____163 =
                        let uu____164 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____164  in
                      FStar_Ident.id_of_text uu____163  in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      }  in
                    (b2, imp)
              else b))
  
let name_function_binders t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
      let uu____194 =
        let uu____197 =
          let uu____198 =
            let uu____206 = name_binders binders  in (uu____206, comp)  in
          FStar_Syntax_Syntax.Tm_arrow uu____198  in
        FStar_Syntax_Syntax.mk uu____197  in
      uu____194 None t.FStar_Syntax_Syntax.pos
  | uu____223 -> t 
let null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____244  ->
            match uu____244 with
            | (t,imp) ->
                let uu____251 =
                  let uu____252 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____252  in
                (uu____251, imp)))
  
let binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____279  ->
            match uu____279 with
            | (t,imp) ->
                let uu____292 =
                  FStar_Syntax_Syntax.new_bv
                    (Some (t.FStar_Syntax_Syntax.pos)) t
                   in
                (uu____292, imp)))
  
let binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let uu____300 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____300
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
  
let mk_subst s = [s] 
let subst_of_list :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.subst_t
  =
  fun formals  ->
    fun actuals  ->
      if (FStar_List.length formals) = (FStar_List.length actuals)
      then
        FStar_List.fold_right2
          (fun f  ->
             fun a  ->
               fun out  -> (FStar_Syntax_Syntax.NT ((fst f), (fst a))) :: out)
          formals actuals []
      else failwith "Ill-formed substitution"
  
let rename_binders :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.subst_t
  =
  fun replace_xs  ->
    fun with_ys  ->
      if (FStar_List.length replace_xs) = (FStar_List.length with_ys)
      then
        FStar_List.map2
          (fun uu____382  ->
             fun uu____383  ->
               match (uu____382, uu____383) with
               | ((x,uu____393),(y,uu____395)) ->
                   let uu____400 =
                     let uu____405 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____405)  in
                   FStar_Syntax_Syntax.NT uu____400) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____413) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____419,uu____420) -> unmeta e2
    | uu____449 -> e1
  
let rec univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____458 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____459 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____463 = univ_kernel u1  in
        (match uu____463 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____470 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____474 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  -> let uu____481 = univ_kernel u  in snd uu____481 
let rec compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____492,uu____493) ->
          failwith "Impossible: compare_univs"
      | (uu____494,FStar_Syntax_Syntax.U_bvar uu____495) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____496) ->
          ~- (Prims.parse_int "1")
      | (uu____497,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____498) -> ~- (Prims.parse_int "1")
      | (uu____499,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____502,FStar_Syntax_Syntax.U_unif
         uu____503) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____506,FStar_Syntax_Syntax.U_name
         uu____507) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____516 = FStar_Syntax_Unionfind.univ_uvar_id u11  in
          let uu____517 = FStar_Syntax_Unionfind.univ_uvar_id u21  in
          uu____516 - uu____517
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____549 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____549
                 (fun uu____555  ->
                    match uu____555 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0") then Some c else None)
                in
             match copt with | None  -> (Prims.parse_int "0") | Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____565,uu____566) ->
          ~- (Prims.parse_int "1")
      | (uu____568,FStar_Syntax_Syntax.U_max uu____569) ->
          (Prims.parse_int "1")
      | uu____571 ->
          let uu____574 = univ_kernel u1  in
          (match uu____574 with
           | (k1,n1) ->
               let uu____579 = univ_kernel u2  in
               (match uu____579 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____594 = compare_univs u1 u2  in
      uu____594 = (Prims.parse_int "0")
  
let ml_comp :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    FStar_Range.range -> FStar_Syntax_Syntax.comp
  =
  fun t  ->
    fun r  ->
      FStar_Syntax_Syntax.mk_Comp
        {
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
          FStar_Syntax_Syntax.effect_name =
            (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }
  
let comp_effect_name c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.effect_name
  | FStar_Syntax_Syntax.Total uu____625 -> FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.GTotal uu____631 ->
      FStar_Syntax_Const.effect_GTot_lid
  
let comp_flags c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____651 -> [FStar_Syntax_Syntax.TOTAL]
  | FStar_Syntax_Syntax.GTotal uu____657 -> [FStar_Syntax_Syntax.SOMETRIVIAL]
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags 
let comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    fun f  ->
      let comp_to_comp_typ c1 =
        match c1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Comp c2 -> c2
        | FStar_Syntax_Syntax.Total (t,u_opt) ->
            let uu____689 =
              let uu____690 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
              FStar_Util.dflt [] uu____690  in
            {
              FStar_Syntax_Syntax.comp_univs = uu____689;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____708 =
              let uu____709 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
              FStar_Util.dflt [] uu____709  in
            {
              FStar_Syntax_Syntax.comp_univs = uu____708;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
         in
      let uu___174_719 = c  in
      let uu____720 =
        let uu____721 =
          let uu___175_722 = comp_to_comp_typ c  in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___175_722.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___175_722.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___175_722.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___175_722.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____721  in
      {
        FStar_Syntax_Syntax.n = uu____720;
        FStar_Syntax_Syntax.tk = (uu___174_719.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___174_719.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___174_719.FStar_Syntax_Syntax.vars)
      }
  
let comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | FStar_Syntax_Syntax.GTotal (t,Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu____754 ->
        failwith "Assertion failed: Computation type without universe"
  
let is_named_tot c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
        FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.Total uu____769 -> true
  | FStar_Syntax_Syntax.GTotal uu____775 -> false 
let is_total_comp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___162_795  ->
          match uu___162_795 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____796 -> false))
  
let is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Syntax_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___163_802  ->
               match uu___163_802 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____803 -> false)))
  
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
        FStar_Syntax_Const.effect_Tot_lid)
       ||
       (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
          FStar_Syntax_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___164_809  ->
               match uu___164_809 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____810 -> false)))
  
let is_partial_return c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___165_825  ->
          match uu___165_825 with
          | FStar_Syntax_Syntax.RETURN  -> true
          | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
          | uu____826 -> false))
  
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___166_832  ->
            match uu___166_832 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____833 -> false))
  
let is_tot_or_gtot_comp c =
  (is_total_comp c) ||
    (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid
       (comp_effect_name c))
  
let is_pure_effect : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Pure_lid)
  
let is_pure_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____864 -> true
  | FStar_Syntax_Syntax.GTotal uu____870 -> false
  | FStar_Syntax_Syntax.Comp ct ->
      ((is_total_comp c) ||
         (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
        ||
        (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___167_878  ->
                 match uu___167_878 with
                 | FStar_Syntax_Syntax.LEMMA  -> true
                 | uu____879 -> false)))
  
let is_ghost_effect : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)
  
let is_pure_or_ghost_comp c =
  (is_pure_comp c) || (is_ghost_effect (comp_effect_name c)) 
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___168_902  ->
               match uu___168_902 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____903 -> false)))
  
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
  
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____912 =
      let uu____913 = FStar_Syntax_Subst.compress t  in
      uu____913.FStar_Syntax_Syntax.n  in
    match uu____912 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____916,c) -> is_pure_or_ghost_comp c
    | uu____928 -> true
  
let is_lemma_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Syntax_Const.effect_Lemma_lid
  | uu____943 -> false 
let is_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____948 =
      let uu____949 = FStar_Syntax_Subst.compress t  in
      uu____949.FStar_Syntax_Syntax.n  in
    match uu____948 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____952,c) -> is_lemma_comp c
    | uu____964 -> false
  
let head_and_args :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax *
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____1011 -> (t1, [])
  
let rec head_and_args' :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term *
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1056 = head_and_args' head1  in
        (match uu____1056 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1092 -> (t1, [])
  
let un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1108) ->
        FStar_Syntax_Subst.compress t2
    | uu____1113 -> t1
  
let is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1118 =
      let uu____1119 = FStar_Syntax_Subst.compress t  in
      uu____1119.FStar_Syntax_Syntax.n  in
    match uu____1118 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1122,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1138)::uu____1139 ->
                  let pats' = unmeta pats  in
                  let uu____1170 = head_and_args pats'  in
                  (match uu____1170 with
                   | (head1,uu____1181) ->
                       let uu____1196 =
                         let uu____1197 = un_uinst head1  in
                         uu____1197.FStar_Syntax_Syntax.n  in
                       (match uu____1196 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.cons_lid
                        | uu____1201 -> false))
              | uu____1202 -> false)
         | uu____1208 -> false)
    | uu____1209 -> false
  
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
         FStar_Syntax_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___169_1225  ->
                 match uu___169_1225 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____1226 -> false)))
  | uu____1227 -> false 
let comp_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____1244) -> t
  | FStar_Syntax_Syntax.GTotal (t,uu____1252) -> t
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ 
let set_result_typ c t =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____1279 -> FStar_Syntax_Syntax.mk_Total t
  | FStar_Syntax_Syntax.GTotal uu____1285 -> FStar_Syntax_Syntax.mk_GTotal t
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Syntax_Syntax.mk_Comp
        (let uu___176_1292 = ct  in
         {
           FStar_Syntax_Syntax.comp_univs =
             (uu___176_1292.FStar_Syntax_Syntax.comp_univs);
           FStar_Syntax_Syntax.effect_name =
             (uu___176_1292.FStar_Syntax_Syntax.effect_name);
           FStar_Syntax_Syntax.result_typ = t;
           FStar_Syntax_Syntax.effect_args =
             (uu___176_1292.FStar_Syntax_Syntax.effect_args);
           FStar_Syntax_Syntax.flags =
             (uu___176_1292.FStar_Syntax_Syntax.flags)
         })
  
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___170_1307  ->
          match uu___170_1307 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____1308 -> false))
  
let primops : FStar_Ident.lident Prims.list =
  [FStar_Syntax_Const.op_Eq;
  FStar_Syntax_Const.op_notEq;
  FStar_Syntax_Const.op_LT;
  FStar_Syntax_Const.op_LTE;
  FStar_Syntax_Const.op_GT;
  FStar_Syntax_Const.op_GTE;
  FStar_Syntax_Const.op_Subtraction;
  FStar_Syntax_Const.op_Minus;
  FStar_Syntax_Const.op_Addition;
  FStar_Syntax_Const.op_Multiply;
  FStar_Syntax_Const.op_Division;
  FStar_Syntax_Const.op_Modulus;
  FStar_Syntax_Const.op_And;
  FStar_Syntax_Const.op_Or;
  FStar_Syntax_Const.op_Negation] 
let is_primop_lid : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
  
let is_primop f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____1333 -> false 
let rec unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1340,uu____1341) ->
        unascribe e2
    | uu____1370 -> e1
  
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1415,uu____1416) ->
      ascribe t' k
  | uu____1445 ->
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (t, k, None))
        None t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let uu___is_Equal : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1468 -> false
  
let uu___is_NotEqual : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1473 -> false
  
let uu___is_Unknown : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1478 -> false
  
let rec eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        let uu____1499 =
          let uu____1507 = unascribe t  in head_and_args' uu____1507  in
        match uu____1499 with
        | (hd1,args) ->
            FStar_Syntax_Syntax.mk_Tm_app hd1 args None
              t.FStar_Syntax_Syntax.pos
         in
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      let equal_if uu___171_1533 = if uu___171_1533 then Equal else Unknown
         in
      let equal_iff uu___172_1538 = if uu___172_1538 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____1552 -> Unknown
         in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____1560) -> NotEqual
        | (uu____1561,NotEqual ) -> NotEqual
        | (Unknown ,uu____1562) -> Unknown
        | (uu____1563,Unknown ) -> Unknown  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____1568 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____1568
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____1581 = eq_tm f g  in
          eq_and uu____1581
            (fun uu____1582  ->
               let uu____1583 = eq_univs_list us vs  in equal_if uu____1583)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____1586 = FStar_Const.eq_const c d  in equal_iff uu____1586
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1588),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1590)) ->
          let uu____1615 = FStar_Syntax_Unionfind.equiv u1 u2  in
          equal_if uu____1615
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____1648 =
            let uu____1651 =
              let uu____1652 = un_uinst h1  in
              uu____1652.FStar_Syntax_Syntax.n  in
            let uu____1655 =
              let uu____1656 = un_uinst h2  in
              uu____1656.FStar_Syntax_Syntax.n  in
            (uu____1651, uu____1655)  in
          (match uu____1648 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (f1.FStar_Syntax_Syntax.fv_qual =
                  (Some FStar_Syntax_Syntax.Data_ctor))
                 &&
                 (f2.FStar_Syntax_Syntax.fv_qual =
                    (Some FStar_Syntax_Syntax.Data_ctor))
               ->
               let uu____1663 = FStar_Syntax_Syntax.fv_eq f1 f2  in
               if uu____1663
               then
                 let uu____1665 = FStar_List.zip args1 args2  in
                 FStar_All.pipe_left
                   (FStar_List.fold_left
                      (fun acc  ->
                         fun uu____1695  ->
                           match uu____1695 with
                           | ((a1,q1),(a2,q2)) ->
                               let uu____1711 = eq_tm a1 a2  in
                               eq_inj acc uu____1711) Equal) uu____1665
               else NotEqual
           | uu____1713 ->
               let uu____1716 = eq_tm h1 h2  in
               eq_and uu____1716 (fun uu____1717  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____1720 = eq_univs u v1  in equal_if uu____1720
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1722),uu____1723) ->
          eq_tm t12 t21
      | (uu____1728,FStar_Syntax_Syntax.Tm_meta (t22,uu____1730)) ->
          eq_tm t11 t22
      | uu____1735 -> Unknown

and eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1759)::a11,(b,uu____1762)::b1) ->
          let uu____1800 = eq_tm a b  in
          (match uu____1800 with
           | Equal  -> eq_args a11 b1
           | uu____1801 -> Unknown)
      | uu____1802 -> Unknown

and eq_univs_list :
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)

let rec unrefine : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1821) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1827,uu____1828) ->
        unrefine t2
    | uu____1857 -> t1
  
let rec is_unit : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1862 =
      let uu____1863 = unrefine t  in uu____1863.FStar_Syntax_Syntax.n  in
    match uu____1862 with
    | FStar_Syntax_Syntax.Tm_type uu____1866 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1869) -> is_unit t1
    | uu____1874 -> false
  
let rec non_informative : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1879 =
      let uu____1880 = unrefine t  in uu____1880.FStar_Syntax_Syntax.n  in
    match uu____1879 with
    | FStar_Syntax_Syntax.Tm_type uu____1883 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____1886) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1902) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____1907,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____1919 -> false
  
let is_fun : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1924 =
      let uu____1925 = FStar_Syntax_Subst.compress e  in
      uu____1925.FStar_Syntax_Syntax.n  in
    match uu____1924 with
    | FStar_Syntax_Syntax.Tm_abs uu____1928 -> true
    | uu____1938 -> false
  
let is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1943 =
      let uu____1944 = FStar_Syntax_Subst.compress t  in
      uu____1944.FStar_Syntax_Syntax.n  in
    match uu____1943 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1947 -> true
    | uu____1955 -> false
  
let rec pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1962) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1968,uu____1969) ->
        pre_typ t2
    | uu____1998 -> t1
  
let destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list
        option
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____2014 =
        let uu____2015 = un_uinst typ1  in uu____2015.FStar_Syntax_Syntax.n
         in
      match uu____2014 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____2053 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____2069 -> None
  
let lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____2081,lids) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____2085,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2092,uu____2093,uu____2094,uu____2095,uu____2096) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____2102,uu____2103,uu____2104,uu____2105) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____2109,uu____2110,uu____2111,uu____2112,uu____2113) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2117,uu____2118) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2120) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____2123 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____2124 -> []
    | FStar_Syntax_Syntax.Sig_main uu____2125 -> []
  
let lid_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident option =
  fun se  ->
    match lids_of_sigelt se with | l::[] -> Some l | uu____2134 -> None
  
let quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals 
let range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng 
let range_of_lb uu___173_2161 =
  match uu___173_2161 with
  | (FStar_Util.Inl x,uu____2168,uu____2169) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____2173,uu____2174) -> FStar_Ident.range_of_lid l 
let range_of_arg uu____2195 =
  match uu____2195 with | (hd1,uu____2201) -> hd1.FStar_Syntax_Syntax.pos 
let range_of_args args r =
  FStar_All.pipe_right args
    (FStar_List.fold_left
       (fun r1  -> fun a  -> FStar_Range.union_ranges r1 (range_of_arg a)) r)
  
let mk_app f args =
  let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args)) None r 
let mk_data l args =
  match args with
  | [] ->
      let uu____2326 =
        let uu____2329 =
          let uu____2330 =
            let uu____2335 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor)
               in
            (uu____2335,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app))
             in
          FStar_Syntax_Syntax.Tm_meta uu____2330  in
        FStar_Syntax_Syntax.mk uu____2329  in
      uu____2326 None (FStar_Ident.range_of_lid l)
  | uu____2344 ->
      let e =
        let uu____2353 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor)
           in
        mk_app uu____2353 args  in
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_meta
           (e,
             (FStar_Syntax_Syntax.Meta_desugared FStar_Syntax_Syntax.Data_app)))
        None e.FStar_Syntax_Syntax.pos
  
let mangle_field_name : FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    FStar_Ident.mk_ident
      ((Prims.strcat "__fname__" x.FStar_Ident.idText),
        (x.FStar_Ident.idRange))
  
let unmangle_field_name : FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    if FStar_Util.starts_with x.FStar_Ident.idText "__fname__"
    then
      let uu____2370 =
        let uu____2373 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "9")
           in
        (uu____2373, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____2370
    else x
  
let field_projector_prefix : Prims.string = "__proj__" 
let field_projector_sep : Prims.string = "__item__" 
let field_projector_contains_constructor : Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s field_projector_prefix 
let mk_field_projector_name_from_string :
  Prims.string -> Prims.string -> Prims.string =
  fun constr  ->
    fun field  ->
      Prims.strcat field_projector_prefix
        (Prims.strcat constr (Prims.strcat field_projector_sep field))
  
let mk_field_projector_name_from_ident :
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun i  ->
      let j = unmangle_field_name i  in
      let jtext = j.FStar_Ident.idText  in
      let newi =
        if field_projector_contains_constructor jtext
        then j
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText jtext),
              (i.FStar_Ident.idRange))
         in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
  
let mk_field_projector_name :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int -> (FStar_Ident.lident * FStar_Syntax_Syntax.bv)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____2414 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____2414
          then
            let uu____2415 =
              let uu____2418 =
                let uu____2419 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____2419  in
              let uu____2420 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____2418, uu____2420)  in
            FStar_Ident.mk_ident uu____2415
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___177_2423 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___177_2423.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___177_2423.FStar_Syntax_Syntax.sort)
          }  in
        let uu____2424 = mk_field_projector_name_from_ident lid nm  in
        (uu____2424, y)
  
let set_uvar :
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____2433 = FStar_Syntax_Unionfind.find uv  in
      match uu____2433 with
      | Some uu____2435 ->
          let uu____2436 =
            let uu____2437 =
              let uu____2438 = FStar_Syntax_Unionfind.uvar_id uv  in
              FStar_All.pipe_left FStar_Util.string_of_int uu____2438  in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2437  in
          failwith uu____2436
      | uu____2439 -> FStar_Syntax_Unionfind.change uv t
  
let qualifier_equal :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Syntax_Syntax.qualifier -> Prims.bool
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
      | uu____2519 -> q1 = q2
  
let abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.residual_comp option -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | None  -> None
          | Some rc ->
              let uu____2545 =
                let uu___178_2546 = rc  in
                let uu____2547 =
                  FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                    (FStar_Syntax_Subst.close bs)
                   in
                {
                  FStar_Syntax_Syntax.residual_effect =
                    (uu___178_2546.FStar_Syntax_Syntax.residual_effect);
                  FStar_Syntax_Syntax.residual_typ = uu____2547;
                  FStar_Syntax_Syntax.residual_flags =
                    (uu___178_2546.FStar_Syntax_Syntax.residual_flags)
                }  in
              Some uu____2545
           in
        match bs with
        | [] -> t
        | uu____2555 ->
            let body =
              let uu____2557 = FStar_Syntax_Subst.close bs t  in
              FStar_Syntax_Subst.compress uu____2557  in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt'),None ) ->
                 let uu____2575 =
                   let uu____2578 =
                     let uu____2579 =
                       let uu____2589 =
                         let uu____2593 = FStar_Syntax_Subst.close_binders bs
                            in
                         FStar_List.append uu____2593 bs'  in
                       let uu____2599 = close_lopt lopt'  in
                       (uu____2589, t1, uu____2599)  in
                     FStar_Syntax_Syntax.Tm_abs uu____2579  in
                   FStar_Syntax_Syntax.mk uu____2578  in
                 uu____2575 None t1.FStar_Syntax_Syntax.pos
             | uu____2615 ->
                 let uu____2619 =
                   let uu____2622 =
                     let uu____2623 =
                       let uu____2633 = FStar_Syntax_Subst.close_binders bs
                          in
                       let uu____2634 = close_lopt lopt  in
                       (uu____2633, body, uu____2634)  in
                     FStar_Syntax_Syntax.Tm_abs uu____2623  in
                   FStar_Syntax_Syntax.mk uu____2622  in
                 uu____2619 None t.FStar_Syntax_Syntax.pos)
  
let arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____2669 ->
          let uu____2673 =
            let uu____2676 =
              let uu____2677 =
                let uu____2685 = FStar_Syntax_Subst.close_binders bs  in
                let uu____2686 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____2685, uu____2686)  in
              FStar_Syntax_Syntax.Tm_arrow uu____2677  in
            FStar_Syntax_Syntax.mk uu____2676  in
          uu____2673 None c.FStar_Syntax_Syntax.pos
  
let flat_arrow :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____2718 =
        let uu____2719 = FStar_Syntax_Subst.compress t  in
        uu____2719.FStar_Syntax_Syntax.n  in
      match uu____2718 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2739) ->
               let uu____2746 =
                 let uu____2747 = FStar_Syntax_Subst.compress tres  in
                 uu____2747.FStar_Syntax_Syntax.n  in
               (match uu____2746 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____2764 = FStar_ST.read t.FStar_Syntax_Syntax.tk
                       in
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c')) uu____2764
                      t.FStar_Syntax_Syntax.pos
                | uu____2780 -> t)
           | uu____2781 -> t)
      | uu____2782 -> t
  
let refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____2793 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk  in
      let uu____2798 =
        let uu____2799 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____2799 t.FStar_Syntax_Syntax.pos  in
      let uu____2800 =
        let uu____2803 =
          let uu____2804 =
            let uu____2809 =
              let uu____2810 =
                let uu____2811 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____2811]  in
              FStar_Syntax_Subst.close uu____2810 t  in
            (b, uu____2809)  in
          FStar_Syntax_Syntax.Tm_refine uu____2804  in
        FStar_Syntax_Syntax.mk uu____2803  in
      uu____2800 uu____2793 uu____2798
  
let branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let rec arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____2851 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____2851 with
         | (bs1,c1) ->
             let uu____2861 = is_tot_or_gtot_comp c1  in
             if uu____2861
             then
               let uu____2867 = arrow_formals_comp (comp_result c1)  in
               (match uu____2867 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____2892 ->
        let uu____2893 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____2893)
  
let rec arrow_formals :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
  =
  fun k  ->
    let uu____2910 = arrow_formals_comp k  in
    match uu____2910 with | (bs,c) -> (bs, (comp_result c))
  
let abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.residual_comp option)
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | Some rc ->
          let uu____2958 =
            let uu___179_2959 = rc  in
            let uu____2960 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
                (FStar_Syntax_Subst.subst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___179_2959.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____2960;
              FStar_Syntax_Syntax.residual_flags =
                (uu___179_2959.FStar_Syntax_Syntax.residual_flags)
            }  in
          Some uu____2958
      | uu____2966 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____2984 =
        let uu____2985 =
          let uu____2988 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____2988  in
        uu____2985.FStar_Syntax_Syntax.n  in
      match uu____2984 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____3011 = aux t2 what  in
          (match uu____3011 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____3043 -> ([], t1, abs_body_lcomp)  in
    let uu____3050 = aux t None  in
    match uu____3050 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____3073 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____3073 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp  in
             (bs1, t2, abs_body_lcomp1))
  
let mk_letbinding :
  (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
    FStar_Syntax_Syntax.univ_name Prims.list ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax ->
        FStar_Ident.lident ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.letbinding
  =
  fun lbname  ->
    fun univ_vars  ->
      fun typ  ->
        fun eff  ->
          fun def  ->
            {
              FStar_Syntax_Syntax.lbname = lbname;
              FStar_Syntax_Syntax.lbunivs = univ_vars;
              FStar_Syntax_Syntax.lbtyp = typ;
              FStar_Syntax_Syntax.lbeff = eff;
              FStar_Syntax_Syntax.lbdef = def
            }
  
let close_univs_and_mk_letbinding :
  FStar_Syntax_Syntax.fv Prims.list option ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      FStar_Ident.ident Prims.list ->
        FStar_Syntax_Syntax.term ->
          FStar_Ident.lident ->
            FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.letbinding
  =
  fun recs  ->
    fun lbname  ->
      fun univ_vars  ->
        fun typ  ->
          fun eff  ->
            fun def  ->
              let def1 =
                match (recs, univ_vars) with
                | (None ,uu____3159) -> def
                | (uu____3165,[]) -> def
                | (Some fvs,uu____3172) ->
                    let universes =
                      FStar_All.pipe_right univ_vars
                        (FStar_List.map
                           (fun _0_26  -> FStar_Syntax_Syntax.U_name _0_26))
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
              let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ  in
              let def2 = FStar_Syntax_Subst.close_univ_vars univ_vars def1
                 in
              mk_letbinding lbname univ_vars typ1 eff def2
  
let open_univ_vars_binders_and_comp :
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.univ_names * (FStar_Syntax_Syntax.bv *
          FStar_Syntax_Syntax.aqual) Prims.list * FStar_Syntax_Syntax.comp)
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____3236 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____3236 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____3252 ->
            let t' = arrow binders c  in
            let uu____3259 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____3259 with
             | (uvs1,t'1) ->
                 let uu____3270 =
                   let uu____3271 = FStar_Syntax_Subst.compress t'1  in
                   uu____3271.FStar_Syntax_Syntax.n  in
                 (match uu____3270 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____3297 -> failwith "Impossible"))
  
let is_tuple_constructor_string : Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s "FStar.Pervasives.tuple" 
let is_dtuple_constructor_string : Prims.string -> Prims.bool =
  fun s  ->
    (s = "Prims.dtuple2") ||
      (FStar_Util.starts_with s "FStar.Pervasives.dtuple")
  
let is_tuple_datacon_string : Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s "FStar.Pervasives.Mktuple" 
let is_dtuple_datacon_string : Prims.string -> Prims.bool =
  fun s  ->
    (s = "Prims.Mkdtuple2") ||
      (FStar_Util.starts_with s "FStar.Pervasives.Mkdtuple")
  
let mod_prefix_dtuple : Prims.int -> Prims.string -> FStar_Ident.lident =
  fun n1  ->
    if n1 = (Prims.parse_int "2")
    then FStar_Syntax_Const.pconst
    else FStar_Syntax_Const.psconst
  
let is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____3340 -> false
  
let mk_tuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3350 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "tuple%s" uu____3350  in
      let uu____3351 = FStar_Syntax_Const.psconst t  in
      FStar_Ident.set_lid_range uu____3351 r
  
let mk_tuple_data_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3361 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "Mktuple%s" uu____3361  in
      let uu____3362 = FStar_Syntax_Const.psconst t  in
      FStar_Ident.set_lid_range uu____3362 r
  
let is_tuple_data_lid : FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____3371 = mk_tuple_data_lid n1 FStar_Range.dummyRange  in
      FStar_Ident.lid_equals f uu____3371
  
let is_tuple_data_lid' : FStar_Ident.lident -> Prims.bool =
  fun f  -> is_tuple_datacon_string f.FStar_Ident.str 
let is_tuple_constructor_lid : FStar_Ident.ident -> Prims.bool =
  fun lid  -> is_tuple_constructor_string (FStar_Ident.text_of_id lid) 
let is_dtuple_constructor_lid : FStar_Ident.lident -> Prims.bool =
  fun lid  -> is_dtuple_constructor_string lid.FStar_Ident.str 
let is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____3393 -> false
  
let mk_dtuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3403 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "dtuple%s" uu____3403  in
      let uu____3404 = let uu____3405 = mod_prefix_dtuple n1  in uu____3405 t
         in
      FStar_Ident.set_lid_range uu____3404 r
  
let mk_dtuple_data_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3417 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "Mkdtuple%s" uu____3417  in
      let uu____3418 = let uu____3419 = mod_prefix_dtuple n1  in uu____3419 t
         in
      FStar_Ident.set_lid_range uu____3418 r
  
let is_dtuple_data_lid' : FStar_Ident.lident -> Prims.bool =
  fun f  -> is_dtuple_datacon_string (FStar_Ident.text_of_lid f) 
let is_lid_equality : FStar_Ident.lident -> Prims.bool =
  fun x  -> FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid 
let is_forall : FStar_Ident.lident -> Prims.bool =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid 
let is_exists : FStar_Ident.lident -> Prims.bool =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid 
let is_qlid : FStar_Ident.lident -> Prims.bool =
  fun lid  -> (is_forall lid) || (is_exists lid) 
let is_equality x = is_lid_equality x.FStar_Syntax_Syntax.v 
let lid_is_connective : FStar_Ident.lident -> Prims.bool =
  let lst =
    [FStar_Syntax_Const.and_lid;
    FStar_Syntax_Const.or_lid;
    FStar_Syntax_Const.not_lid;
    FStar_Syntax_Const.iff_lid;
    FStar_Syntax_Const.imp_lid]  in
  fun lid  -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst 
let is_constructor :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3469 =
        let uu____3470 = pre_typ t  in uu____3470.FStar_Syntax_Syntax.n  in
      match uu____3469 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3478 -> false
  
let rec is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3487 =
        let uu____3488 = pre_typ t  in uu____3488.FStar_Syntax_Syntax.n  in
      match uu____3487 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3491 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____3493) ->
          is_constructed_typ t1 lid
      | uu____3508 -> false
  
let rec get_tycon :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term option =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____3516 -> Some t1
    | FStar_Syntax_Syntax.Tm_name uu____3517 -> Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____3518 -> Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____3520) -> get_tycon t2
    | uu____3535 -> None
  
let is_interpreted : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    let theory_syms =
      [FStar_Syntax_Const.op_Eq;
      FStar_Syntax_Const.op_notEq;
      FStar_Syntax_Const.op_LT;
      FStar_Syntax_Const.op_LTE;
      FStar_Syntax_Const.op_GT;
      FStar_Syntax_Const.op_GTE;
      FStar_Syntax_Const.op_Subtraction;
      FStar_Syntax_Const.op_Minus;
      FStar_Syntax_Const.op_Addition;
      FStar_Syntax_Const.op_Multiply;
      FStar_Syntax_Const.op_Division;
      FStar_Syntax_Const.op_Modulus;
      FStar_Syntax_Const.op_And;
      FStar_Syntax_Const.op_Or;
      FStar_Syntax_Const.op_Negation]  in
    FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms
  
let is_fstar_tactics_embed : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3546 =
      let uu____3547 = un_uinst t  in uu____3547.FStar_Syntax_Syntax.n  in
    match uu____3546 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_refl_embed_lid
    | uu____3551 -> false
  
let is_fstar_tactics_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3556 =
      let uu____3557 = un_uinst t  in uu____3557.FStar_Syntax_Syntax.n  in
    match uu____3556 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.by_tactic_lid
    | uu____3561 -> false
  
let ktype :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)) None
    FStar_Range.dummyRange
  
let ktype0 :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)) None
    FStar_Range.dummyRange
  
let type_u :
  Prims.unit ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.universe)
  =
  fun uu____3587  ->
    let u =
      let uu____3591 = FStar_Syntax_Unionfind.univ_fresh ()  in
      FStar_All.pipe_left (fun _0_27  -> FStar_Syntax_Syntax.U_unif _0_27)
        uu____3591
       in
    let uu____3596 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u) None
        FStar_Range.dummyRange
       in
    (uu____3596, u)
  
let kt_kt : FStar_Syntax_Syntax.term =
  FStar_Syntax_Const.kunary ktype0 ktype0 
let kt_kt_kt : FStar_Syntax_Syntax.term =
  FStar_Syntax_Const.kbin ktype0 ktype0 ktype0 
let fvar_const : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None
  
let tand : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.and_lid 
let tor : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.or_lid 
let timp : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")) None
  
let tiff : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2")) None
  
let t_bool : FStar_Syntax_Syntax.term =
  fvar_const FStar_Syntax_Const.bool_lid 
let t_false : FStar_Syntax_Syntax.term =
  fvar_const FStar_Syntax_Const.false_lid 
let t_true : FStar_Syntax_Syntax.term =
  fvar_const FStar_Syntax_Const.true_lid 
let b2t_v : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.b2t_lid 
let t_not : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.not_lid 
let mk_conj_opt :
  FStar_Syntax_Syntax.term option ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax option
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | None  -> Some phi2
      | Some phi11 ->
          let uu____3622 =
            let uu____3625 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____3626 =
              let uu____3629 =
                let uu____3630 =
                  let uu____3640 =
                    let uu____3642 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____3643 =
                      let uu____3645 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____3645]  in
                    uu____3642 :: uu____3643  in
                  (tand, uu____3640)  in
                FStar_Syntax_Syntax.Tm_app uu____3630  in
              FStar_Syntax_Syntax.mk uu____3629  in
            uu____3626 None uu____3625  in
          Some uu____3622
  
let mk_binop op_t phi1 phi2 =
  let uu____3684 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos
     in
  let uu____3685 =
    let uu____3688 =
      let uu____3689 =
        let uu____3699 =
          let uu____3701 = FStar_Syntax_Syntax.as_arg phi1  in
          let uu____3702 =
            let uu____3704 = FStar_Syntax_Syntax.as_arg phi2  in [uu____3704]
             in
          uu____3701 :: uu____3702  in
        (op_t, uu____3699)  in
      FStar_Syntax_Syntax.Tm_app uu____3689  in
    FStar_Syntax_Syntax.mk uu____3688  in
  uu____3685 None uu____3684 
let mk_neg phi =
  let uu____3727 =
    let uu____3730 =
      let uu____3731 =
        let uu____3741 =
          let uu____3743 = FStar_Syntax_Syntax.as_arg phi  in [uu____3743]
           in
        (t_not, uu____3741)  in
      FStar_Syntax_Syntax.Tm_app uu____3731  in
    FStar_Syntax_Syntax.mk uu____3730  in
  uu____3727 None phi.FStar_Syntax_Syntax.pos 
let mk_conj phi1 phi2 = mk_binop tand phi1 phi2 
let mk_conj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
          FStar_Syntax_Syntax.Delta_constant None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
  
let mk_disj phi1 phi2 = mk_binop tor phi1 phi2 
let mk_disj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
  
let mk_imp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2 
let mk_iff :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2 
let b2t e =
  let uu____3832 =
    let uu____3835 =
      let uu____3836 =
        let uu____3846 =
          let uu____3848 = FStar_Syntax_Syntax.as_arg e  in [uu____3848]  in
        (b2t_v, uu____3846)  in
      FStar_Syntax_Syntax.Tm_app uu____3836  in
    FStar_Syntax_Syntax.mk uu____3835  in
  uu____3832 None e.FStar_Syntax_Syntax.pos 
let teq : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid 
let mk_untyped_eq2 e1 e2 =
  let uu____3875 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos
     in
  let uu____3876 =
    let uu____3879 =
      let uu____3880 =
        let uu____3890 =
          let uu____3892 = FStar_Syntax_Syntax.as_arg e1  in
          let uu____3893 =
            let uu____3895 = FStar_Syntax_Syntax.as_arg e2  in [uu____3895]
             in
          uu____3892 :: uu____3893  in
        (teq, uu____3890)  in
      FStar_Syntax_Syntax.Tm_app uu____3880  in
    FStar_Syntax_Syntax.mk uu____3879  in
  uu____3876 None uu____3875 
let mk_eq2 :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
            FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    fun t  ->
      fun e1  ->
        fun e2  ->
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u]  in
          let uu____3922 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____3923 =
            let uu____3926 =
              let uu____3927 =
                let uu____3937 =
                  let uu____3939 = FStar_Syntax_Syntax.iarg t  in
                  let uu____3940 =
                    let uu____3942 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____3943 =
                      let uu____3945 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____3945]  in
                    uu____3942 :: uu____3943  in
                  uu____3939 :: uu____3940  in
                (eq_inst, uu____3937)  in
              FStar_Syntax_Syntax.Tm_app uu____3927  in
            FStar_Syntax_Syntax.mk uu____3926  in
          uu____3923 None uu____3922
  
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid  in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange
     in
  let uu____3987 =
    let uu____3990 =
      let uu____3991 =
        let uu____4001 =
          let uu____4003 = FStar_Syntax_Syntax.iarg t  in
          let uu____4004 =
            let uu____4006 = FStar_Syntax_Syntax.as_arg x  in
            let uu____4007 =
              let uu____4009 = FStar_Syntax_Syntax.as_arg t'  in [uu____4009]
               in
            uu____4006 :: uu____4007  in
          uu____4003 :: uu____4004  in
        (t_has_type1, uu____4001)  in
      FStar_Syntax_Syntax.Tm_app uu____3991  in
    FStar_Syntax_Syntax.mk uu____3990  in
  uu____3987 None FStar_Range.dummyRange 
let lex_t : FStar_Syntax_Syntax.term =
  fvar_const FStar_Syntax_Const.lex_t_lid 
let lex_top : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid
    FStar_Syntax_Syntax.Delta_constant (Some FStar_Syntax_Syntax.Data_ctor)
  
let lex_pair : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid
    FStar_Syntax_Syntax.Delta_constant (Some FStar_Syntax_Syntax.Data_ctor)
  
let tforall : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")) None
  
let t_haseq : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.haseq_lid
    FStar_Syntax_Syntax.Delta_constant None
  
let lcomp_of_comp :
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.lcomp
  =
  fun c0  ->
    let uu____4029 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____4036 ->
          (FStar_Syntax_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____4043 ->
          (FStar_Syntax_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags))
       in
    match uu____4029 with
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = ((fun uu____4056  -> c0))
        }
  
let mk_residual_comp :
  FStar_Ident.lident ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option ->
      FStar_Syntax_Syntax.cflags Prims.list ->
        FStar_Syntax_Syntax.residual_comp
  =
  fun l  ->
    fun t  ->
      fun f  ->
        {
          FStar_Syntax_Syntax.residual_effect = l;
          FStar_Syntax_Syntax.residual_typ = t;
          FStar_Syntax_Syntax.residual_flags = f
        }
  
let residual_tot :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.residual_comp
  =
  fun t  ->
    {
      FStar_Syntax_Syntax.residual_effect = FStar_Syntax_Const.effect_Tot_lid;
      FStar_Syntax_Syntax.residual_typ = (Some t);
      FStar_Syntax_Syntax.residual_flags = [FStar_Syntax_Syntax.TOTAL]
    }
  
let residual_comp_of_comp :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.residual_comp =
  fun c  ->
    {
      FStar_Syntax_Syntax.residual_effect = (comp_effect_name c);
      FStar_Syntax_Syntax.residual_typ = (Some (comp_result c));
      FStar_Syntax_Syntax.residual_flags = (comp_flags c)
    }
  
let residual_comp_of_lcomp :
  FStar_Syntax_Syntax.lcomp -> FStar_Syntax_Syntax.residual_comp =
  fun lc  ->
    {
      FStar_Syntax_Syntax.residual_effect = (lc.FStar_Syntax_Syntax.eff_name);
      FStar_Syntax_Syntax.residual_typ =
        (Some (lc.FStar_Syntax_Syntax.res_typ));
      FStar_Syntax_Syntax.residual_flags = (lc.FStar_Syntax_Syntax.cflags)
    }
  
let mk_forall_aux fa x body =
  let uu____4126 =
    let uu____4129 =
      let uu____4130 =
        let uu____4140 =
          let uu____4142 =
            FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
          let uu____4143 =
            let uu____4145 =
              let uu____4146 =
                let uu____4147 =
                  let uu____4148 = FStar_Syntax_Syntax.mk_binder x  in
                  [uu____4148]  in
                abs uu____4147 body (Some (residual_tot ktype0))  in
              FStar_Syntax_Syntax.as_arg uu____4146  in
            [uu____4145]  in
          uu____4142 :: uu____4143  in
        (fa, uu____4140)  in
      FStar_Syntax_Syntax.Tm_app uu____4130  in
    FStar_Syntax_Syntax.mk uu____4129  in
  uu____4126 None FStar_Range.dummyRange 
let mk_forall_no_univ :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun x  -> fun body  -> mk_forall_aux tforall x body 
let mk_forall :
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    fun x  ->
      fun body  ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u]  in
        mk_forall_aux tforall1 x body
  
let close_forall_no_univs :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____4193 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____4193 then f1 else mk_forall_no_univ (fst b) f1) bs f
  
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____4208 -> true
  | uu____4209 -> false 
let if_then_else b t1 t2 =
  let then_branch =
    let uu____4256 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos
       in
    (uu____4256, None, t1)  in
  let else_branch =
    let uu____4279 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos
       in
    (uu____4279, None, t2)  in
  let uu____4291 =
    let uu____4292 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos
       in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4292  in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____4291
  
let mk_squash p =
  let sq =
    FStar_Syntax_Syntax.fvar FStar_Syntax_Const.squash_lid
      (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")) None
     in
  let uu____4352 =
    FStar_Syntax_Syntax.mk_Tm_uinst sq [FStar_Syntax_Syntax.U_zero]  in
  let uu____4355 =
    let uu____4361 = FStar_Syntax_Syntax.as_arg p  in [uu____4361]  in
  mk_app uu____4352 uu____4355 
let un_squash :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option
  =
  fun t  ->
    let uu____4369 = head_and_args t  in
    match uu____4369 with
    | (head1,args) ->
        let uu____4398 =
          let uu____4406 =
            let uu____4407 = un_uinst head1  in
            uu____4407.FStar_Syntax_Syntax.n  in
          (uu____4406, args)  in
        (match uu____4398 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____4420)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Syntax_Const.unit_lid
                  ->
                  let uu____4459 =
                    let uu____4462 =
                      let uu____4463 = FStar_Syntax_Syntax.mk_binder b  in
                      [uu____4463]  in
                    FStar_Syntax_Subst.open_term uu____4462 p  in
                  (match uu____4459 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____4481 -> failwith "impossible"  in
                       let uu____4484 =
                         let uu____4485 = FStar_Syntax_Free.names p1  in
                         FStar_Util.set_mem (fst b1) uu____4485  in
                       if uu____4484 then None else Some p1)
              | uu____4493 -> None)
         | uu____4496 -> None)
  
let arrow_one :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____4516 =
      let uu____4517 = FStar_Syntax_Subst.compress t  in
      uu____4517.FStar_Syntax_Syntax.n  in
    match uu____4516 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____4578 =
          let uu____4583 =
            let uu____4584 = arrow bs c  in
            FStar_Syntax_Syntax.mk_Total uu____4584  in
          (b, uu____4583)  in
        Some uu____4578
    | uu____4591 -> None
  
let is_free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun bv  ->
    fun t  ->
      let uu____4602 = FStar_Syntax_Free.names t  in
      FStar_Util.set_mem bv uu____4602
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let uu___is_QAll : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____4633 -> false
  
let __proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let uu___is_QEx : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____4659 -> false
  
let __proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let uu___is_BaseConn : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____4684 -> false
  
let __proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0 
let destruct_typ_as_formula : FStar_Syntax_Syntax.term -> connective option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____4711) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____4721) ->
          unmeta_monadic t
      | uu____4731 -> f2  in
    let destruct_base_conn f1 =
      let connectives =
        [(FStar_Syntax_Const.true_lid, (Prims.parse_int "0"));
        (FStar_Syntax_Const.false_lid, (Prims.parse_int "0"));
        (FStar_Syntax_Const.and_lid, (Prims.parse_int "2"));
        (FStar_Syntax_Const.or_lid, (Prims.parse_int "2"));
        (FStar_Syntax_Const.imp_lid, (Prims.parse_int "2"));
        (FStar_Syntax_Const.iff_lid, (Prims.parse_int "2"));
        (FStar_Syntax_Const.ite_lid, (Prims.parse_int "3"));
        (FStar_Syntax_Const.not_lid, (Prims.parse_int "1"));
        (FStar_Syntax_Const.eq2_lid, (Prims.parse_int "3"));
        (FStar_Syntax_Const.eq2_lid, (Prims.parse_int "2"));
        (FStar_Syntax_Const.eq3_lid, (Prims.parse_int "4"));
        (FStar_Syntax_Const.eq3_lid, (Prims.parse_int "2"))]  in
      let aux f2 uu____4776 =
        match uu____4776 with
        | (lid,arity) ->
            let uu____4782 =
              let uu____4792 = unmeta_monadic f2  in head_and_args uu____4792
               in
            (match uu____4782 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____4811 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____4811 then Some (BaseConn (lid, args)) else None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____4866 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____4866)
      | uu____4873 ->
          let uu____4874 = FStar_Syntax_Subst.compress t1  in
          ([], uu____4874)
       in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____4916 = head_and_args t1  in
        match uu____4916 with
        | (t2,args) ->
            let uu____4947 = un_uinst t2  in
            let uu____4948 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____4964  ->
                      match uu____4964 with
                      | (t3,imp) ->
                          let uu____4971 = unascribe t3  in (uu____4971, imp)))
               in
            (uu____4947, uu____4948)
         in
      let rec aux qopt out t1 =
        let uu____4994 = let uu____5003 = flat t1  in (qopt, uu____5003)  in
        match uu____4994 with
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____5018;
                 FStar_Syntax_Syntax.pos = uu____5019;
                 FStar_Syntax_Syntax.vars = uu____5020;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____5023);
                                                             FStar_Syntax_Syntax.tk
                                                               = uu____5024;
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____5025;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____5026;_},uu____5027)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____5078;
                 FStar_Syntax_Syntax.pos = uu____5079;
                 FStar_Syntax_Syntax.vars = uu____5080;_},uu____5081::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____5084);
                  FStar_Syntax_Syntax.tk = uu____5085;
                  FStar_Syntax_Syntax.pos = uu____5086;
                  FStar_Syntax_Syntax.vars = uu____5087;_},uu____5088)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____5146;
               FStar_Syntax_Syntax.pos = uu____5147;
               FStar_Syntax_Syntax.vars = uu____5148;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____5151);
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____5152;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5153;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5154;_},uu____5155)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____5213;
               FStar_Syntax_Syntax.pos = uu____5214;
               FStar_Syntax_Syntax.vars = uu____5215;_},uu____5216::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____5219);
                                                                    FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____5220;
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____5221;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____5222;_},uu____5223)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (Some b,uu____5289) ->
            let bs = FStar_List.rev out  in
            let uu____5307 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____5307 with
             | (bs1,t2) ->
                 let uu____5313 = patterns t2  in
                 (match uu____5313 with
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs1, pats, body))
                      else Some (QEx (bs1, pats, body))))
        | uu____5351 -> None  in
      aux None [] t  in
    let u_connectives =
      [(FStar_Syntax_Const.true_lid, FStar_Syntax_Const.c_true_lid,
         (Prims.parse_int "0"));
      (FStar_Syntax_Const.false_lid, FStar_Syntax_Const.c_false_lid,
        (Prims.parse_int "0"));
      (FStar_Syntax_Const.and_lid, FStar_Syntax_Const.c_and_lid,
        (Prims.parse_int "2"));
      (FStar_Syntax_Const.or_lid, FStar_Syntax_Const.c_or_lid,
        (Prims.parse_int "2"))]
       in
    let destruct_sq_base_conn t =
      let uu____5387 = un_squash t  in
      FStar_Util.bind_opt uu____5387
        (fun t1  ->
           let uu____5396 = head_and_args' t1  in
           match uu____5396 with
           | (hd1,args) ->
               let uu____5417 =
                 let uu____5420 =
                   let uu____5421 = un_uinst hd1  in
                   uu____5421.FStar_Syntax_Syntax.n  in
                 (uu____5420, (FStar_List.length args))  in
               (match uu____5417 with
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_28) when
                    (_0_28 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.c_and_lid)
                    -> Some (BaseConn (FStar_Syntax_Const.and_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_29) when
                    (_0_29 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.c_or_lid)
                    -> Some (BaseConn (FStar_Syntax_Const.or_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_30) when
                    (_0_30 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.c_eq2_lid)
                    -> Some (BaseConn (FStar_Syntax_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_31) when
                    (_0_31 = (Prims.parse_int "3")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.c_eq2_lid)
                    -> Some (BaseConn (FStar_Syntax_Const.eq2_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_32) when
                    (_0_32 = (Prims.parse_int "2")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.c_eq3_lid)
                    -> Some (BaseConn (FStar_Syntax_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_33) when
                    (_0_33 = (Prims.parse_int "4")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.c_eq3_lid)
                    -> Some (BaseConn (FStar_Syntax_Const.eq3_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_34) when
                    (_0_34 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.c_true_lid)
                    -> Some (BaseConn (FStar_Syntax_Const.true_lid, args))
                | (FStar_Syntax_Syntax.Tm_fvar fv,_0_35) when
                    (_0_35 = (Prims.parse_int "0")) &&
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.c_false_lid)
                    -> Some (BaseConn (FStar_Syntax_Const.false_lid, args))
                | uu____5481 -> None))
       in
    let rec destruct_sq_forall t =
      let uu____5498 = un_squash t  in
      FStar_Util.bind_opt uu____5498
        (fun t1  ->
           let uu____5507 = arrow_one t1  in
           match uu____5507 with
           | Some (b,c) ->
               let uu____5516 =
                 let uu____5517 = is_tot_or_gtot_comp c  in
                 Prims.op_Negation uu____5517  in
               if uu____5516
               then None
               else
                 (let q =
                    let uu____5523 = comp_to_comp_typ c  in
                    uu____5523.FStar_Syntax_Syntax.result_typ  in
                  let uu____5524 = FStar_Syntax_Subst.open_term [b] q  in
                  match uu____5524 with
                  | (bs,q1) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____5542 -> failwith "impossible"  in
                      let uu____5545 = is_free_in (fst b1) q1  in
                      if uu____5545
                      then
                        let uu____5547 = patterns q1  in
                        (match uu____5547 with
                         | (pats,q2) ->
                             FStar_All.pipe_left maybe_collect
                               (Some (QAll ([b1], pats, q2))))
                      else
                        (let uu____5587 =
                           let uu____5588 =
                             let uu____5591 =
                               let uu____5593 =
                                 FStar_Syntax_Syntax.as_arg
                                   (fst b1).FStar_Syntax_Syntax.sort
                                  in
                               let uu____5594 =
                                 let uu____5596 =
                                   FStar_Syntax_Syntax.as_arg q1  in
                                 [uu____5596]  in
                               uu____5593 :: uu____5594  in
                             (FStar_Syntax_Const.imp_lid, uu____5591)  in
                           BaseConn uu____5588  in
                         Some uu____5587))
           | uu____5598 -> None)
    
    and destruct_sq_exists t =
      let uu____5603 = un_squash t  in
      FStar_Util.bind_opt uu____5603
        (fun t1  ->
           let uu____5612 = head_and_args' t1  in
           match uu____5612 with
           | (hd1,args) ->
               let uu____5633 =
                 let uu____5641 =
                   let uu____5642 = un_uinst hd1  in
                   uu____5642.FStar_Syntax_Syntax.n  in
                 (uu____5641, args)  in
               (match uu____5633 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____5653)::(a2,uu____5655)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.dtuple2_lid
                    ->
                    let uu____5681 =
                      let uu____5682 = FStar_Syntax_Subst.compress a2  in
                      uu____5682.FStar_Syntax_Syntax.n  in
                    (match uu____5681 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____5688) ->
                         let uu____5704 = FStar_Syntax_Subst.open_term [b] q
                            in
                         (match uu____5704 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____5726 -> failwith "impossible"  in
                              let uu____5729 = patterns q1  in
                              (match uu____5729 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (Some (QEx ([b1], pats, q2)))))
                     | uu____5768 -> None)
                | uu____5769 -> None))
    
    and maybe_collect f1 =
      match f1 with
      | Some (QAll (bs,pats,phi)) ->
          let uu____5783 = destruct_sq_forall phi  in
          (match uu____5783 with
           | Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left (fun _0_36  -> Some _0_36)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____5796 -> f1)
      | Some (QEx (bs,pats,phi)) ->
          let uu____5801 = destruct_sq_exists phi  in
          (match uu____5801 with
           | Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____5814 -> f1)
      | uu____5816 -> f1
     in
    let phi = unmeta_monadic f  in
    let uu____5819 = destruct_base_conn phi  in
    FStar_Util.catch_opt uu____5819
      (fun uu____5821  ->
         let uu____5822 = destruct_q_conn phi  in
         FStar_Util.catch_opt uu____5822
           (fun uu____5824  ->
              let uu____5825 = destruct_sq_base_conn phi  in
              FStar_Util.catch_opt uu____5825
                (fun uu____5827  ->
                   let uu____5828 = destruct_sq_forall phi  in
                   FStar_Util.catch_opt uu____5828
                     (fun uu____5830  ->
                        let uu____5831 = destruct_sq_exists phi  in
                        FStar_Util.catch_opt uu____5831
                          (fun uu____5833  -> None)))))
  
let action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____5843 =
          let uu____5846 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None
             in
          FStar_Util.Inr uu____5846  in
        let uu____5847 =
          let uu____5848 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ  in
          arrow a.FStar_Syntax_Syntax.action_params uu____5848  in
        let uu____5851 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn None
           in
        close_univs_and_mk_letbinding None uu____5843
          a.FStar_Syntax_Syntax.action_univs uu____5847
          FStar_Syntax_Const.effect_Tot_lid uu____5851
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
  
let mk_reify t =
  let reify_ =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify) None
      t.FStar_Syntax_Syntax.pos
     in
  let uu____5880 =
    let uu____5883 =
      let uu____5884 =
        let uu____5894 =
          let uu____5896 = FStar_Syntax_Syntax.as_arg t  in [uu____5896]  in
        (reify_, uu____5894)  in
      FStar_Syntax_Syntax.Tm_app uu____5884  in
    FStar_Syntax_Syntax.mk uu____5883  in
  uu____5880 None t.FStar_Syntax_Syntax.pos 
let rec delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____5913 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____5929 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____5930 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____5931 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____5947 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____5956 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____5957 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____5958 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5967) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____5972;
           FStar_Syntax_Syntax.index = uu____5973;
           FStar_Syntax_Syntax.sort = t2;_},uu____5975)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____5983) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5989,uu____5990) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____6020) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____6035,t2,uu____6037) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____6050,t2) -> delta_qualifier t2
  
let rec incr_delta_depth :
  FStar_Syntax_Syntax.delta_depth -> FStar_Syntax_Syntax.delta_depth =
  fun d  ->
    match d with
    | FStar_Syntax_Syntax.Delta_equational  -> d
    | FStar_Syntax_Syntax.Delta_constant  ->
        FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")
    | FStar_Syntax_Syntax.Delta_defined_at_level i ->
        FStar_Syntax_Syntax.Delta_defined_at_level
          (i + (Prims.parse_int "1"))
    | FStar_Syntax_Syntax.Delta_abstract d1 -> incr_delta_depth d1
  
let incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let uu____6072 = delta_qualifier t  in incr_delta_depth uu____6072
  
let is_unknown : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6077 =
      let uu____6078 = FStar_Syntax_Subst.compress t  in
      uu____6078.FStar_Syntax_Syntax.n  in
    match uu____6077 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6081 -> false
  
let rec list_elements :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.list option =
  fun e  ->
    let uu____6090 = let uu____6100 = unmeta e  in head_and_args uu____6100
       in
    match uu____6090 with
    | (head1,args) ->
        let uu____6119 =
          let uu____6127 =
            let uu____6128 = un_uinst head1  in
            uu____6128.FStar_Syntax_Syntax.n  in
          (uu____6127, args)  in
        (match uu____6119 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6139) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____6152::(hd1,uu____6154)::(tl1,uu____6156)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____6190 =
               let uu____6194 =
                 let uu____6198 = list_elements tl1  in
                 FStar_Util.must uu____6198  in
               hd1 :: uu____6194  in
             Some uu____6190
         | uu____6207 -> None)
  
let rec apply_last f l =
  match l with
  | [] -> failwith "apply_last: got empty list"
  | a::[] -> let uu____6241 = f a  in [uu____6241]
  | x::xs -> let uu____6245 = apply_last f xs  in x :: uu____6245 
let dm4f_lid :
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident =
  fun ed  ->
    fun name  ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname  in
      let p' =
        apply_last
          (fun s  ->
             Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))
          p
         in
      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
  
let rec mk_list :
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____6280 =
            let uu____6283 =
              let uu____6284 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (Some FStar_Syntax_Syntax.Data_ctor)
                 in
              FStar_Syntax_Syntax.Tm_fvar uu____6284  in
            FStar_Syntax_Syntax.mk uu____6283  in
          uu____6280 None rng  in
        let cons1 args pos =
          let uu____6302 =
            let uu____6303 =
              let uu____6304 = ctor FStar_Syntax_Const.cons_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____6304
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____6303 args  in
          uu____6302 None pos  in
        let nil args pos =
          let uu____6318 =
            let uu____6319 =
              let uu____6320 = ctor FStar_Syntax_Const.nil_lid  in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____6320
                [FStar_Syntax_Syntax.U_zero]
               in
            FStar_Syntax_Syntax.mk_Tm_app uu____6319 args  in
          uu____6318 None pos  in
        let uu____6325 =
          let uu____6326 =
            let uu____6327 = FStar_Syntax_Syntax.iarg typ  in [uu____6327]
             in
          nil uu____6326 rng  in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____6330 =
                 let uu____6331 = FStar_Syntax_Syntax.iarg typ  in
                 let uu____6332 =
                   let uu____6334 = FStar_Syntax_Syntax.as_arg t  in
                   let uu____6335 =
                     let uu____6337 = FStar_Syntax_Syntax.as_arg a  in
                     [uu____6337]  in
                   uu____6334 :: uu____6335  in
                 uu____6331 :: uu____6332  in
               cons1 uu____6330 t.FStar_Syntax_Syntax.pos) l uu____6325
  
let rec eqlist eq1 xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
  | uu____6385 -> false 
let eqsum e1 e2 x y =
  match (x, y) with
  | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
  | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
  | uu____6464 -> false 
let eqprod e1 e2 x y =
  match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2) 
let eqopt e x y =
  match (x, y) with | (Some x1,Some y1) -> e x1 y1 | uu____6582 -> false 
let rec term_eq :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> Prims.bool
  =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_app uu____6695 ->
            let uu____6705 = head_and_args' t  in
            (match uu____6705 with
             | (hd1,args) ->
                 let uu___180_6727 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.tk =
                     (uu___180_6727.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___180_6727.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___180_6727.FStar_Syntax_Syntax.vars)
                 })
        | uu____6739 -> t  in
      let t11 = canon_app t1  in
      let t21 = canon_app t2  in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
          x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
          FStar_Syntax_Syntax.bv_eq x y
      | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
          FStar_Syntax_Syntax.fv_eq x y
      | (FStar_Syntax_Syntax.Tm_uinst (t12,us1),FStar_Syntax_Syntax.Tm_uinst
         (t22,us2)) -> (eqlist eq_univs us1 us2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_constant x,FStar_Syntax_Syntax.Tm_constant y)
          -> x = y
      | (FStar_Syntax_Syntax.Tm_type x,FStar_Syntax_Syntax.Tm_type y) ->
          x = y
      | (FStar_Syntax_Syntax.Tm_abs (b1,t12,k1),FStar_Syntax_Syntax.Tm_abs
         (b2,t22,k2)) -> (eqlist binder_eq b1 b2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
         (f2,a2)) -> (term_eq f1 f2) && (eqlist arg_eq a1 a2)
      | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
         (b2,c2)) -> (eqlist binder_eq b1 b2) && (comp_eq c1 c2)
      | (FStar_Syntax_Syntax.Tm_refine (b1,t12),FStar_Syntax_Syntax.Tm_refine
         (b2,t22)) -> (FStar_Syntax_Syntax.bv_eq b1 b2) && (term_eq t12 t22)
      | (FStar_Syntax_Syntax.Tm_match (t12,bs1),FStar_Syntax_Syntax.Tm_match
         (t22,bs2)) -> (term_eq t12 t22) && (eqlist branch_eq bs1 bs2)
      | (uu____6940,uu____6941) -> false

and arg_eq :
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) -> Prims.bool
  =
  fun a1  -> fun a2  -> eqprod term_eq (fun q1  -> fun q2  -> q1 = q2) a1 a2

and binder_eq :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) -> Prims.bool
  =
  fun b1  ->
    fun b2  ->
      eqprod
        (fun b11  ->
           fun b21  ->
             term_eq b11.FStar_Syntax_Syntax.sort
               b21.FStar_Syntax_Syntax.sort) (fun q1  -> fun q2  -> q1 = q2)
        b1 b2

and lcomp_eq c1 c2 = false

and residual_eq r1 r2 = false

and comp_eq :
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      Prims.bool
  =
  fun c1  ->
    fun c2  ->
      match ((c1.FStar_Syntax_Syntax.n), (c2.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Total (t1,u1),FStar_Syntax_Syntax.Total (t2,u2))
          -> term_eq t1 t2
      | (FStar_Syntax_Syntax.GTotal (t1,u1),FStar_Syntax_Syntax.GTotal
         (t2,u2)) -> term_eq t1 t2
      | (FStar_Syntax_Syntax.Comp c11,FStar_Syntax_Syntax.Comp c21) ->
          ((((c11.FStar_Syntax_Syntax.comp_univs =
                c21.FStar_Syntax_Syntax.comp_univs)
               &&
               (c11.FStar_Syntax_Syntax.effect_name =
                  c21.FStar_Syntax_Syntax.effect_name))
              &&
              (term_eq c11.FStar_Syntax_Syntax.result_typ
                 c21.FStar_Syntax_Syntax.result_typ))
             &&
             (eqlist arg_eq c11.FStar_Syntax_Syntax.effect_args
                c21.FStar_Syntax_Syntax.effect_args))
            &&
            (eq_flags c11.FStar_Syntax_Syntax.flags
               c21.FStar_Syntax_Syntax.flags)
      | (uu____7014,uu____7015) -> false

and eq_flags :
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list -> Prims.bool
  = fun f1  -> fun f2  -> false

and branch_eq :
  ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax option *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t *
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option *
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) -> Prims.bool
  =
  fun uu____7020  ->
    fun uu____7021  ->
      match (uu____7020, uu____7021) with | ((p1,w1,t1),(p2,w2,t2)) -> false

let rec bottom_fold :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f  in
      let tn =
        let uu____7133 = FStar_Syntax_Subst.compress t  in
        uu____7133.FStar_Syntax_Syntax.n  in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____7153 =
              let uu____7163 = ff f1  in
              let uu____7164 =
                FStar_List.map
                  (fun uu____7172  ->
                     match uu____7172 with
                     | (a,q) -> let uu____7179 = ff a  in (uu____7179, q))
                  args
                 in
              (uu____7163, uu____7164)  in
            FStar_Syntax_Syntax.Tm_app uu____7153
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____7198 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____7198 with
             | (bs1,t') ->
                 let t'' = ff t'  in
                 let uu____7204 =
                   let uu____7214 = FStar_Syntax_Subst.close bs1 t''  in
                   (bs1, uu____7214, k)  in
                 FStar_Syntax_Syntax.Tm_abs uu____7204)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____7234 = let uu____7239 = ff t1  in (uu____7239, us)  in
            FStar_Syntax_Syntax.Tm_uinst uu____7234
        | uu____7240 -> tn  in
      f
        (let uu___181_7241 = t  in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.tk = (uu___181_7241.FStar_Syntax_Syntax.tk);
           FStar_Syntax_Syntax.pos = (uu___181_7241.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___181_7241.FStar_Syntax_Syntax.vars)
         })
  
let rec sizeof : FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____7250 ->
        let uu____7265 =
          let uu____7266 = FStar_Syntax_Subst.compress t  in
          sizeof uu____7266  in
        (Prims.parse_int "1") + uu____7265
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____7268 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____7268
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____7270 = sizeof bv.FStar_Syntax_Syntax.sort  in
        (Prims.parse_int "1") + uu____7270
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____7277 = sizeof t1  in (FStar_List.length us) + uu____7277
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____7286) ->
        let uu____7299 = sizeof t1  in
        let uu____7300 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____7304  ->
                 match uu____7304 with
                 | (bv,uu____7308) ->
                     let uu____7309 = sizeof bv.FStar_Syntax_Syntax.sort  in
                     acc + uu____7309) (Prims.parse_int "0") bs
           in
        uu____7299 + uu____7300
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____7326 = sizeof hd1  in
        let uu____7327 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____7331  ->
                 match uu____7331 with
                 | (arg,uu____7335) ->
                     let uu____7336 = sizeof arg  in acc + uu____7336)
            (Prims.parse_int "0") args
           in
        uu____7326 + uu____7327
    | uu____7337 -> (Prims.parse_int "1")
  
let is_synth_by_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____7342 =
      let uu____7343 = un_uinst t  in uu____7343.FStar_Syntax_Syntax.n  in
    match uu____7342 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.synth_lid
    | uu____7347 -> false
  
let mk_alien b s r =
  let uu____7371 =
    let uu____7374 =
      let uu____7375 =
        let uu____7380 =
          let uu____7381 =
            let uu____7384 = FStar_Dyn.mkdyn b  in (uu____7384, s)  in
          FStar_Syntax_Syntax.Meta_alien uu____7381  in
        (FStar_Syntax_Syntax.tun, uu____7380)  in
      FStar_Syntax_Syntax.Tm_meta uu____7375  in
    FStar_Syntax_Syntax.mk uu____7374  in
  uu____7371 None
    (match r with | Some r1 -> r1 | None  -> FStar_Range.dummyRange)
  
let un_alien : FStar_Syntax_Syntax.term -> FStar_Dyn.dyn =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        (uu____7400,FStar_Syntax_Syntax.Meta_alien (blob,uu____7402)) -> blob
    | uu____7407 -> failwith "Something paranormal occurred"
  