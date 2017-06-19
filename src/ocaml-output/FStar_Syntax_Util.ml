open Prims
let qual_id: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun id  ->
      let uu____9 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id]) in
      FStar_Ident.set_lid_range uu____9 id.FStar_Ident.idRange
let mk_discriminator: FStar_Ident.lident -> FStar_Ident.lident =
  fun lid  ->
    FStar_Ident.lid_of_ids
      (FStar_List.append lid.FStar_Ident.ns
         [FStar_Ident.mk_ident
            ((Prims.strcat FStar_Ident.reserved_prefix
                (Prims.strcat "is_"
                   (lid.FStar_Ident.ident).FStar_Ident.idText)),
              ((lid.FStar_Ident.ident).FStar_Ident.idRange))])
let is_name: FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    let c =
      FStar_Util.char_at (lid.FStar_Ident.ident).FStar_Ident.idText
        (Prims.parse_int "0") in
    FStar_Util.is_upper c
let arg_of_non_null_binder uu____31 =
  match uu____31 with
  | (b,imp) ->
      let uu____36 = FStar_Syntax_Syntax.bv_to_name b in (uu____36, imp)
let args_of_non_null_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____50 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____50
            then []
            else (let uu____57 = arg_of_non_null_binder b in [uu____57])))
let args_of_binders:
  FStar_Syntax_Syntax.binders ->
    ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun binders  ->
    let uu____72 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____94 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____94
              then
                let b1 =
                  let uu____104 =
                    FStar_Syntax_Syntax.new_bv None
                      (fst b).FStar_Syntax_Syntax.sort in
                  (uu____104, (snd b)) in
                let uu____105 = arg_of_non_null_binder b1 in (b1, uu____105)
              else
                (let uu____113 = arg_of_non_null_binder b in (b, uu____113)))) in
    FStar_All.pipe_right uu____72 FStar_List.unzip
let name_binders:
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____154 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____154
              then
                let uu____157 = b in
                match uu____157 with
                | (a,imp) ->
                    let b1 =
                      let uu____163 =
                        let uu____164 = FStar_Util.string_of_int i in
                        Prims.strcat "_" uu____164 in
                      FStar_Ident.id_of_text uu____163 in
                    let b2 =
                      {
                        FStar_Syntax_Syntax.ppname = b1;
                        FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      } in
                    (b2, imp)
              else b))
let name_function_binders t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
      let uu____194 =
        let uu____197 =
          let uu____198 =
            let uu____206 = name_binders binders in (uu____206, comp) in
          FStar_Syntax_Syntax.Tm_arrow uu____198 in
        FStar_Syntax_Syntax.mk uu____197 in
      uu____194 None t.FStar_Syntax_Syntax.pos
  | uu____223 -> t
let null_binders_of_tks:
  (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____244  ->
            match uu____244 with
            | (t,imp) ->
                let uu____251 =
                  let uu____252 = FStar_Syntax_Syntax.null_binder t in
                  FStar_All.pipe_left FStar_Pervasives.fst uu____252 in
                (uu____251, imp)))
let binders_of_tks:
  (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____279  ->
            match uu____279 with
            | (t,imp) ->
                let uu____292 =
                  FStar_Syntax_Syntax.new_bv
                    (Some (t.FStar_Syntax_Syntax.pos)) t in
                (uu____292, imp)))
let binders_of_freevars:
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let uu____300 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____300
      (FStar_List.map FStar_Syntax_Syntax.mk_binder)
let mk_subst s = [s]
let subst_of_list:
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
let rename_binders:
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
                     let uu____405 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu____405) in
                   FStar_Syntax_Syntax.NT uu____400) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec unmeta: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____413) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____419,uu____420) -> unmeta e2
    | uu____449 -> e1
let rec univ_kernel:
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe* Prims.int) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____458 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____459 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____463 = univ_kernel u1 in
        (match uu____463 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____470 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____474 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let constant_univ_as_nat: FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  -> let uu____481 = univ_kernel u in snd uu____481
let rec compare_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____492,uu____493) ->
          failwith "Impossible: compare_univs"
      | (uu____494,FStar_Syntax_Syntax.U_bvar uu____495) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_unknown ,uu____496) -> - (Prims.parse_int "1")
      | (uu____497,FStar_Syntax_Syntax.U_unknown ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_zero ,uu____498) -> - (Prims.parse_int "1")
      | (uu____499,FStar_Syntax_Syntax.U_zero ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____502,FStar_Syntax_Syntax.U_unif
         uu____503) -> - (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____506,FStar_Syntax_Syntax.U_name
         uu____507) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____516 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
          let uu____517 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
          uu____516 - uu____517
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1 in
          let n2 = FStar_List.length us2 in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____549 = FStar_List.zip us1 us2 in
               FStar_Util.find_map uu____549
                 (fun uu____555  ->
                    match uu____555 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21 in
                        if c <> (Prims.parse_int "0") then Some c else None) in
             match copt with | None  -> Prims.parse_int "0" | Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____565,uu____566) ->
          - (Prims.parse_int "1")
      | (uu____568,FStar_Syntax_Syntax.U_max uu____569) ->
          Prims.parse_int "1"
      | uu____571 ->
          let uu____574 = univ_kernel u1 in
          (match uu____574 with
           | (k1,n1) ->
               let uu____579 = univ_kernel u2 in
               (match uu____579 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2 in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
let eq_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____594 = compare_univs u1 u2 in
      uu____594 = (Prims.parse_int "0")
let ml_comp:
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
let comp_set_flags:
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
              let uu____690 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____690 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____689;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____708 =
              let uu____709 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____709 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____708;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            } in
      let uu___174_719 = c in
      let uu____720 =
        let uu____721 =
          let uu___175_722 = comp_to_comp_typ c in
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
          } in
        FStar_Syntax_Syntax.Comp uu____721 in
      {
        FStar_Syntax_Syntax.n = uu____720;
        FStar_Syntax_Syntax.tk = (uu___174_719.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___174_719.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___174_719.FStar_Syntax_Syntax.vars)
      }
let comp_to_comp_typ:
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
let is_total_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
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
let is_tot_or_gtot_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
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
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
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
let is_pure_effect: FStar_Ident.lident -> Prims.bool =
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
let is_ghost_effect: FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)
let is_pure_or_ghost_comp c =
  (is_pure_comp c) || (is_ghost_effect (comp_effect_name c))
let is_pure_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    ((is_total_lcomp lc) || (is_pure_effect lc.FStar_Syntax_Syntax.eff_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___168_902  ->
               match uu___168_902 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____903 -> false)))
let is_pure_or_ghost_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
let is_pure_or_ghost_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____912 =
      let uu____913 = FStar_Syntax_Subst.compress t in
      uu____913.FStar_Syntax_Syntax.n in
    match uu____912 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____916,c) -> is_pure_or_ghost_comp c
    | uu____928 -> true
let is_lemma_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Syntax_Const.effect_Lemma_lid
  | uu____943 -> false
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____948 =
      let uu____949 = FStar_Syntax_Subst.compress t in
      uu____949.FStar_Syntax_Syntax.n in
    match uu____948 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____952,c) -> is_lemma_comp c
    | uu____964 -> false
let head_and_args:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax*
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) -> (head1, args)
    | uu____1011 -> (t1, [])
let rec head_and_args':
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term*
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head1,args) ->
        let uu____1056 = head_and_args' head1 in
        (match uu____1056 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1092 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1108) ->
        FStar_Syntax_Subst.compress t2
    | uu____1113 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1118 =
      let uu____1119 = FStar_Syntax_Subst.compress t in
      uu____1119.FStar_Syntax_Syntax.n in
    match uu____1118 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1122,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1138)::uu____1139 ->
                  let pats' = unmeta pats in
                  let uu____1170 = head_and_args pats' in
                  (match uu____1170 with
                   | (head1,uu____1181) ->
                       let uu____1196 =
                         let uu____1197 = un_uinst head1 in
                         uu____1197.FStar_Syntax_Syntax.n in
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
        (let uu___176_1292 = ct in
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
let primops: FStar_Ident.lident Prims.list =
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
let is_primop_lid: FStar_Ident.lident -> Prims.bool =
  fun l  ->
    FStar_All.pipe_right primops
      (FStar_Util.for_some (FStar_Ident.lid_equals l))
let is_primop f =
  match f.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_fvar fv ->
      is_primop_lid (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
  | uu____1333 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
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
let uu___is_Equal: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1468 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1473 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1478 -> false
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        let uu____1499 =
          let uu____1507 = unascribe t in head_and_args' uu____1507 in
        match uu____1499 with
        | (hd1,args) ->
            FStar_Syntax_Syntax.mk_Tm_app hd1 args None
              t.FStar_Syntax_Syntax.pos in
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      let equal_if uu___171_1533 = if uu___171_1533 then Equal else Unknown in
      let equal_iff uu___172_1538 = if uu___172_1538 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____1552 -> Unknown in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____1560) -> NotEqual
        | (uu____1561,NotEqual ) -> NotEqual
        | (Unknown ,uu____1562) -> Unknown
        | (uu____1563,Unknown ) -> Unknown in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____1568 = FStar_Syntax_Syntax.fv_eq f g in
          equal_if uu____1568
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____1581 = eq_tm f g in
          eq_and uu____1581
            (fun uu____1582  ->
               let uu____1583 = eq_univs_list us vs in equal_if uu____1583)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____1586 = FStar_Const.eq_const c d in equal_iff uu____1586
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1588),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1590)) ->
          let uu____1615 = FStar_Syntax_Unionfind.equiv u1 u2 in
          equal_if uu____1615
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____1648 =
            let uu____1651 =
              let uu____1652 = un_uinst h1 in
              uu____1652.FStar_Syntax_Syntax.n in
            let uu____1655 =
              let uu____1656 = un_uinst h2 in
              uu____1656.FStar_Syntax_Syntax.n in
            (uu____1651, uu____1655) in
          (match uu____1648 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (f1.FStar_Syntax_Syntax.fv_qual =
                  (Some FStar_Syntax_Syntax.Data_ctor))
                 &&
                 (f2.FStar_Syntax_Syntax.fv_qual =
                    (Some FStar_Syntax_Syntax.Data_ctor))
               ->
               let uu____1663 = FStar_Syntax_Syntax.fv_eq f1 f2 in
               if uu____1663
               then
                 let uu____1665 = FStar_List.zip args1 args2 in
                 FStar_All.pipe_left
                   (FStar_List.fold_left
                      (fun acc  ->
                         fun uu____1695  ->
                           match uu____1695 with
                           | ((a1,q1),(a2,q2)) ->
                               let uu____1711 = eq_tm a1 a2 in
                               eq_inj acc uu____1711) Equal) uu____1665
               else NotEqual
           | uu____1713 ->
               let uu____1716 = eq_tm h1 h2 in
               eq_and uu____1716 (fun uu____1717  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____1720 = eq_univs u v1 in equal_if uu____1720
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1722),uu____1723) ->
          eq_tm t12 t21
      | (uu____1728,FStar_Syntax_Syntax.Tm_meta (t22,uu____1730)) ->
          eq_tm t11 t22
      | uu____1735 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1759)::a11,(b,uu____1762)::b1) ->
          let uu____1800 = eq_tm a b in
          (match uu____1800 with
           | Equal  -> eq_args a11 b1
           | uu____1801 -> Unknown)
      | uu____1802 -> Unknown
and eq_univs_list:
  FStar_Syntax_Syntax.universes ->
    FStar_Syntax_Syntax.universes -> Prims.bool
  =
  fun us  ->
    fun vs  ->
      ((FStar_List.length us) = (FStar_List.length vs)) &&
        (FStar_List.forall2 eq_univs us vs)
let rec unrefine: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1821) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1827,uu____1828) ->
        unrefine t2
    | uu____1857 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1862 =
      let uu____1863 = unrefine t in uu____1863.FStar_Syntax_Syntax.n in
    match uu____1862 with
    | FStar_Syntax_Syntax.Tm_type uu____1866 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1869) -> is_unit t1
    | uu____1874 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1879 =
      let uu____1880 = unrefine t in uu____1880.FStar_Syntax_Syntax.n in
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
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1924 =
      let uu____1925 = FStar_Syntax_Subst.compress e in
      uu____1925.FStar_Syntax_Syntax.n in
    match uu____1924 with
    | FStar_Syntax_Syntax.Tm_abs uu____1928 -> true
    | uu____1943 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1948 =
      let uu____1949 = FStar_Syntax_Subst.compress t in
      uu____1949.FStar_Syntax_Syntax.n in
    match uu____1948 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1952 -> true
    | uu____1960 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1967) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1973,uu____1974) ->
        pre_typ t2
    | uu____2003 -> t1
let destruct:
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list
        option
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ in
      let uu____2019 =
        let uu____2020 = un_uinst typ1 in uu____2020.FStar_Syntax_Syntax.n in
      match uu____2019 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____2058 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____2074 -> None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____2086,lids,uu____2088) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____2093,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2100,uu____2101,uu____2102,uu____2103,uu____2104) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____2110,uu____2111,uu____2112,uu____2113) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____2117,uu____2118,uu____2119,uu____2120,uu____2121) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2125,uu____2126) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2128) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____2131 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____2132 -> []
    | FStar_Syntax_Syntax.Sig_main uu____2133 -> []
let lid_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident option =
  fun se  ->
    match lids_of_sigelt se with | l::[] -> Some l | uu____2142 -> None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb uu___173_2169 =
  match uu___173_2169 with
  | (FStar_Util.Inl x,uu____2176,uu____2177) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____2181,uu____2182) -> FStar_Ident.range_of_lid l
let range_of_arg uu____2203 =
  match uu____2203 with | (hd1,uu____2209) -> hd1.FStar_Syntax_Syntax.pos
let range_of_args args r =
  FStar_All.pipe_right args
    (FStar_List.fold_left
       (fun r1  -> fun a  -> FStar_Range.union_ranges r1 (range_of_arg a)) r)
let mk_app f args =
  let r = range_of_args args f.FStar_Syntax_Syntax.pos in
  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args)) None r
let mk_data l args =
  match args with
  | [] ->
      let uu____2334 =
        let uu____2337 =
          let uu____2338 =
            let uu____2343 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            (uu____2343,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app)) in
          FStar_Syntax_Syntax.Tm_meta uu____2338 in
        FStar_Syntax_Syntax.mk uu____2337 in
      uu____2334 None (FStar_Ident.range_of_lid l)
  | uu____2352 ->
      let e =
        let uu____2361 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor) in
        mk_app uu____2361 args in
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_meta
           (e,
             (FStar_Syntax_Syntax.Meta_desugared FStar_Syntax_Syntax.Data_app)))
        None e.FStar_Syntax_Syntax.pos
let mangle_field_name: FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    FStar_Ident.mk_ident
      ((Prims.strcat "^fname^" x.FStar_Ident.idText),
        (x.FStar_Ident.idRange))
let unmangle_field_name: FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    if FStar_Util.starts_with x.FStar_Ident.idText "^fname^"
    then
      let uu____2378 =
        let uu____2381 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "7") in
        (uu____2381, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____2378
    else x
let field_projector_prefix: Prims.string = "__proj__"
let field_projector_sep: Prims.string = "__item__"
let field_projector_contains_constructor: Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s field_projector_prefix
let mk_field_projector_name_from_string:
  Prims.string -> Prims.string -> Prims.string =
  fun constr  ->
    fun field  ->
      Prims.strcat field_projector_prefix
        (Prims.strcat constr (Prims.strcat field_projector_sep field))
let mk_field_projector_name_from_ident:
  FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun i  ->
      let j = unmangle_field_name i in
      let jtext = j.FStar_Ident.idText in
      let newi =
        if field_projector_contains_constructor jtext
        then j
        else
          FStar_Ident.mk_ident
            ((mk_field_projector_name_from_string
                (lid.FStar_Ident.ident).FStar_Ident.idText jtext),
              (i.FStar_Ident.idRange)) in
      FStar_Ident.lid_of_ids (FStar_List.append lid.FStar_Ident.ns [newi])
let mk_field_projector_name:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.bv ->
      Prims.int -> (FStar_Ident.lident* FStar_Syntax_Syntax.bv)
  =
  fun lid  ->
    fun x  ->
      fun i  ->
        let nm =
          let uu____2422 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____2422
          then
            let uu____2423 =
              let uu____2426 =
                let uu____2427 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____2427 in
              let uu____2428 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____2426, uu____2428) in
            FStar_Ident.mk_ident uu____2423
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___177_2431 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___177_2431.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___177_2431.FStar_Syntax_Syntax.sort)
          } in
        let uu____2432 = mk_field_projector_name_from_ident lid nm in
        (uu____2432, y)
let set_uvar:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____2441 = FStar_Syntax_Unionfind.find uv in
      match uu____2441 with
      | Some uu____2443 ->
          let uu____2444 =
            let uu____2445 =
              let uu____2446 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____2446 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2445 in
          failwith uu____2444
      | uu____2447 -> FStar_Syntax_Unionfind.change uv t
let qualifier_equal:
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
      | uu____2527 -> q1 = q2
let abs:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                   FStar_Syntax_Syntax.cflags Prims.list))
        FStar_Util.either option -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | None  -> lopt1
          | Some (FStar_Util.Inr uu____2587) -> lopt1
          | Some (FStar_Util.Inl lc) ->
              let uu____2608 =
                let uu____2614 = FStar_Syntax_Subst.close_lcomp bs lc in
                FStar_Util.Inl uu____2614 in
              Some uu____2608 in
        match bs with
        | [] -> t
        | uu____2625 ->
            let body =
              let uu____2627 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____2627 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt'),None ) ->
                 let uu____2670 =
                   let uu____2673 =
                     let uu____2674 =
                       let uu____2689 =
                         let uu____2693 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____2693 bs' in
                       let uu____2699 = close_lopt lopt' in
                       (uu____2689, t1, uu____2699) in
                     FStar_Syntax_Syntax.Tm_abs uu____2674 in
                   FStar_Syntax_Syntax.mk uu____2673 in
                 uu____2670 None t1.FStar_Syntax_Syntax.pos
             | uu____2725 ->
                 let uu____2734 =
                   let uu____2737 =
                     let uu____2738 =
                       let uu____2753 = FStar_Syntax_Subst.close_binders bs in
                       let uu____2754 = close_lopt lopt in
                       (uu____2753, body, uu____2754) in
                     FStar_Syntax_Syntax.Tm_abs uu____2738 in
                   FStar_Syntax_Syntax.mk uu____2737 in
                 uu____2734 None t.FStar_Syntax_Syntax.pos)
let arrow:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> comp_result c
      | uu____2799 ->
          let uu____2803 =
            let uu____2806 =
              let uu____2807 =
                let uu____2815 = FStar_Syntax_Subst.close_binders bs in
                let uu____2816 = FStar_Syntax_Subst.close_comp bs c in
                (uu____2815, uu____2816) in
              FStar_Syntax_Syntax.Tm_arrow uu____2807 in
            FStar_Syntax_Syntax.mk uu____2806 in
          uu____2803 None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____2848 =
        let uu____2849 = FStar_Syntax_Subst.compress t in
        uu____2849.FStar_Syntax_Syntax.n in
      match uu____2848 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2869) ->
               let uu____2876 =
                 let uu____2877 = FStar_Syntax_Subst.compress tres in
                 uu____2877.FStar_Syntax_Syntax.n in
               (match uu____2876 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____2894 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c')) uu____2894
                      t.FStar_Syntax_Syntax.pos
                | uu____2910 -> t)
           | uu____2911 -> t)
      | uu____2912 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____2923 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
      let uu____2928 =
        let uu____2929 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____2929 t.FStar_Syntax_Syntax.pos in
      let uu____2930 =
        let uu____2933 =
          let uu____2934 =
            let uu____2939 =
              let uu____2940 =
                let uu____2941 = FStar_Syntax_Syntax.mk_binder b in
                [uu____2941] in
              FStar_Syntax_Subst.close uu____2940 t in
            (b, uu____2939) in
          FStar_Syntax_Syntax.Tm_refine uu____2934 in
        FStar_Syntax_Syntax.mk uu____2933 in
      uu____2930 uu____2923 uu____2928
let branch: FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun b  -> FStar_Syntax_Subst.close_branch b
let rec arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
      FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____2981 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____2981 with
         | (bs1,c1) ->
             let uu____2991 = is_tot_or_gtot_comp c1 in
             if uu____2991
             then
               let uu____2997 = arrow_formals_comp (comp_result c1) in
               (match uu____2997 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____3022 ->
        let uu____3023 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____3023)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
  =
  fun k  ->
    let uu____3040 = arrow_formals_comp k in
    match uu____3040 with | (bs,c) -> (bs, (comp_result c))
let abs_formals:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                   FStar_Syntax_Syntax.cflags Prims.list))
      FStar_Util.either option)
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | Some (FStar_Util.Inl l1) ->
          let l2 =
            let uu___178_3122 = l1 in
            let uu____3123 =
              FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.res_typ in
            {
              FStar_Syntax_Syntax.eff_name =
                (uu___178_3122.FStar_Syntax_Syntax.eff_name);
              FStar_Syntax_Syntax.res_typ = uu____3123;
              FStar_Syntax_Syntax.cflags =
                (uu___178_3122.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                (fun uu____3126  ->
                   let uu____3127 = l1.FStar_Syntax_Syntax.comp () in
                   FStar_Syntax_Subst.subst_comp s uu____3127)
            } in
          Some (FStar_Util.Inl l2)
      | uu____3136 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____3174 =
        let uu____3175 =
          let uu____3178 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____3178 in
        uu____3175.FStar_Syntax_Syntax.n in
      match uu____3174 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____3216 = aux t2 what in
          (match uu____3216 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____3273 -> ([], t1, abs_body_lcomp) in
    let uu____3285 = aux t None in
    match uu____3285 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____3333 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____3333 with
         | (bs1,t2,opening) ->
             let abs_body_lcomp1 = subst_lcomp_opt opening abs_body_lcomp in
             (bs1, t2, abs_body_lcomp1))
let mk_letbinding:
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
let close_univs_and_mk_letbinding:
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
                | (None ,uu____3434) -> def
                | (uu____3440,[]) -> def
                | (Some fvs,uu____3447) ->
                    let universes =
                      FStar_All.pipe_right univ_vars
                        (FStar_List.map
                           (fun _0_26  -> FStar_Syntax_Syntax.U_name _0_26)) in
                    let inst1 =
                      FStar_All.pipe_right fvs
                        (FStar_List.map
                           (fun fv  ->
                              (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                universes))) in
                    FStar_Syntax_InstFV.instantiate inst1 def in
              let typ1 = FStar_Syntax_Subst.close_univ_vars univ_vars typ in
              let def2 = FStar_Syntax_Subst.close_univ_vars univ_vars def1 in
              mk_letbinding lbname univ_vars typ1 eff def2
let open_univ_vars_binders_and_comp:
  FStar_Syntax_Syntax.univ_names ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
      FStar_Syntax_Syntax.comp ->
        (FStar_Syntax_Syntax.univ_names* (FStar_Syntax_Syntax.bv*
          FStar_Syntax_Syntax.aqual) Prims.list* FStar_Syntax_Syntax.comp)
  =
  fun uvs  ->
    fun binders  ->
      fun c  ->
        match binders with
        | [] ->
            let uu____3511 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____3511 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____3527 ->
            let t' = arrow binders c in
            let uu____3534 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____3534 with
             | (uvs1,t'1) ->
                 let uu____3545 =
                   let uu____3546 = FStar_Syntax_Subst.compress t'1 in
                   uu____3546.FStar_Syntax_Syntax.n in
                 (match uu____3545 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____3572 -> failwith "Impossible"))
let is_tuple_constructor_string: Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s "FStar.Pervasives.tuple"
let is_dtuple_constructor_string: Prims.string -> Prims.bool =
  fun s  ->
    (s = "Prims.dtuple2") ||
      (FStar_Util.starts_with s "FStar.Pervasives.dtuple")
let is_tuple_datacon_string: Prims.string -> Prims.bool =
  fun s  -> FStar_Util.starts_with s "FStar.Pervasives.Mktuple"
let is_dtuple_datacon_string: Prims.string -> Prims.bool =
  fun s  ->
    (s = "Prims.Mkdtuple2") ||
      (FStar_Util.starts_with s "FStar.Pervasives.Mkdtuple")
let mod_prefix_dtuple: Prims.int -> Prims.string -> FStar_Ident.lident =
  fun n1  ->
    if n1 = (Prims.parse_int "2")
    then FStar_Syntax_Const.pconst
    else FStar_Syntax_Const.psconst
let is_tuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_tuple_constructor_string
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
    | uu____3615 -> false
let mk_tuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3625 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "tuple%s" uu____3625 in
      let uu____3626 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3626 r
let mk_tuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3636 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mktuple%s" uu____3636 in
      let uu____3637 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3637 r
let is_tuple_data_lid: FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____3646 = mk_tuple_data_lid n1 FStar_Range.dummyRange in
      FStar_Ident.lid_equals f uu____3646
let is_tuple_data_lid': FStar_Ident.lident -> Prims.bool =
  fun f  -> is_tuple_datacon_string f.FStar_Ident.str
let is_tuple_constructor_lid: FStar_Ident.ident -> Prims.bool =
  fun lid  -> is_tuple_constructor_string (FStar_Ident.text_of_id lid)
let is_dtuple_constructor_lid: FStar_Ident.lident -> Prims.bool =
  fun lid  -> is_dtuple_constructor_string lid.FStar_Ident.str
let is_dtuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____3668 -> false
let mk_dtuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3678 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "dtuple%s" uu____3678 in
      let uu____3679 = let uu____3680 = mod_prefix_dtuple n1 in uu____3680 t in
      FStar_Ident.set_lid_range uu____3679 r
let mk_dtuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3692 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mkdtuple%s" uu____3692 in
      let uu____3693 = let uu____3694 = mod_prefix_dtuple n1 in uu____3694 t in
      FStar_Ident.set_lid_range uu____3693 r
let is_dtuple_data_lid': FStar_Ident.lident -> Prims.bool =
  fun f  -> is_dtuple_datacon_string (FStar_Ident.text_of_lid f)
let is_lid_equality: FStar_Ident.lident -> Prims.bool =
  fun x  -> FStar_Ident.lid_equals x FStar_Syntax_Const.eq2_lid
let is_forall: FStar_Ident.lident -> Prims.bool =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Syntax_Const.forall_lid
let is_exists: FStar_Ident.lident -> Prims.bool =
  fun lid  -> FStar_Ident.lid_equals lid FStar_Syntax_Const.exists_lid
let is_qlid: FStar_Ident.lident -> Prims.bool =
  fun lid  -> (is_forall lid) || (is_exists lid)
let is_equality x = is_lid_equality x.FStar_Syntax_Syntax.v
let lid_is_connective: FStar_Ident.lident -> Prims.bool =
  let lst =
    [FStar_Syntax_Const.and_lid;
    FStar_Syntax_Const.or_lid;
    FStar_Syntax_Const.not_lid;
    FStar_Syntax_Const.iff_lid;
    FStar_Syntax_Const.imp_lid] in
  fun lid  -> FStar_Util.for_some (FStar_Ident.lid_equals lid) lst
let is_constructor:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3744 =
        let uu____3745 = pre_typ t in uu____3745.FStar_Syntax_Syntax.n in
      match uu____3744 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3753 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3762 =
        let uu____3763 = pre_typ t in uu____3763.FStar_Syntax_Syntax.n in
      match uu____3762 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3766 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____3768) ->
          is_constructed_typ t1 lid
      | uu____3783 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term option =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____3791 -> Some t1
    | FStar_Syntax_Syntax.Tm_name uu____3792 -> Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____3793 -> Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____3795) -> get_tycon t2
    | uu____3810 -> None
let is_interpreted: FStar_Ident.lident -> Prims.bool =
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
      FStar_Syntax_Const.op_Negation] in
    FStar_Util.for_some (FStar_Ident.lid_equals l) theory_syms
let is_fstar_tactics_embed: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3821 =
      let uu____3822 = un_uinst t in uu____3822.FStar_Syntax_Syntax.n in
    match uu____3821 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv
          FStar_Syntax_Const.fstar_refl_embed_lid
    | uu____3826 -> false
let is_fstar_tactics_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____3831 =
      let uu____3832 = un_uinst t in uu____3832.FStar_Syntax_Syntax.n in
    match uu____3831 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.by_tactic_lid
    | uu____3836 -> false
let ktype:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)) None
    FStar_Range.dummyRange
let ktype0:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax
  =
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)) None
    FStar_Range.dummyRange
let type_u:
  Prims.unit ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.universe)
  =
  fun uu____3862  ->
    let u =
      let uu____3866 = FStar_Syntax_Unionfind.univ_fresh () in
      FStar_All.pipe_left (fun _0_27  -> FStar_Syntax_Syntax.U_unif _0_27)
        uu____3866 in
    let uu____3871 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u) None
        FStar_Range.dummyRange in
    (uu____3871, u)
let kt_kt: FStar_Syntax_Syntax.term = FStar_Syntax_Const.kunary ktype0 ktype0
let kt_kt_kt: FStar_Syntax_Syntax.term =
  FStar_Syntax_Const.kbin ktype0 ktype0 ktype0
let fvar_const: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None
let tand: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.and_lid
let tor: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.or_lid
let timp: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.imp_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")) None
let tiff: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.iff_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "2")) None
let t_bool: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.bool_lid
let t_false: FStar_Syntax_Syntax.term =
  fvar_const FStar_Syntax_Const.false_lid
let t_true: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.true_lid
let b2t_v: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.b2t_lid
let t_not: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.not_lid
let mk_conj_opt:
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
          let uu____3897 =
            let uu____3900 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____3901 =
              let uu____3904 =
                let uu____3905 =
                  let uu____3915 =
                    let uu____3917 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____3918 =
                      let uu____3920 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____3920] in
                    uu____3917 :: uu____3918 in
                  (tand, uu____3915) in
                FStar_Syntax_Syntax.Tm_app uu____3905 in
              FStar_Syntax_Syntax.mk uu____3904 in
            uu____3901 None uu____3900 in
          Some uu____3897
let mk_binop op_t phi1 phi2 =
  let uu____3959 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos in
  let uu____3960 =
    let uu____3963 =
      let uu____3964 =
        let uu____3974 =
          let uu____3976 = FStar_Syntax_Syntax.as_arg phi1 in
          let uu____3977 =
            let uu____3979 = FStar_Syntax_Syntax.as_arg phi2 in [uu____3979] in
          uu____3976 :: uu____3977 in
        (op_t, uu____3974) in
      FStar_Syntax_Syntax.Tm_app uu____3964 in
    FStar_Syntax_Syntax.mk uu____3963 in
  uu____3960 None uu____3959
let mk_neg phi =
  let uu____4002 =
    let uu____4005 =
      let uu____4006 =
        let uu____4016 =
          let uu____4018 = FStar_Syntax_Syntax.as_arg phi in [uu____4018] in
        (t_not, uu____4016) in
      FStar_Syntax_Syntax.Tm_app uu____4006 in
    FStar_Syntax_Syntax.mk uu____4005 in
  uu____4002 None phi.FStar_Syntax_Syntax.pos
let mk_conj phi1 phi2 = mk_binop tand phi1 phi2
let mk_conj_l:
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
          FStar_Syntax_Syntax.Delta_constant None
    | hd1::tl1 -> FStar_List.fold_right mk_conj tl1 hd1
let mk_disj phi1 phi2 = mk_binop tor phi1 phi2
let mk_disj_l:
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd1::tl1 -> FStar_List.fold_right mk_disj tl1 hd1
let mk_imp:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop timp phi1 phi2
let mk_iff:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun phi1  -> fun phi2  -> mk_binop tiff phi1 phi2
let b2t e =
  let uu____4107 =
    let uu____4110 =
      let uu____4111 =
        let uu____4121 =
          let uu____4123 = FStar_Syntax_Syntax.as_arg e in [uu____4123] in
        (b2t_v, uu____4121) in
      FStar_Syntax_Syntax.Tm_app uu____4111 in
    FStar_Syntax_Syntax.mk uu____4110 in
  uu____4107 None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid
let mk_untyped_eq2 e1 e2 =
  let uu____4150 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos in
  let uu____4151 =
    let uu____4154 =
      let uu____4155 =
        let uu____4165 =
          let uu____4167 = FStar_Syntax_Syntax.as_arg e1 in
          let uu____4168 =
            let uu____4170 = FStar_Syntax_Syntax.as_arg e2 in [uu____4170] in
          uu____4167 :: uu____4168 in
        (teq, uu____4165) in
      FStar_Syntax_Syntax.Tm_app uu____4155 in
    FStar_Syntax_Syntax.mk uu____4154 in
  uu____4151 None uu____4150
let mk_eq2:
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
          let eq_inst = FStar_Syntax_Syntax.mk_Tm_uinst teq [u] in
          let uu____4197 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____4198 =
            let uu____4201 =
              let uu____4202 =
                let uu____4212 =
                  let uu____4214 = FStar_Syntax_Syntax.iarg t in
                  let uu____4215 =
                    let uu____4217 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____4218 =
                      let uu____4220 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____4220] in
                    uu____4217 :: uu____4218 in
                  uu____4214 :: uu____4215 in
                (eq_inst, uu____4212) in
              FStar_Syntax_Syntax.Tm_app uu____4202 in
            FStar_Syntax_Syntax.mk uu____4201 in
          uu____4198 None uu____4197
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange in
  let uu____4262 =
    let uu____4265 =
      let uu____4266 =
        let uu____4276 =
          let uu____4278 = FStar_Syntax_Syntax.iarg t in
          let uu____4279 =
            let uu____4281 = FStar_Syntax_Syntax.as_arg x in
            let uu____4282 =
              let uu____4284 = FStar_Syntax_Syntax.as_arg t' in [uu____4284] in
            uu____4281 :: uu____4282 in
          uu____4278 :: uu____4279 in
        (t_has_type1, uu____4276) in
      FStar_Syntax_Syntax.Tm_app uu____4266 in
    FStar_Syntax_Syntax.mk uu____4265 in
  uu____4262 None FStar_Range.dummyRange
let lex_t: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.lex_t_lid
let lex_top: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lextop_lid
    FStar_Syntax_Syntax.Delta_constant (Some FStar_Syntax_Syntax.Data_ctor)
let lex_pair: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.lexcons_lid
    FStar_Syntax_Syntax.Delta_constant (Some FStar_Syntax_Syntax.Data_ctor)
let tforall: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.forall_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")) None
let t_haseq: FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.fvar FStar_Syntax_Const.haseq_lid
    FStar_Syntax_Syntax.Delta_constant None
let lcomp_of_comp:
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.lcomp
  =
  fun c0  ->
    let uu____4304 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____4311 ->
          (FStar_Syntax_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____4318 ->
          (FStar_Syntax_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
    match uu____4304 with
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = ((fun uu____4331  -> c0))
        }
let mk_forall_aux fa x body =
  let uu____4359 =
    let uu____4362 =
      let uu____4363 =
        let uu____4373 =
          let uu____4375 =
            FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
          let uu____4376 =
            let uu____4378 =
              let uu____4379 =
                let uu____4380 =
                  let uu____4381 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____4381] in
                let uu____4382 =
                  let uu____4389 =
                    let uu____4395 =
                      let uu____4396 = FStar_Syntax_Syntax.mk_Total ktype0 in
                      FStar_All.pipe_left lcomp_of_comp uu____4396 in
                    FStar_Util.Inl uu____4395 in
                  Some uu____4389 in
                abs uu____4380 body uu____4382 in
              FStar_Syntax_Syntax.as_arg uu____4379 in
            [uu____4378] in
          uu____4375 :: uu____4376 in
        (fa, uu____4373) in
      FStar_Syntax_Syntax.Tm_app uu____4363 in
    FStar_Syntax_Syntax.mk uu____4362 in
  uu____4359 None FStar_Range.dummyRange
let mk_forall_no_univ:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  = fun x  -> fun body  -> mk_forall_aux tforall x body
let mk_forall:
  FStar_Syntax_Syntax.universe ->
    FStar_Syntax_Syntax.bv ->
      FStar_Syntax_Syntax.typ ->
        (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
          FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    fun x  ->
      fun body  ->
        let tforall1 = FStar_Syntax_Syntax.mk_Tm_uinst tforall [u] in
        mk_forall_aux tforall1 x body
let close_forall_no_univs:
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____4453 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____4453 then f1 else mk_forall_no_univ (fst b) f1) bs f
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____4468 -> true
  | uu____4469 -> false
let if_then_else b t1 t2 =
  let then_branch =
    let uu____4516 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos in
    (uu____4516, None, t1) in
  let else_branch =
    let uu____4539 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos in
    (uu____4539, None, t2) in
  let uu____4551 =
    let uu____4552 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4552 in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____4551
let mk_squash p =
  let sq =
    FStar_Syntax_Syntax.fvar FStar_Syntax_Const.squash_lid
      (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")) None in
  let uu____4612 =
    FStar_Syntax_Syntax.mk_Tm_uinst sq [FStar_Syntax_Syntax.U_zero] in
  let uu____4615 =
    let uu____4621 = FStar_Syntax_Syntax.as_arg p in [uu____4621] in
  mk_app uu____4612 uu____4615
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option
  =
  fun t  ->
    let uu____4629 = head_and_args t in
    match uu____4629 with
    | (head1,args) ->
        let uu____4658 =
          let uu____4666 =
            let uu____4667 = un_uinst head1 in
            uu____4667.FStar_Syntax_Syntax.n in
          (uu____4666, args) in
        (match uu____4658 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____4680)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Syntax_Const.unit_lid
                  ->
                  let uu____4719 =
                    let uu____4722 =
                      let uu____4723 = FStar_Syntax_Syntax.mk_binder b in
                      [uu____4723] in
                    FStar_Syntax_Subst.open_term uu____4722 p in
                  (match uu____4719 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____4741 -> failwith "impossible" in
                       let uu____4744 =
                         let uu____4745 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (fst b1) uu____4745 in
                       if uu____4744 then None else Some p1)
              | uu____4753 -> None)
         | uu____4756 -> None)
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____4776 =
      let uu____4777 = FStar_Syntax_Subst.compress t in
      uu____4777.FStar_Syntax_Syntax.n in
    match uu____4776 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____4838 =
          let uu____4843 =
            let uu____4844 = arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____4844 in
          (b, uu____4843) in
        Some uu____4838
    | uu____4851 -> None
let is_free_in:
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun bv  ->
    fun t  ->
      let uu____4862 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____4862
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | QEx of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | BaseConn of (FStar_Ident.lident* FStar_Syntax_Syntax.args)
let uu___is_QAll: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____4893 -> false
let __proj__QAll__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____4919 -> false
let __proj__QEx__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____4944 -> false
let __proj__BaseConn__item___0:
  connective -> (FStar_Ident.lident* FStar_Syntax_Syntax.args) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0
let destruct_typ_as_formula: FStar_Syntax_Syntax.term -> connective option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1 in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____4971) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____4981) ->
          unmeta_monadic t
      | uu____4991 -> f2 in
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
        (FStar_Syntax_Const.eq3_lid, (Prims.parse_int "2"))] in
      let aux f2 uu____5036 =
        match uu____5036 with
        | (lid,arity) ->
            let uu____5042 =
              let uu____5052 = unmeta_monadic f2 in head_and_args uu____5052 in
            (match uu____5042 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____5071 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____5071 then Some (BaseConn (lid, args)) else None) in
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____5126 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____5126)
      | uu____5133 ->
          let uu____5134 = FStar_Syntax_Subst.compress t1 in ([], uu____5134) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____5176 = head_and_args t1 in
        match uu____5176 with
        | (t2,args) ->
            let uu____5207 = un_uinst t2 in
            let uu____5208 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____5224  ->
                      match uu____5224 with
                      | (t3,imp) ->
                          let uu____5231 = unascribe t3 in (uu____5231, imp))) in
            (uu____5207, uu____5208) in
      let rec aux qopt out t1 =
        let uu____5254 = let uu____5263 = flat t1 in (qopt, uu____5263) in
        match uu____5254 with
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____5278;
                 FStar_Syntax_Syntax.pos = uu____5279;
                 FStar_Syntax_Syntax.vars = uu____5280;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____5283);
                                                             FStar_Syntax_Syntax.tk
                                                               = uu____5284;
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____5285;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____5286;_},uu____5287)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____5348;
                 FStar_Syntax_Syntax.pos = uu____5349;
                 FStar_Syntax_Syntax.vars = uu____5350;_},uu____5351::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____5354);
                  FStar_Syntax_Syntax.tk = uu____5355;
                  FStar_Syntax_Syntax.pos = uu____5356;
                  FStar_Syntax_Syntax.vars = uu____5357;_},uu____5358)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____5426;
               FStar_Syntax_Syntax.pos = uu____5427;
               FStar_Syntax_Syntax.vars = uu____5428;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____5431);
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____5432;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5433;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5434;_},uu____5435)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____5503;
               FStar_Syntax_Syntax.pos = uu____5504;
               FStar_Syntax_Syntax.vars = uu____5505;_},uu____5506::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____5509);
                                                                    FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____5510;
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____5511;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____5512;_},uu____5513)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (Some b,uu____5589) ->
            let bs = FStar_List.rev out in
            let uu____5607 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____5607 with
             | (bs1,t2) ->
                 let uu____5613 = patterns t2 in
                 (match uu____5613 with
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs1, pats, body))
                      else Some (QEx (bs1, pats, body))))
        | uu____5651 -> None in
      aux None [] t in
    let u_connectives =
      [(FStar_Syntax_Const.true_lid, FStar_Syntax_Const.c_true_lid,
         (Prims.parse_int "0"));
      (FStar_Syntax_Const.false_lid, FStar_Syntax_Const.c_false_lid,
        (Prims.parse_int "0"));
      (FStar_Syntax_Const.and_lid, FStar_Syntax_Const.c_and_lid,
        (Prims.parse_int "2"));
      (FStar_Syntax_Const.or_lid, FStar_Syntax_Const.c_or_lid,
        (Prims.parse_int "2"))] in
    let destruct_sq_base_conn t =
      let uu____5687 = un_squash t in
      FStar_Util.bind_opt uu____5687
        (fun t1  ->
           let uu____5696 = head_and_args' t1 in
           match uu____5696 with
           | (hd1,args) ->
               let uu____5717 =
                 let uu____5720 =
                   let uu____5721 = un_uinst hd1 in
                   uu____5721.FStar_Syntax_Syntax.n in
                 (uu____5720, (FStar_List.length args)) in
               (match uu____5717 with
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
                | uu____5781 -> None)) in
    let rec destruct_sq_forall t =
      let uu____5798 = un_squash t in
      FStar_Util.bind_opt uu____5798
        (fun t1  ->
           let uu____5807 = arrow_one t1 in
           match uu____5807 with
           | Some (b,c) ->
               let uu____5816 =
                 let uu____5817 = is_tot_or_gtot_comp c in
                 Prims.op_Negation uu____5817 in
               if uu____5816
               then None
               else
                 (let q =
                    let uu____5823 = comp_to_comp_typ c in
                    uu____5823.FStar_Syntax_Syntax.result_typ in
                  let uu____5824 = FStar_Syntax_Subst.open_term [b] q in
                  match uu____5824 with
                  | (bs,q1) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____5842 -> failwith "impossible" in
                      let uu____5845 = is_free_in (fst b1) q1 in
                      if uu____5845
                      then
                        let uu____5847 = patterns q1 in
                        (match uu____5847 with
                         | (pats,q2) ->
                             FStar_All.pipe_left maybe_collect
                               (Some (QAll ([b1], pats, q2))))
                      else
                        (let uu____5887 =
                           let uu____5888 =
                             let uu____5891 =
                               let uu____5893 =
                                 FStar_Syntax_Syntax.as_arg
                                   (fst b1).FStar_Syntax_Syntax.sort in
                               let uu____5894 =
                                 let uu____5896 =
                                   FStar_Syntax_Syntax.as_arg q1 in
                                 [uu____5896] in
                               uu____5893 :: uu____5894 in
                             (FStar_Syntax_Const.imp_lid, uu____5891) in
                           BaseConn uu____5888 in
                         Some uu____5887))
           | uu____5898 -> None)
    and destruct_sq_exists t =
      let uu____5903 = un_squash t in
      FStar_Util.bind_opt uu____5903
        (fun t1  ->
           let uu____5912 = head_and_args' t1 in
           match uu____5912 with
           | (hd1,args) ->
               let uu____5933 =
                 let uu____5941 =
                   let uu____5942 = un_uinst hd1 in
                   uu____5942.FStar_Syntax_Syntax.n in
                 (uu____5941, args) in
               (match uu____5933 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____5953)::(a2,uu____5955)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.dtuple2_lid
                    ->
                    let uu____5981 =
                      let uu____5982 = FStar_Syntax_Subst.compress a2 in
                      uu____5982.FStar_Syntax_Syntax.n in
                    (match uu____5981 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____5988) ->
                         let uu____6014 = FStar_Syntax_Subst.open_term [b] q in
                         (match uu____6014 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____6036 -> failwith "impossible" in
                              let uu____6039 = patterns q1 in
                              (match uu____6039 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (Some (QEx ([b1], pats, q2)))))
                     | uu____6078 -> None)
                | uu____6079 -> None))
    and maybe_collect f1 =
      match f1 with
      | Some (QAll (bs,pats,phi)) ->
          let uu____6093 = destruct_sq_forall phi in
          (match uu____6093 with
           | Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left (fun _0_36  -> Some _0_36)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____6106 -> f1)
      | Some (QEx (bs,pats,phi)) ->
          let uu____6111 = destruct_sq_exists phi in
          (match uu____6111 with
           | Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____6124 -> f1)
      | uu____6126 -> f1 in
    let phi = unmeta_monadic f in
    let uu____6129 = destruct_base_conn phi in
    FStar_Util.catch_opt uu____6129
      (fun uu____6131  ->
         let uu____6132 = destruct_q_conn phi in
         FStar_Util.catch_opt uu____6132
           (fun uu____6134  ->
              let uu____6135 = destruct_sq_base_conn phi in
              FStar_Util.catch_opt uu____6135
                (fun uu____6137  ->
                   let uu____6138 = destruct_sq_forall phi in
                   FStar_Util.catch_opt uu____6138
                     (fun uu____6140  ->
                        let uu____6141 = destruct_sq_exists phi in
                        FStar_Util.catch_opt uu____6141
                          (fun uu____6143  -> None)))))
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____6153 =
          let uu____6156 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None in
          FStar_Util.Inr uu____6156 in
        let uu____6157 =
          let uu____6158 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____6158 in
        let uu____6161 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn None in
        close_univs_and_mk_letbinding None uu____6153
          a.FStar_Syntax_Syntax.action_univs uu____6157
          FStar_Syntax_Const.effect_Tot_lid uu____6161 in
      {
        FStar_Syntax_Syntax.sigel =
          (FStar_Syntax_Syntax.Sig_let
             ((false, [lb]), [a.FStar_Syntax_Syntax.action_name], []));
        FStar_Syntax_Syntax.sigrng =
          ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.sigquals =
          [FStar_Syntax_Syntax.Visible_default;
          FStar_Syntax_Syntax.Action eff_lid];
        FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta
      }
let mk_reify t =
  let reify_ =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify) None
      t.FStar_Syntax_Syntax.pos in
  let uu____6196 =
    let uu____6199 =
      let uu____6200 =
        let uu____6210 =
          let uu____6212 = FStar_Syntax_Syntax.as_arg t in [uu____6212] in
        (reify_, uu____6210) in
      FStar_Syntax_Syntax.Tm_app uu____6200 in
    FStar_Syntax_Syntax.mk uu____6199 in
  uu____6196 None t.FStar_Syntax_Syntax.pos
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6229 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____6251 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____6252 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____6253 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____6269 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____6278 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____6279 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____6280 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6289) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6294;
           FStar_Syntax_Syntax.index = uu____6295;
           FStar_Syntax_Syntax.sort = t2;_},uu____6297)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____6305) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6311,uu____6312) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____6342) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____6357,t2,uu____6359) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____6382,t2) -> delta_qualifier t2
let rec incr_delta_depth:
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
let incr_delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  -> let uu____6404 = delta_qualifier t in incr_delta_depth uu____6404
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6409 =
      let uu____6410 = FStar_Syntax_Subst.compress t in
      uu____6410.FStar_Syntax_Syntax.n in
    match uu____6409 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6413 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.list option =
  fun e  ->
    let uu____6422 = let uu____6432 = unmeta e in head_and_args uu____6432 in
    match uu____6422 with
    | (head1,args) ->
        let uu____6451 =
          let uu____6459 =
            let uu____6460 = un_uinst head1 in
            uu____6460.FStar_Syntax_Syntax.n in
          (uu____6459, args) in
        (match uu____6451 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6471) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____6484::(hd1,uu____6486)::(tl1,uu____6488)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____6522 =
               let uu____6526 =
                 let uu____6530 = list_elements tl1 in
                 FStar_Util.must uu____6530 in
               hd1 :: uu____6526 in
             Some uu____6522
         | uu____6539 -> None)
let rec apply_last f l =
  match l with
  | [] -> failwith "apply_last: got empty list"
  | a::[] -> let uu____6573 = f a in [uu____6573]
  | x::xs -> let uu____6577 = apply_last f xs in x :: uu____6577
let dm4f_lid:
  FStar_Syntax_Syntax.eff_decl -> Prims.string -> FStar_Ident.lident =
  fun ed  ->
    fun name  ->
      let p = FStar_Ident.path_of_lid ed.FStar_Syntax_Syntax.mname in
      let p' =
        apply_last
          (fun s  ->
             Prims.strcat "_dm4f_" (Prims.strcat s (Prims.strcat "_" name)))
          p in
      FStar_Ident.lid_of_path p' FStar_Range.dummyRange
let rec mk_list:
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____6612 =
            let uu____6615 =
              let uu____6616 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____6616 in
            FStar_Syntax_Syntax.mk uu____6615 in
          uu____6612 None rng in
        let cons1 args pos =
          let uu____6634 =
            let uu____6635 =
              let uu____6636 = ctor FStar_Syntax_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____6636
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____6635 args in
          uu____6634 None pos in
        let nil args pos =
          let uu____6650 =
            let uu____6651 =
              let uu____6652 = ctor FStar_Syntax_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____6652
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____6651 args in
          uu____6650 None pos in
        let uu____6657 =
          let uu____6658 =
            let uu____6659 = FStar_Syntax_Syntax.iarg typ in [uu____6659] in
          nil uu____6658 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____6662 =
                 let uu____6663 = FStar_Syntax_Syntax.iarg typ in
                 let uu____6664 =
                   let uu____6666 = FStar_Syntax_Syntax.as_arg t in
                   let uu____6667 =
                     let uu____6669 = FStar_Syntax_Syntax.as_arg a in
                     [uu____6669] in
                   uu____6666 :: uu____6667 in
                 uu____6663 :: uu____6664 in
               cons1 uu____6662 t.FStar_Syntax_Syntax.pos) l uu____6657
let rec eqlist eq1 xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
  | uu____6717 -> false
let eqsum e1 e2 x y =
  match (x, y) with
  | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
  | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
  | uu____6796 -> false
let eqprod e1 e2 x y =
  match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt e x y =
  match (x, y) with | (Some x1,Some y1) -> e x1 y1 | uu____6914 -> false
let rec term_eq:
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> Prims.bool
  =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        match t.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_app uu____7027 ->
            let uu____7037 = head_and_args' t in
            (match uu____7037 with
             | (hd1,args) ->
                 let uu___179_7059 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.tk =
                     (uu___179_7059.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___179_7059.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___179_7059.FStar_Syntax_Syntax.vars)
                 })
        | uu____7071 -> t in
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
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
      | (uu____7292,uu____7293) -> false
and arg_eq:
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) -> Prims.bool
  =
  fun a1  -> fun a2  -> eqprod term_eq (fun q1  -> fun q2  -> q1 = q2) a1 a2
and binder_eq:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) -> Prims.bool
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
and comp_eq:
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
      | (uu____7366,uu____7367) -> false
and eq_flags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list -> Prims.bool
  = fun f1  -> fun f2  -> false
and branch_eq:
  ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax option*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) -> Prims.bool
  =
  fun uu____7372  ->
    fun uu____7373  ->
      match (uu____7372, uu____7373) with | ((p1,w1,t1),(p2,w2,t2)) -> false
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
        let uu____7485 = FStar_Syntax_Subst.compress t in
        uu____7485.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____7505 =
              let uu____7515 = ff f1 in
              let uu____7516 =
                FStar_List.map
                  (fun uu____7524  ->
                     match uu____7524 with
                     | (a,q) -> let uu____7531 = ff a in (uu____7531, q))
                  args in
              (uu____7515, uu____7516) in
            FStar_Syntax_Syntax.Tm_app uu____7505
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____7560 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____7560 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____7566 =
                   let uu____7581 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____7581, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____7566)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____7606 = let uu____7611 = ff t1 in (uu____7611, us) in
            FStar_Syntax_Syntax.Tm_uinst uu____7606
        | uu____7612 -> tn in
      f
        (let uu___180_7613 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.tk = (uu___180_7613.FStar_Syntax_Syntax.tk);
           FStar_Syntax_Syntax.pos = (uu___180_7613.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___180_7613.FStar_Syntax_Syntax.vars)
         })
let rec sizeof: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____7622 ->
        let uu____7643 =
          let uu____7644 = FStar_Syntax_Subst.compress t in sizeof uu____7644 in
        (Prims.parse_int "1") + uu____7643
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____7646 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____7646
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____7648 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____7648
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____7655 = sizeof t1 in (FStar_List.length us) + uu____7655
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____7664) ->
        let uu____7687 = sizeof t1 in
        let uu____7688 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____7692  ->
                 match uu____7692 with
                 | (bv,uu____7696) ->
                     let uu____7697 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____7697) (Prims.parse_int "0") bs in
        uu____7687 + uu____7688
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____7714 = sizeof hd1 in
        let uu____7715 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____7719  ->
                 match uu____7719 with
                 | (arg,uu____7723) ->
                     let uu____7724 = sizeof arg in acc + uu____7724)
            (Prims.parse_int "0") args in
        uu____7714 + uu____7715
    | uu____7725 -> Prims.parse_int "1"
let is_synth_by_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____7730 =
      let uu____7731 = un_uinst t in uu____7731.FStar_Syntax_Syntax.n in
    match uu____7730 with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.synth_lid
    | uu____7735 -> false