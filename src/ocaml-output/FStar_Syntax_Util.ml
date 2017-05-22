open Prims
let qual_id: FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun id  ->
      let uu____7 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id]) in
      FStar_Ident.set_lid_range uu____7 id.FStar_Ident.idRange
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
let arg_of_non_null_binder uu____25 =
  match uu____25 with
  | (b,imp) ->
      let uu____30 = FStar_Syntax_Syntax.bv_to_name b in (uu____30, imp)
let args_of_non_null_binders:
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____43 = FStar_Syntax_Syntax.is_null_binder b in
            if uu____43
            then []
            else (let uu____50 = arg_of_non_null_binder b in [uu____50])))
let args_of_binders:
  FStar_Syntax_Syntax.binders ->
    ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun binders  ->
    let uu____64 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____86 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____86
              then
                let b1 =
                  let uu____96 =
                    FStar_Syntax_Syntax.new_bv None
                      (Prims.fst b).FStar_Syntax_Syntax.sort in
                  (uu____96, (Prims.snd b)) in
                let uu____97 = arg_of_non_null_binder b1 in (b1, uu____97)
              else
                (let uu____105 = arg_of_non_null_binder b in (b, uu____105)))) in
    FStar_All.pipe_right uu____64 FStar_List.unzip
let name_binders:
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____145 = FStar_Syntax_Syntax.is_null_binder b in
              if uu____145
              then
                let uu____148 = b in
                match uu____148 with
                | (a,imp) ->
                    let b1 =
                      let uu____154 =
                        let uu____155 = FStar_Util.string_of_int i in
                        Prims.strcat "_" uu____155 in
                      FStar_Ident.id_of_text uu____154 in
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
      let uu____183 =
        let uu____186 =
          let uu____187 =
            let uu____195 = name_binders binders in (uu____195, comp) in
          FStar_Syntax_Syntax.Tm_arrow uu____187 in
        FStar_Syntax_Syntax.mk uu____186 in
      uu____183 None t.FStar_Syntax_Syntax.pos
  | uu____212 -> t
let null_binders_of_tks:
  (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____232  ->
            match uu____232 with
            | (t,imp) ->
                let uu____239 =
                  let uu____240 = FStar_Syntax_Syntax.null_binder t in
                  FStar_All.pipe_left Prims.fst uu____240 in
                (uu____239, imp)))
let binders_of_tks:
  (FStar_Syntax_Syntax.typ* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____266  ->
            match uu____266 with
            | (t,imp) ->
                let uu____279 =
                  FStar_Syntax_Syntax.new_bv
                    (Some (t.FStar_Syntax_Syntax.pos)) t in
                (uu____279, imp)))
let binders_of_freevars:
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let uu____286 = FStar_Util.set_elements fvs in
    FStar_All.pipe_right uu____286
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
               fun out  ->
                 (FStar_Syntax_Syntax.NT ((Prims.fst f), (Prims.fst a))) ::
                 out) formals actuals []
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
          (fun uu____354  ->
             fun uu____355  ->
               match (uu____354, uu____355) with
               | ((x,uu____365),(y,uu____367)) ->
                   let uu____372 =
                     let uu____377 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu____377) in
                   FStar_Syntax_Syntax.NT uu____372) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec unmeta: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,_)|FStar_Syntax_Syntax.Tm_ascribed
      (e2,_,_) -> unmeta e2
    | uu____407 -> e1
let rec univ_kernel:
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe* Prims.int) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown 
      |FStar_Syntax_Syntax.U_name _
       |FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  ->
        (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____418 = univ_kernel u1 in
        (match uu____418 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____425 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____429 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let constant_univ_as_nat: FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  -> let uu____435 = univ_kernel u in Prims.snd uu____435
let rec compare_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar _,_)|(_,FStar_Syntax_Syntax.U_bvar _) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_unknown ,uu____448) -> - (Prims.parse_int "1")
      | (uu____449,FStar_Syntax_Syntax.U_unknown ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_zero ,uu____450) -> - (Prims.parse_int "1")
      | (uu____451,FStar_Syntax_Syntax.U_zero ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____454,FStar_Syntax_Syntax.U_unif
         uu____455) -> - (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____458,FStar_Syntax_Syntax.U_name
         uu____459) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____468 = FStar_Unionfind.uvar_id u11 in
          let uu____470 = FStar_Unionfind.uvar_id u21 in
          uu____468 - uu____470
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1 in
          let n2 = FStar_List.length us2 in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____492 = FStar_List.zip us1 us2 in
               FStar_Util.find_map uu____492
                 (fun uu____498  ->
                    match uu____498 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21 in
                        if c <> (Prims.parse_int "0") then Some c else None) in
             match copt with | None  -> Prims.parse_int "0" | Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____508,uu____509) ->
          - (Prims.parse_int "1")
      | (uu____511,FStar_Syntax_Syntax.U_max uu____512) ->
          Prims.parse_int "1"
      | uu____514 ->
          let uu____517 = univ_kernel u1 in
          (match uu____517 with
           | (k1,n1) ->
               let uu____522 = univ_kernel u2 in
               (match uu____522 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2 in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
let eq_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____535 = compare_univs u1 u2 in
      uu____535 = (Prims.parse_int "0")
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
  | FStar_Syntax_Syntax.Total uu____562 -> FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.GTotal uu____568 ->
      FStar_Syntax_Const.effect_GTot_lid
let comp_flags c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____586 -> [FStar_Syntax_Syntax.TOTAL]
  | FStar_Syntax_Syntax.GTotal uu____592 -> [FStar_Syntax_Syntax.SOMETRIVIAL]
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
        | FStar_Syntax_Syntax.Total (t,u_opt)|FStar_Syntax_Syntax.GTotal
          (t,u_opt) ->
            let uu____628 =
              let uu____629 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____629 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____628;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            } in
      let uu___175_639 = c in
      let uu____640 =
        let uu____641 =
          let uu___176_642 = comp_to_comp_typ c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___176_642.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___176_642.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___176_642.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___176_642.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____641 in
      {
        FStar_Syntax_Syntax.n = uu____640;
        FStar_Syntax_Syntax.tk = (uu___175_639.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___175_639.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___175_639.FStar_Syntax_Syntax.vars)
      }
let comp_to_comp_typ:
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,Some u)|FStar_Syntax_Syntax.GTotal
      (t,Some u) ->
        {
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_name = (comp_effect_name c);
          FStar_Syntax_Syntax.result_typ = t;
          FStar_Syntax_Syntax.effect_args = [];
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu____667 ->
        failwith "Assertion failed: Computation type without universe"
let is_named_tot c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
        FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.Total uu____680 -> true
  | FStar_Syntax_Syntax.GTotal uu____686 -> false
let is_total_comp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___163_704  ->
          match uu___163_704 with
          | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  -> true
          | uu____705 -> false))
let is_total_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Syntax_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___164_710  ->
               match uu___164_710 with
               | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  ->
                   true
               | uu____711 -> false)))
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
            (fun uu___165_716  ->
               match uu___165_716 with
               | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  ->
                   true
               | uu____717 -> false)))
let is_partial_return c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___166_730  ->
          match uu___166_730 with
          | FStar_Syntax_Syntax.RETURN |FStar_Syntax_Syntax.PARTIAL_RETURN 
              -> true
          | uu____731 -> false))
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___167_736  ->
            match uu___167_736 with
            | FStar_Syntax_Syntax.RETURN |FStar_Syntax_Syntax.PARTIAL_RETURN 
                -> true
            | uu____737 -> false))
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
  | FStar_Syntax_Syntax.Total uu____763 -> true
  | FStar_Syntax_Syntax.GTotal uu____769 -> false
  | FStar_Syntax_Syntax.Comp ct ->
      ((is_total_comp c) ||
         (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
        ||
        (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___168_777  ->
                 match uu___168_777 with
                 | FStar_Syntax_Syntax.LEMMA  -> true
                 | uu____778 -> false)))
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
            (fun uu___169_797  ->
               match uu___169_797 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____798 -> false)))
let is_pure_or_ghost_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
let is_pure_or_ghost_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____805 =
      let uu____806 = FStar_Syntax_Subst.compress t in
      uu____806.FStar_Syntax_Syntax.n in
    match uu____805 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____809,c) -> is_pure_or_ghost_comp c
    | uu____821 -> true
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____825 =
      let uu____826 = FStar_Syntax_Subst.compress t in
      uu____826.FStar_Syntax_Syntax.n in
    match uu____825 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____829,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct ->
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
         | uu____842 -> false)
    | uu____843 -> false
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
    | uu____889 -> (t1, [])
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
        let uu____933 = head_and_args' head1 in
        (match uu____933 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____969 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____984) ->
        FStar_Syntax_Subst.compress t2
    | uu____989 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____993 =
      let uu____994 = FStar_Syntax_Subst.compress t in
      uu____994.FStar_Syntax_Syntax.n in
    match uu____993 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____997,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1013)::uu____1014 ->
                  let pats' = unmeta pats in
                  let uu____1045 = head_and_args pats' in
                  (match uu____1045 with
                   | (head1,uu____1056) ->
                       let uu____1071 =
                         let uu____1072 = un_uinst head1 in
                         uu____1072.FStar_Syntax_Syntax.n in
                       (match uu____1071 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.cons_lid
                        | uu____1076 -> false))
              | uu____1077 -> false)
         | uu____1083 -> false)
    | uu____1084 -> false
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
         FStar_Syntax_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___170_1098  ->
                 match uu___170_1098 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____1099 -> false)))
  | uu____1100 -> false
let comp_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,_)|FStar_Syntax_Syntax.GTotal (t,_) -> t
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let set_result_typ c t =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____1144 -> FStar_Syntax_Syntax.mk_Total t
  | FStar_Syntax_Syntax.GTotal uu____1150 -> FStar_Syntax_Syntax.mk_GTotal t
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Syntax_Syntax.mk_Comp
        (let uu___177_1157 = ct in
         {
           FStar_Syntax_Syntax.comp_univs =
             (uu___177_1157.FStar_Syntax_Syntax.comp_univs);
           FStar_Syntax_Syntax.effect_name =
             (uu___177_1157.FStar_Syntax_Syntax.effect_name);
           FStar_Syntax_Syntax.result_typ = t;
           FStar_Syntax_Syntax.effect_args =
             (uu___177_1157.FStar_Syntax_Syntax.effect_args);
           FStar_Syntax_Syntax.flags =
             (uu___177_1157.FStar_Syntax_Syntax.flags)
         })
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___171_1170  ->
          match uu___171_1170 with
          | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  -> true
          | uu____1171 -> false))
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
  | uu____1193 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1199,uu____1200) ->
        unascribe e2
    | uu____1229 -> e1
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1271,uu____1272) ->
      ascribe t' k
  | uu____1301 ->
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (t, k, None))
        None t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal
  | NotEqual
  | Unknown
let uu___is_Equal: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1323 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1327 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1331 -> false
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let t11 = unascribe t1 in
      let t21 = unascribe t2 in
      let equal_if uu___172_1351 = if uu___172_1351 then Equal else Unknown in
      let equal_iff uu___173_1356 = if uu___173_1356 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____1370 -> Unknown in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____1375 = FStar_Syntax_Syntax.fv_eq f g in
          equal_if uu____1375
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____1388 = eq_tm f g in
          eq_and uu____1388
            (fun uu____1389  ->
               let uu____1390 = eq_univs_list us vs in equal_if uu____1390)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____1393 = FStar_Const.eq_const c d in equal_iff uu____1393
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1395),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1397)) ->
          let uu____1422 = FStar_Unionfind.equivalent u1 u2 in
          equal_if uu____1422
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____1458 = eq_tm h1 h2 in
          eq_and uu____1458 (fun uu____1459  -> eq_args args1 args2)
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____1462 = eq_univs u v1 in equal_if uu____1462
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1464),uu____1465) ->
          eq_tm t12 t21
      | (uu____1470,FStar_Syntax_Syntax.Tm_meta (t22,uu____1472)) ->
          eq_tm t11 t22
      | uu____1477 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1501)::a11,(b,uu____1504)::b1) ->
          let uu____1542 = eq_tm a b in
          (match uu____1542 with
           | Equal  -> eq_args a11 b1
           | uu____1543 -> Unknown)
      | uu____1544 -> Unknown
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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1558) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1564,uu____1565) ->
        unrefine t2
    | uu____1594 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1598 =
      let uu____1599 = unrefine t in uu____1599.FStar_Syntax_Syntax.n in
    match uu____1598 with
    | FStar_Syntax_Syntax.Tm_type uu____1602 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1605) -> is_unit t1
    | uu____1610 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1614 =
      let uu____1615 = unrefine t in uu____1615.FStar_Syntax_Syntax.n in
    match uu____1614 with
    | FStar_Syntax_Syntax.Tm_type uu____1618 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____1621) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1637) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____1642,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____1654 -> false
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1658 =
      let uu____1659 = FStar_Syntax_Subst.compress e in
      uu____1659.FStar_Syntax_Syntax.n in
    match uu____1658 with
    | FStar_Syntax_Syntax.Tm_abs uu____1662 -> true
    | uu____1677 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1681 =
      let uu____1682 = FStar_Syntax_Subst.compress t in
      uu____1682.FStar_Syntax_Syntax.n in
    match uu____1681 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1685 -> true
    | uu____1693 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1699) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1705,uu____1706) ->
        pre_typ t2
    | uu____1735 -> t1
let destruct:
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list
        Prims.option
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ in
      let uu____1749 =
        let uu____1750 = un_uinst typ1 in uu____1750.FStar_Syntax_Syntax.n in
      match uu____1749 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____1788 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____1804 -> None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (_,lids,_)|FStar_Syntax_Syntax.Sig_bundle
      (_,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ (lid,_,_,_,_,_)
      |FStar_Syntax_Syntax.Sig_effect_abbrev (lid,_,_,_,_)
       |FStar_Syntax_Syntax.Sig_datacon (lid,_,_,_,_,_)
        |FStar_Syntax_Syntax.Sig_declare_typ (lid,_,_)
         |FStar_Syntax_Syntax.Sig_assume (lid,_)
        -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1
      |FStar_Syntax_Syntax.Sig_new_effect n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect _
      |FStar_Syntax_Syntax.Sig_pragma _|FStar_Syntax_Syntax.Sig_main _ -> []
let lid_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.option =
  fun se  ->
    match lids_of_sigelt se with | l::[] -> Some l | uu____1858 -> None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb uu___174_1880 =
  match uu___174_1880 with
  | (FStar_Util.Inl x,uu____1887,uu____1888) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____1892,uu____1893) -> FStar_Ident.range_of_lid l
let range_of_arg uu____1910 =
  match uu____1910 with | (hd1,uu____1916) -> hd1.FStar_Syntax_Syntax.pos
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
      let uu____2030 =
        let uu____2033 =
          let uu____2034 =
            let uu____2039 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            (uu____2039,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app)) in
          FStar_Syntax_Syntax.Tm_meta uu____2034 in
        FStar_Syntax_Syntax.mk uu____2033 in
      uu____2030 None (FStar_Ident.range_of_lid l)
  | uu____2048 ->
      let e =
        let uu____2057 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor) in
        mk_app uu____2057 args in
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
      let uu____2072 =
        let uu____2075 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "7") in
        (uu____2075, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____2072
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
          let uu____2108 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____2108
          then
            let uu____2109 =
              let uu____2112 =
                let uu____2113 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____2113 in
              let uu____2114 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____2112, uu____2114) in
            FStar_Ident.mk_ident uu____2109
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___178_2117 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___178_2117.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___178_2117.FStar_Syntax_Syntax.sort)
          } in
        let uu____2118 = mk_field_projector_name_from_ident lid nm in
        (uu____2118, y)
let set_uvar uv t =
  let uu____2135 = FStar_Unionfind.find uv in
  match uu____2135 with
  | FStar_Syntax_Syntax.Fixed uu____2138 ->
      let uu____2139 =
        let uu____2140 =
          let uu____2141 = FStar_Unionfind.uvar_id uv in
          FStar_All.pipe_left FStar_Util.string_of_int uu____2141 in
        FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2140 in
      failwith uu____2139
  | uu____2143 -> FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed t)
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
         (ns1,f1),FStar_Syntax_Syntax.RecordType (ns2,f2))
        |(FStar_Syntax_Syntax.RecordConstructor
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
      | uu____2190 -> q1 = q2
let abs:
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                   FStar_Syntax_Syntax.cflags Prims.list))
        FStar_Util.either Prims.option -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        let close_lopt lopt1 =
          match lopt1 with
          | None |Some (FStar_Util.Inr _) -> lopt1
          | Some (FStar_Util.Inl lc) ->
              let uu____2265 =
                let uu____2271 = FStar_Syntax_Subst.close_lcomp bs lc in
                FStar_Util.Inl uu____2271 in
              Some uu____2265 in
        match bs with
        | [] -> t
        | uu____2282 ->
            let body =
              let uu____2284 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____2284 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt'),None ) ->
                 let uu____2327 =
                   let uu____2330 =
                     let uu____2331 =
                       let uu____2346 =
                         let uu____2350 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____2350 bs' in
                       let uu____2356 = close_lopt lopt' in
                       (uu____2346, t1, uu____2356) in
                     FStar_Syntax_Syntax.Tm_abs uu____2331 in
                   FStar_Syntax_Syntax.mk uu____2330 in
                 uu____2327 None t1.FStar_Syntax_Syntax.pos
             | uu____2382 ->
                 let uu____2391 =
                   let uu____2394 =
                     let uu____2395 =
                       let uu____2410 = FStar_Syntax_Subst.close_binders bs in
                       let uu____2411 = close_lopt lopt in
                       (uu____2410, body, uu____2411) in
                     FStar_Syntax_Syntax.Tm_abs uu____2395 in
                   FStar_Syntax_Syntax.mk uu____2394 in
                 uu____2391 None t.FStar_Syntax_Syntax.pos)
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
      | uu____2454 ->
          let uu____2458 =
            let uu____2461 =
              let uu____2462 =
                let uu____2470 = FStar_Syntax_Subst.close_binders bs in
                let uu____2471 = FStar_Syntax_Subst.close_comp bs c in
                (uu____2470, uu____2471) in
              FStar_Syntax_Syntax.Tm_arrow uu____2462 in
            FStar_Syntax_Syntax.mk uu____2461 in
          uu____2458 None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____2501 =
        let uu____2502 = FStar_Syntax_Subst.compress t in
        uu____2502.FStar_Syntax_Syntax.n in
      match uu____2501 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2522) ->
               let uu____2529 =
                 let uu____2530 = FStar_Syntax_Subst.compress tres in
                 uu____2530.FStar_Syntax_Syntax.n in
               (match uu____2529 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____2547 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_arrow
                          ((FStar_List.append bs1 bs'), c'))) uu____2547
                      t.FStar_Syntax_Syntax.pos
                | uu____2567 -> t)
           | uu____2568 -> t)
      | uu____2569 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____2578 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
      let uu____2583 =
        let uu____2584 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____2584 t.FStar_Syntax_Syntax.pos in
      let uu____2585 =
        let uu____2588 =
          let uu____2589 =
            let uu____2594 =
              let uu____2595 =
                let uu____2596 = FStar_Syntax_Syntax.mk_binder b in
                [uu____2596] in
              FStar_Syntax_Subst.close uu____2595 t in
            (b, uu____2594) in
          FStar_Syntax_Syntax.Tm_refine uu____2589 in
        FStar_Syntax_Syntax.mk uu____2588 in
      uu____2585 uu____2578 uu____2583
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
        let uu____2634 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____2634 with
         | (bs1,c1) ->
             let uu____2644 = is_tot_or_gtot_comp c1 in
             if uu____2644
             then
               let uu____2650 = arrow_formals_comp (comp_result c1) in
               (match uu____2650 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____2675 ->
        let uu____2676 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2676)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
  =
  fun k  ->
    let uu____2692 = arrow_formals_comp k in
    match uu____2692 with | (bs,c) -> (bs, (comp_result c))
let abs_formals:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.term*
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                   FStar_Syntax_Syntax.cflags Prims.list))
      FStar_Util.either Prims.option)
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | Some (FStar_Util.Inl l1) ->
          let l2 =
            let uu___179_2773 = l1 in
            let uu____2774 =
              FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.res_typ in
            {
              FStar_Syntax_Syntax.eff_name =
                (uu___179_2773.FStar_Syntax_Syntax.eff_name);
              FStar_Syntax_Syntax.res_typ = uu____2774;
              FStar_Syntax_Syntax.cflags =
                (uu___179_2773.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                (fun uu____2777  ->
                   let uu____2778 = l1.FStar_Syntax_Syntax.comp () in
                   FStar_Syntax_Subst.subst_comp s uu____2778)
            } in
          Some (FStar_Util.Inl l2)
      | uu____2787 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____2825 =
        let uu____2826 =
          let uu____2829 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____2829 in
        uu____2826.FStar_Syntax_Syntax.n in
      match uu____2825 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____2867 = aux t2 what in
          (match uu____2867 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____2924 -> ([], t1, abs_body_lcomp) in
    let uu____2936 = aux t None in
    match uu____2936 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____2984 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____2984 with
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
  FStar_Syntax_Syntax.fv Prims.list Prims.option ->
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
                | (None ,_)|(_,[]) -> def
                | (Some fvs,uu____3084) ->
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
            let uu____3145 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____3145 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____3161 ->
            let t' = arrow binders c in
            let uu____3168 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____3168 with
             | (uvs1,t'1) ->
                 let uu____3179 =
                   let uu____3180 = FStar_Syntax_Subst.compress t'1 in
                   uu____3180.FStar_Syntax_Syntax.n in
                 (match uu____3179 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____3206 -> failwith "Impossible"))
let is_tuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.starts_with
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          "Prims.tuple"
    | uu____3221 -> false
let mk_tuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3229 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "tuple%s" uu____3229 in
      let uu____3230 = FStar_Syntax_Const.pconst t in
      FStar_Ident.set_lid_range uu____3230 r
let mk_tuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3238 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mktuple%s" uu____3238 in
      let uu____3239 = FStar_Syntax_Const.pconst t in
      FStar_Ident.set_lid_range uu____3239 r
let is_tuple_data_lid: FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____3246 = mk_tuple_data_lid n1 FStar_Range.dummyRange in
      FStar_Ident.lid_equals f uu____3246
let is_tuple_data_lid': FStar_Ident.lident -> Prims.bool =
  fun f  ->
    (f.FStar_Ident.nsstr = "Prims") &&
      (FStar_Util.starts_with (f.FStar_Ident.ident).FStar_Ident.idText
         "Mktuple")
let is_tuple_constructor_lid: FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    FStar_Util.starts_with (FStar_Ident.text_of_lid lid) "Prims.tuple"
let is_dtuple_constructor_lid: FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    (lid.FStar_Ident.nsstr = "Prims") &&
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         "Prims.dtuple")
let is_dtuple_constructor: FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____3264 -> false
let mk_dtuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3272 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "dtuple%s" uu____3272 in
      let uu____3273 = FStar_Syntax_Const.pconst t in
      FStar_Ident.set_lid_range uu____3273 r
let mk_dtuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3281 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mkdtuple%s" uu____3281 in
      let uu____3282 = FStar_Syntax_Const.pconst t in
      FStar_Ident.set_lid_range uu____3282 r
let is_dtuple_data_lid': FStar_Ident.lident -> Prims.bool =
  fun f  -> FStar_Util.starts_with (FStar_Ident.text_of_lid f) "Mkdtuple"
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
      let uu____3320 =
        let uu____3321 = pre_typ t in uu____3321.FStar_Syntax_Syntax.n in
      match uu____3320 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3329 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3336 =
        let uu____3337 = pre_typ t in uu____3337.FStar_Syntax_Syntax.n in
      match uu____3336 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3340 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____3342) ->
          is_constructed_typ t1 lid
      | uu____3357 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.option =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar _
      |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ -> 
        Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____3368) -> get_tycon t2
    | uu____3383 -> None
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
  fun uu____3413  ->
    let u =
      let uu____3417 = FStar_Unionfind.fresh None in
      FStar_All.pipe_left (fun _0_27  -> FStar_Syntax_Syntax.U_unif _0_27)
        uu____3417 in
    let uu____3423 =
      (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)) None
        FStar_Range.dummyRange in
    (uu____3423, u)
let kt_kt: FStar_Syntax_Syntax.term = FStar_Syntax_Const.kunary ktype0 ktype0
let kt_kt_kt: FStar_Syntax_Syntax.term =
  FStar_Syntax_Const.kbin ktype0 ktype0 ktype0
let fvar_const: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None
let tand: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.and_lid
let tor: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.or_lid
let timp: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.imp_lid
let tiff: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.iff_lid
let t_bool: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.bool_lid
let t_false: FStar_Syntax_Syntax.term =
  fvar_const FStar_Syntax_Const.false_lid
let t_true: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.true_lid
let b2t_v: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.b2t_lid
let t_not: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.not_lid
let mk_conj_opt:
  FStar_Syntax_Syntax.term Prims.option ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | None  -> Some phi2
      | Some phi11 ->
          let uu____3450 =
            let uu____3453 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____3454 =
              let uu____3457 =
                let uu____3458 =
                  let uu____3468 =
                    let uu____3470 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____3471 =
                      let uu____3473 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____3473] in
                    uu____3470 :: uu____3471 in
                  (tand, uu____3468) in
                FStar_Syntax_Syntax.Tm_app uu____3458 in
              FStar_Syntax_Syntax.mk uu____3457 in
            uu____3454 None uu____3453 in
          Some uu____3450
let mk_binop op_t phi1 phi2 =
  let uu____3508 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos in
  let uu____3509 =
    let uu____3512 =
      let uu____3513 =
        let uu____3523 =
          let uu____3525 = FStar_Syntax_Syntax.as_arg phi1 in
          let uu____3526 =
            let uu____3528 = FStar_Syntax_Syntax.as_arg phi2 in [uu____3528] in
          uu____3525 :: uu____3526 in
        (op_t, uu____3523) in
      FStar_Syntax_Syntax.Tm_app uu____3513 in
    FStar_Syntax_Syntax.mk uu____3512 in
  uu____3509 None uu____3508
let mk_neg phi =
  let uu____3549 =
    let uu____3552 =
      let uu____3553 =
        let uu____3563 =
          let uu____3565 = FStar_Syntax_Syntax.as_arg phi in [uu____3565] in
        (t_not, uu____3563) in
      FStar_Syntax_Syntax.Tm_app uu____3553 in
    FStar_Syntax_Syntax.mk uu____3552 in
  uu____3549 None phi.FStar_Syntax_Syntax.pos
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
let mk_imp phi1 phi2 = mk_binop timp phi1 phi2
let mk_iff phi1 phi2 = mk_binop tiff phi1 phi2
let b2t e =
  let uu____3656 =
    let uu____3659 =
      let uu____3660 =
        let uu____3670 =
          let uu____3672 = FStar_Syntax_Syntax.as_arg e in [uu____3672] in
        (b2t_v, uu____3670) in
      FStar_Syntax_Syntax.Tm_app uu____3660 in
    FStar_Syntax_Syntax.mk uu____3659 in
  uu____3656 None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid
let mk_untyped_eq2 e1 e2 =
  let uu____3696 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos in
  let uu____3697 =
    let uu____3700 =
      let uu____3701 =
        let uu____3711 =
          let uu____3713 = FStar_Syntax_Syntax.as_arg e1 in
          let uu____3714 =
            let uu____3716 = FStar_Syntax_Syntax.as_arg e2 in [uu____3716] in
          uu____3713 :: uu____3714 in
        (teq, uu____3711) in
      FStar_Syntax_Syntax.Tm_app uu____3701 in
    FStar_Syntax_Syntax.mk uu____3700 in
  uu____3697 None uu____3696
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
          let uu____3739 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____3740 =
            let uu____3743 =
              let uu____3744 =
                let uu____3754 =
                  let uu____3756 = FStar_Syntax_Syntax.iarg t in
                  let uu____3757 =
                    let uu____3759 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____3760 =
                      let uu____3762 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____3762] in
                    uu____3759 :: uu____3760 in
                  uu____3756 :: uu____3757 in
                (eq_inst, uu____3754) in
              FStar_Syntax_Syntax.Tm_app uu____3744 in
            FStar_Syntax_Syntax.mk uu____3743 in
          uu____3740 None uu____3739
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange in
  let uu____3800 =
    let uu____3803 =
      let uu____3804 =
        let uu____3814 =
          let uu____3816 = FStar_Syntax_Syntax.iarg t in
          let uu____3817 =
            let uu____3819 = FStar_Syntax_Syntax.as_arg x in
            let uu____3820 =
              let uu____3822 = FStar_Syntax_Syntax.as_arg t' in [uu____3822] in
            uu____3819 :: uu____3820 in
          uu____3816 :: uu____3817 in
        (t_has_type1, uu____3814) in
      FStar_Syntax_Syntax.Tm_app uu____3804 in
    FStar_Syntax_Syntax.mk uu____3803 in
  uu____3800 None FStar_Range.dummyRange
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
    let uu____3841 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3848 ->
          (FStar_Syntax_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3855 ->
          (FStar_Syntax_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
    match uu____3841 with
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = ((fun uu____3868  -> c0))
        }
let mk_forall_aux fa x body =
  let uu____3892 =
    let uu____3895 =
      let uu____3896 =
        let uu____3906 =
          let uu____3908 =
            FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
          let uu____3909 =
            let uu____3911 =
              let uu____3912 =
                let uu____3913 =
                  let uu____3914 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____3914] in
                let uu____3915 =
                  let uu____3922 =
                    let uu____3928 =
                      let uu____3929 = FStar_Syntax_Syntax.mk_Total ktype0 in
                      FStar_All.pipe_left lcomp_of_comp uu____3929 in
                    FStar_Util.Inl uu____3928 in
                  Some uu____3922 in
                abs uu____3913 body uu____3915 in
              FStar_Syntax_Syntax.as_arg uu____3912 in
            [uu____3911] in
          uu____3908 :: uu____3909 in
        (fa, uu____3906) in
      FStar_Syntax_Syntax.Tm_app uu____3896 in
    FStar_Syntax_Syntax.mk uu____3895 in
  uu____3892 None FStar_Range.dummyRange
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
             let uu____3979 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____3979 then f1 else mk_forall_no_univ (Prims.fst b) f1)
        bs f
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____3992 -> true
  | uu____3993 -> false
let if_then_else b t1 t2 =
  let then_branch =
    let uu____4036 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos in
    (uu____4036, None, t1) in
  let else_branch =
    let uu____4059 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos in
    (uu____4059, None, t2) in
  let uu____4071 =
    let uu____4072 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4072 in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____4071
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | QEx of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | BaseConn of (FStar_Ident.lident* FStar_Syntax_Syntax.args)
let uu___is_QAll: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____4145 -> false
let __proj__QAll__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____4169 -> false
let __proj__QEx__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____4192 -> false
let __proj__BaseConn__item___0:
  connective -> (FStar_Ident.lident* FStar_Syntax_Syntax.args) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0
let destruct_typ_as_formula:
  FStar_Syntax_Syntax.term -> connective Prims.option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1 in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_monadic _)
        |FStar_Syntax_Syntax.Tm_meta
        (t,FStar_Syntax_Syntax.Meta_monadic_lift _) -> unmeta_monadic t
      | uu____4227 -> f2 in
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
      let aux f2 uu____4272 =
        match uu____4272 with
        | (lid,arity) ->
            let uu____4278 =
              let uu____4288 = unmeta_monadic f2 in head_and_args uu____4288 in
            (match uu____4278 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____4307 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____4307 then Some (BaseConn (lid, args)) else None) in
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____4358 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____4358)
      | uu____4365 ->
          let uu____4366 = FStar_Syntax_Subst.compress t1 in ([], uu____4366) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____4408 = head_and_args t1 in
        match uu____4408 with
        | (t2,args) ->
            let uu____4439 = un_uinst t2 in
            let uu____4440 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____4456  ->
                      match uu____4456 with
                      | (t3,imp) ->
                          let uu____4463 = unascribe t3 in (uu____4463, imp))) in
            (uu____4439, uu____4440) in
      let rec aux qopt out t1 =
        let uu____4486 = let uu____4495 = flat t1 in (qopt, uu____4495) in
        match uu____4486 with
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                 FStar_Syntax_Syntax.vars = _;_},({
                                                    FStar_Syntax_Syntax.n =
                                                      FStar_Syntax_Syntax.Tm_abs
                                                      (b::[],t2,_);
                                                    FStar_Syntax_Syntax.tk =
                                                      _;
                                                    FStar_Syntax_Syntax.pos =
                                                      _;
                                                    FStar_Syntax_Syntax.vars
                                                      = _;_},_)::[]))
          |(Some
            fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                  FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                  FStar_Syntax_Syntax.vars = _;_},_::({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_abs
                                                          (b::[],t2,_);
                                                        FStar_Syntax_Syntax.tk
                                                          = _;
                                                        FStar_Syntax_Syntax.pos
                                                          = _;
                                                        FStar_Syntax_Syntax.vars
                                                          = _;_},_)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
               FStar_Syntax_Syntax.vars = _;_},({
                                                  FStar_Syntax_Syntax.n =
                                                    FStar_Syntax_Syntax.Tm_abs
                                                    (b::[],t2,_);
                                                  FStar_Syntax_Syntax.tk = _;
                                                  FStar_Syntax_Syntax.pos = _;
                                                  FStar_Syntax_Syntax.vars =
                                                    _;_},_)::[]))
          |(None
            ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
                FStar_Syntax_Syntax.vars = _;_},_::({
                                                      FStar_Syntax_Syntax.n =
                                                        FStar_Syntax_Syntax.Tm_abs
                                                        (b::[],t2,_);
                                                      FStar_Syntax_Syntax.tk
                                                        = _;
                                                      FStar_Syntax_Syntax.pos
                                                        = _;
                                                      FStar_Syntax_Syntax.vars
                                                        = _;_},_)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (Some b,uu____4754) ->
            let bs = FStar_List.rev out in
            let uu____4772 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____4772 with
             | (bs1,t2) ->
                 let uu____4778 = patterns t2 in
                 (match uu____4778 with
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs1, pats, body))
                      else Some (QEx (bs1, pats, body))))
        | uu____4816 -> None in
      aux None [] t in
    let phi = unmeta_monadic f in
    let uu____4828 = destruct_base_conn phi in
    match uu____4828 with | Some b -> Some b | None  -> destruct_q_conn phi
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____4839 =
          let uu____4842 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None in
          FStar_Util.Inr uu____4842 in
        let uu____4843 =
          let uu____4844 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____4844 in
        let uu____4847 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn None in
        close_univs_and_mk_letbinding None uu____4839
          a.FStar_Syntax_Syntax.action_univs uu____4843
          FStar_Syntax_Const.effect_Tot_lid uu____4847 in
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
  let uu____4880 =
    let uu____4883 =
      let uu____4884 =
        let uu____4894 =
          let uu____4896 = FStar_Syntax_Syntax.as_arg t in [uu____4896] in
        (reify_, uu____4894) in
      FStar_Syntax_Syntax.Tm_app uu____4884 in
    FStar_Syntax_Syntax.mk uu____4883 in
  uu____4880 None t.FStar_Syntax_Syntax.pos
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____4912 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar _
      |FStar_Syntax_Syntax.Tm_name _
       |FStar_Syntax_Syntax.Tm_match _
        |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type _
      |FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_arrow _ ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,_)
      |FStar_Syntax_Syntax.Tm_refine
       ({ FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t2;_},_)
       |FStar_Syntax_Syntax.Tm_meta (t2,_)
        |FStar_Syntax_Syntax.Tm_ascribed (t2,_,_)
         |FStar_Syntax_Syntax.Tm_app (t2,_)
          |FStar_Syntax_Syntax.Tm_abs (_,t2,_)|FStar_Syntax_Syntax.Tm_let
           (_,t2)
        -> delta_qualifier t2
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
  fun t  -> let uu____5018 = delta_qualifier t in incr_delta_depth uu____5018
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____5022 =
      let uu____5023 = FStar_Syntax_Subst.compress t in
      uu____5023.FStar_Syntax_Syntax.n in
    match uu____5022 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5026 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list Prims.option
  =
  fun e  ->
    let uu____5034 = let uu____5044 = unmeta e in head_and_args uu____5044 in
    match uu____5034 with
    | (head1,args) ->
        let uu____5063 =
          let uu____5071 =
            let uu____5072 = un_uinst head1 in
            uu____5072.FStar_Syntax_Syntax.n in
          (uu____5071, args) in
        (match uu____5063 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5083) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____5096::(hd1,uu____5098)::(tl1,uu____5100)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____5134 =
               let uu____5138 =
                 let uu____5142 = list_elements tl1 in
                 FStar_Util.must uu____5142 in
               hd1 :: uu____5138 in
             Some uu____5134
         | uu____5151 -> None)
let rec apply_last f l =
  match l with
  | [] -> failwith "apply_last: got empty list"
  | a::[] -> let uu____5182 = f a in [uu____5182]
  | x::xs -> let uu____5186 = apply_last f xs in x :: uu____5186
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
          let uu____5216 =
            let uu____5219 =
              let uu____5220 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____5220 in
            FStar_Syntax_Syntax.mk uu____5219 in
          uu____5216 None rng in
        let cons1 args pos =
          let uu____5238 =
            let uu____5239 =
              let uu____5240 = ctor FStar_Syntax_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5240
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5239 args in
          uu____5238 None pos in
        let nil args pos =
          let uu____5254 =
            let uu____5255 =
              let uu____5256 = ctor FStar_Syntax_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5256
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5255 args in
          uu____5254 None pos in
        let uu____5261 =
          let uu____5262 =
            let uu____5263 = FStar_Syntax_Syntax.iarg typ in [uu____5263] in
          nil uu____5262 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____5266 =
                 let uu____5267 = FStar_Syntax_Syntax.iarg typ in
                 let uu____5268 =
                   let uu____5270 = FStar_Syntax_Syntax.as_arg t in
                   let uu____5271 =
                     let uu____5273 = FStar_Syntax_Syntax.as_arg a in
                     [uu____5273] in
                   uu____5270 :: uu____5271 in
                 uu____5267 :: uu____5268 in
               cons1 uu____5266 t.FStar_Syntax_Syntax.pos) l uu____5261
let rec eqlist eq1 xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
  | uu____5317 -> false
let eqsum e1 e2 x y =
  match (x, y) with
  | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
  | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
  | uu____5390 -> false
let eqprod e1 e2 x y =
  match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt e x y =
  match (x, y) with | (Some x1,Some y1) -> e x1 y1 | uu____5498 -> false
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
        | FStar_Syntax_Syntax.Tm_app uu____5611 ->
            let uu____5621 = head_and_args' t in
            (match uu____5621 with
             | (hd1,args) ->
                 let uu___180_5643 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.tk =
                     (uu___180_5643.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___180_5643.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___180_5643.FStar_Syntax_Syntax.vars)
                 })
        | uu____5655 -> t in
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_bvar x,FStar_Syntax_Syntax.Tm_bvar y) ->
          x.FStar_Syntax_Syntax.index = y.FStar_Syntax_Syntax.index
      | (FStar_Syntax_Syntax.Tm_name x,FStar_Syntax_Syntax.Tm_name y) ->
          FStar_Syntax_Syntax.bv_eq x y
      | (FStar_Syntax_Syntax.Tm_fvar x,FStar_Syntax_Syntax.Tm_fvar y) ->
          FStar_Syntax_Syntax.fv_eq x y
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
      | (uu____5864,uu____5865) -> false
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
      | (uu____5938,uu____5939) -> false
and eq_flags:
  FStar_Syntax_Syntax.cflags Prims.list ->
    FStar_Syntax_Syntax.cflags Prims.list -> Prims.bool
  = fun f1  -> fun f2  -> false
and branch_eq:
  ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.withinfo_t*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax Prims.option*
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    ((FStar_Syntax_Syntax.pat',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.withinfo_t*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax Prims.option*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) -> Prims.bool
  =
  fun uu____5944  ->
    fun uu____5945  ->
      match (uu____5944, uu____5945) with | ((p1,w1,t1),(p2,w2,t2)) -> false
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
        let uu____6055 = FStar_Syntax_Subst.compress t in
        uu____6055.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____6075 =
              let uu____6085 = ff f1 in
              let uu____6086 =
                FStar_List.map
                  (fun uu____6094  ->
                     match uu____6094 with
                     | (a,q) -> let uu____6101 = ff a in (uu____6101, q))
                  args in
              (uu____6085, uu____6086) in
            FStar_Syntax_Syntax.Tm_app uu____6075
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____6130 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____6130 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____6136 =
                   let uu____6151 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____6151, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____6136)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____6176 = let uu____6181 = ff t1 in (uu____6181, us) in
            FStar_Syntax_Syntax.Tm_uinst uu____6176
        | uu____6182 -> tn in
      f
        (let uu___181_6183 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.tk = (uu___181_6183.FStar_Syntax_Syntax.tk);
           FStar_Syntax_Syntax.pos = (uu___181_6183.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___181_6183.FStar_Syntax_Syntax.vars)
         })
let rec sizeof: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6191 ->
        let uu____6212 =
          let uu____6213 = FStar_Syntax_Subst.compress t in sizeof uu____6213 in
        (Prims.parse_int "1") + uu____6212
    | FStar_Syntax_Syntax.Tm_bvar bv|FStar_Syntax_Syntax.Tm_name bv ->
        let uu____6215 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____6215
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____6222 = sizeof t1 in (FStar_List.length us) + uu____6222
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____6228) ->
        let uu____6251 = sizeof t1 in
        let uu____6252 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____6256  ->
                 match uu____6256 with
                 | (bv,uu____6260) ->
                     let uu____6261 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____6261) (Prims.parse_int "0") bs in
        uu____6251 + uu____6252
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____6278 = sizeof hd1 in
        let uu____6279 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____6283  ->
                 match uu____6283 with
                 | (arg,uu____6287) ->
                     let uu____6288 = sizeof arg in acc + uu____6288)
            (Prims.parse_int "0") args in
        uu____6278 + uu____6279
    | uu____6289 -> Prims.parse_int "1"