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
                      (fst b).FStar_Syntax_Syntax.sort in
                  (uu____96, (snd b)) in
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
                  FStar_All.pipe_left FStar_Pervasives.fst uu____240 in
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
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____384) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____390,uu____391) -> unmeta e2
    | uu____420 -> e1
let rec univ_kernel:
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe* Prims.int) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____428 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____429 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____433 = univ_kernel u1 in
        (match uu____433 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____440 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____444 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let constant_univ_as_nat: FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  -> let uu____450 = univ_kernel u in snd uu____450
let rec compare_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____459,uu____460) ->
          failwith "Impossible: compare_univs"
      | (uu____461,FStar_Syntax_Syntax.U_bvar uu____462) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_unknown ,uu____463) -> - (Prims.parse_int "1")
      | (uu____464,FStar_Syntax_Syntax.U_unknown ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_zero ,uu____465) -> - (Prims.parse_int "1")
      | (uu____466,FStar_Syntax_Syntax.U_zero ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____469,FStar_Syntax_Syntax.U_unif
         uu____470) -> - (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____473,FStar_Syntax_Syntax.U_name
         uu____474) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____483 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
          let uu____484 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
          uu____483 - uu____484
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1 in
          let n2 = FStar_List.length us2 in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____505 = FStar_List.zip us1 us2 in
               FStar_Util.find_map uu____505
                 (fun uu____511  ->
                    match uu____511 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21 in
                        if c <> (Prims.parse_int "0") then Some c else None) in
             match copt with | None  -> Prims.parse_int "0" | Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____521,uu____522) ->
          - (Prims.parse_int "1")
      | (uu____524,FStar_Syntax_Syntax.U_max uu____525) ->
          Prims.parse_int "1"
      | uu____527 ->
          let uu____530 = univ_kernel u1 in
          (match uu____530 with
           | (k1,n1) ->
               let uu____535 = univ_kernel u2 in
               (match uu____535 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2 in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
let eq_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____548 = compare_univs u1 u2 in
      uu____548 = (Prims.parse_int "0")
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
  | FStar_Syntax_Syntax.Total uu____575 -> FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.GTotal uu____581 ->
      FStar_Syntax_Const.effect_GTot_lid
let comp_flags c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____599 -> [FStar_Syntax_Syntax.TOTAL]
  | FStar_Syntax_Syntax.GTotal uu____605 -> [FStar_Syntax_Syntax.SOMETRIVIAL]
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
            let uu____635 =
              let uu____636 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____636 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____635;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____654 =
              let uu____655 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____655 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____654;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            } in
      let uu___174_665 = c in
      let uu____666 =
        let uu____667 =
          let uu___175_668 = comp_to_comp_typ c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___175_668.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___175_668.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___175_668.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___175_668.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____667 in
      {
        FStar_Syntax_Syntax.n = uu____666;
        FStar_Syntax_Syntax.tk = (uu___174_665.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___174_665.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___174_665.FStar_Syntax_Syntax.vars)
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
    | uu____699 ->
        failwith "Assertion failed: Computation type without universe"
let is_named_tot c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
        FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.Total uu____712 -> true
  | FStar_Syntax_Syntax.GTotal uu____718 -> false
let is_total_comp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___162_736  ->
          match uu___162_736 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____737 -> false))
let is_total_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Syntax_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___163_742  ->
               match uu___163_742 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____743 -> false)))
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
            (fun uu___164_748  ->
               match uu___164_748 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____749 -> false)))
let is_partial_return c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___165_762  ->
          match uu___165_762 with
          | FStar_Syntax_Syntax.RETURN  -> true
          | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
          | uu____763 -> false))
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___166_768  ->
            match uu___166_768 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____769 -> false))
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
  | FStar_Syntax_Syntax.Total uu____795 -> true
  | FStar_Syntax_Syntax.GTotal uu____801 -> false
  | FStar_Syntax_Syntax.Comp ct ->
      ((is_total_comp c) ||
         (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
        ||
        (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___167_809  ->
                 match uu___167_809 with
                 | FStar_Syntax_Syntax.LEMMA  -> true
                 | uu____810 -> false)))
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
            (fun uu___168_829  ->
               match uu___168_829 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____830 -> false)))
let is_pure_or_ghost_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
let is_pure_or_ghost_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____837 =
      let uu____838 = FStar_Syntax_Subst.compress t in
      uu____838.FStar_Syntax_Syntax.n in
    match uu____837 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____841,c) -> is_pure_or_ghost_comp c
    | uu____853 -> true
let is_lemma_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Syntax_Const.effect_Lemma_lid
  | uu____866 -> false
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____870 =
      let uu____871 = FStar_Syntax_Subst.compress t in
      uu____871.FStar_Syntax_Syntax.n in
    match uu____870 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____874,c) -> is_lemma_comp c
    | uu____886 -> false
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
    | uu____932 -> (t1, [])
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
        let uu____976 = head_and_args' head1 in
        (match uu____976 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1012 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1027) ->
        FStar_Syntax_Subst.compress t2
    | uu____1032 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1036 =
      let uu____1037 = FStar_Syntax_Subst.compress t in
      uu____1037.FStar_Syntax_Syntax.n in
    match uu____1036 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1040,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1056)::uu____1057 ->
                  let pats' = unmeta pats in
                  let uu____1088 = head_and_args pats' in
                  (match uu____1088 with
                   | (head1,uu____1099) ->
                       let uu____1114 =
                         let uu____1115 = un_uinst head1 in
                         uu____1115.FStar_Syntax_Syntax.n in
                       (match uu____1114 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.cons_lid
                        | uu____1119 -> false))
              | uu____1120 -> false)
         | uu____1126 -> false)
    | uu____1127 -> false
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
         FStar_Syntax_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___169_1141  ->
                 match uu___169_1141 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____1142 -> false)))
  | uu____1143 -> false
let comp_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____1158) -> t
  | FStar_Syntax_Syntax.GTotal (t,uu____1166) -> t
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let set_result_typ c t =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____1190 -> FStar_Syntax_Syntax.mk_Total t
  | FStar_Syntax_Syntax.GTotal uu____1196 -> FStar_Syntax_Syntax.mk_GTotal t
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Syntax_Syntax.mk_Comp
        (let uu___176_1203 = ct in
         {
           FStar_Syntax_Syntax.comp_univs =
             (uu___176_1203.FStar_Syntax_Syntax.comp_univs);
           FStar_Syntax_Syntax.effect_name =
             (uu___176_1203.FStar_Syntax_Syntax.effect_name);
           FStar_Syntax_Syntax.result_typ = t;
           FStar_Syntax_Syntax.effect_args =
             (uu___176_1203.FStar_Syntax_Syntax.effect_args);
           FStar_Syntax_Syntax.flags =
             (uu___176_1203.FStar_Syntax_Syntax.flags)
         })
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___170_1216  ->
          match uu___170_1216 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____1217 -> false))
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
  | uu____1239 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1245,uu____1246) ->
        unascribe e2
    | uu____1275 -> e1
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1317,uu____1318) ->
      ascribe t' k
  | uu____1347 ->
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (t, k, None))
        None t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal
  | NotEqual
  | Unknown
let uu___is_Equal: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1369 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1373 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1377 -> false
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let t11 = unascribe t1 in
      let t21 = unascribe t2 in
      let equal_if uu___171_1397 = if uu___171_1397 then Equal else Unknown in
      let equal_iff uu___172_1402 = if uu___172_1402 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____1416 -> Unknown in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____1421 = FStar_Syntax_Syntax.fv_eq f g in
          equal_if uu____1421
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____1434 = eq_tm f g in
          eq_and uu____1434
            (fun uu____1435  ->
               let uu____1436 = eq_univs_list us vs in equal_if uu____1436)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____1439 = FStar_Const.eq_const c d in equal_iff uu____1439
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1441),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1443)) ->
          let uu____1468 = FStar_Syntax_Unionfind.equiv u1 u2 in
          equal_if uu____1468
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____1501 = eq_tm h1 h2 in
          eq_and uu____1501 (fun uu____1502  -> eq_args args1 args2)
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____1505 = eq_univs u v1 in equal_if uu____1505
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1507),uu____1508) ->
          eq_tm t12 t21
      | (uu____1513,FStar_Syntax_Syntax.Tm_meta (t22,uu____1515)) ->
          eq_tm t11 t22
      | uu____1520 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1544)::a11,(b,uu____1547)::b1) ->
          let uu____1585 = eq_tm a b in
          (match uu____1585 with
           | Equal  -> eq_args a11 b1
           | uu____1586 -> Unknown)
      | uu____1587 -> Unknown
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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1601) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1607,uu____1608) ->
        unrefine t2
    | uu____1637 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1641 =
      let uu____1642 = unrefine t in uu____1642.FStar_Syntax_Syntax.n in
    match uu____1641 with
    | FStar_Syntax_Syntax.Tm_type uu____1645 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1648) -> is_unit t1
    | uu____1653 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1657 =
      let uu____1658 = unrefine t in uu____1658.FStar_Syntax_Syntax.n in
    match uu____1657 with
    | FStar_Syntax_Syntax.Tm_type uu____1661 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____1664) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1680) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____1685,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____1697 -> false
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1701 =
      let uu____1702 = FStar_Syntax_Subst.compress e in
      uu____1702.FStar_Syntax_Syntax.n in
    match uu____1701 with
    | FStar_Syntax_Syntax.Tm_abs uu____1705 -> true
    | uu____1720 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1724 =
      let uu____1725 = FStar_Syntax_Subst.compress t in
      uu____1725.FStar_Syntax_Syntax.n in
    match uu____1724 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1728 -> true
    | uu____1736 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1742) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1748,uu____1749) ->
        pre_typ t2
    | uu____1778 -> t1
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
      let uu____1792 =
        let uu____1793 = un_uinst typ1 in uu____1793.FStar_Syntax_Syntax.n in
      match uu____1792 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____1831 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____1847 -> None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____1858,lids,uu____1860) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____1865,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____1872,uu____1873,uu____1874,uu____1875,uu____1876) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____1882,uu____1883,uu____1884,uu____1885) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____1889,uu____1890,uu____1891,uu____1892,uu____1893) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1897,uu____1898) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____1900) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____1903 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____1904 -> []
    | FStar_Syntax_Syntax.Sig_main uu____1905 -> []
let lid_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident option =
  fun se  ->
    match lids_of_sigelt se with | l::[] -> Some l | uu____1913 -> None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb uu___173_1935 =
  match uu___173_1935 with
  | (FStar_Util.Inl x,uu____1942,uu____1943) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____1947,uu____1948) -> FStar_Ident.range_of_lid l
let range_of_arg uu____1965 =
  match uu____1965 with | (hd1,uu____1971) -> hd1.FStar_Syntax_Syntax.pos
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
      let uu____2085 =
        let uu____2088 =
          let uu____2089 =
            let uu____2094 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            (uu____2094,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app)) in
          FStar_Syntax_Syntax.Tm_meta uu____2089 in
        FStar_Syntax_Syntax.mk uu____2088 in
      uu____2085 None (FStar_Ident.range_of_lid l)
  | uu____2103 ->
      let e =
        let uu____2112 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor) in
        mk_app uu____2112 args in
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
      let uu____2127 =
        let uu____2130 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "7") in
        (uu____2130, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____2127
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
          let uu____2163 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____2163
          then
            let uu____2164 =
              let uu____2167 =
                let uu____2168 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____2168 in
              let uu____2169 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____2167, uu____2169) in
            FStar_Ident.mk_ident uu____2164
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___177_2172 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___177_2172.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___177_2172.FStar_Syntax_Syntax.sort)
          } in
        let uu____2173 = mk_field_projector_name_from_ident lid nm in
        (uu____2173, y)
let set_uvar:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____2180 = FStar_Syntax_Unionfind.find uv in
      match uu____2180 with
      | Some uu____2182 ->
          let uu____2183 =
            let uu____2184 =
              let uu____2185 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____2185 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2184 in
          failwith uu____2183
      | uu____2186 -> FStar_Syntax_Unionfind.change uv t
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
      | uu____2248 -> q1 = q2
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
          | Some (FStar_Util.Inr uu____2305) -> lopt1
          | Some (FStar_Util.Inl lc) ->
              let uu____2326 =
                let uu____2332 = FStar_Syntax_Subst.close_lcomp bs lc in
                FStar_Util.Inl uu____2332 in
              Some uu____2326 in
        match bs with
        | [] -> t
        | uu____2343 ->
            let body =
              let uu____2345 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____2345 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt'),None ) ->
                 let uu____2388 =
                   let uu____2391 =
                     let uu____2392 =
                       let uu____2407 =
                         let uu____2411 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____2411 bs' in
                       let uu____2417 = close_lopt lopt' in
                       (uu____2407, t1, uu____2417) in
                     FStar_Syntax_Syntax.Tm_abs uu____2392 in
                   FStar_Syntax_Syntax.mk uu____2391 in
                 uu____2388 None t1.FStar_Syntax_Syntax.pos
             | uu____2443 ->
                 let uu____2452 =
                   let uu____2455 =
                     let uu____2456 =
                       let uu____2471 = FStar_Syntax_Subst.close_binders bs in
                       let uu____2472 = close_lopt lopt in
                       (uu____2471, body, uu____2472) in
                     FStar_Syntax_Syntax.Tm_abs uu____2456 in
                   FStar_Syntax_Syntax.mk uu____2455 in
                 uu____2452 None t.FStar_Syntax_Syntax.pos)
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
      | uu____2515 ->
          let uu____2519 =
            let uu____2522 =
              let uu____2523 =
                let uu____2531 = FStar_Syntax_Subst.close_binders bs in
                let uu____2532 = FStar_Syntax_Subst.close_comp bs c in
                (uu____2531, uu____2532) in
              FStar_Syntax_Syntax.Tm_arrow uu____2523 in
            FStar_Syntax_Syntax.mk uu____2522 in
          uu____2519 None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____2562 =
        let uu____2563 = FStar_Syntax_Subst.compress t in
        uu____2563.FStar_Syntax_Syntax.n in
      match uu____2562 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2583) ->
               let uu____2590 =
                 let uu____2591 = FStar_Syntax_Subst.compress tres in
                 uu____2591.FStar_Syntax_Syntax.n in
               (match uu____2590 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____2608 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c')) uu____2608
                      t.FStar_Syntax_Syntax.pos
                | uu____2624 -> t)
           | uu____2625 -> t)
      | uu____2626 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____2635 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
      let uu____2640 =
        let uu____2641 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____2641 t.FStar_Syntax_Syntax.pos in
      let uu____2642 =
        let uu____2645 =
          let uu____2646 =
            let uu____2651 =
              let uu____2652 =
                let uu____2653 = FStar_Syntax_Syntax.mk_binder b in
                [uu____2653] in
              FStar_Syntax_Subst.close uu____2652 t in
            (b, uu____2651) in
          FStar_Syntax_Syntax.Tm_refine uu____2646 in
        FStar_Syntax_Syntax.mk uu____2645 in
      uu____2642 uu____2635 uu____2640
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
        let uu____2691 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____2691 with
         | (bs1,c1) ->
             let uu____2701 = is_tot_or_gtot_comp c1 in
             if uu____2701
             then
               let uu____2707 = arrow_formals_comp (comp_result c1) in
               (match uu____2707 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____2732 ->
        let uu____2733 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2733)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
  =
  fun k  ->
    let uu____2749 = arrow_formals_comp k in
    match uu____2749 with | (bs,c) -> (bs, (comp_result c))
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
            let uu___178_2830 = l1 in
            let uu____2831 =
              FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.res_typ in
            {
              FStar_Syntax_Syntax.eff_name =
                (uu___178_2830.FStar_Syntax_Syntax.eff_name);
              FStar_Syntax_Syntax.res_typ = uu____2831;
              FStar_Syntax_Syntax.cflags =
                (uu___178_2830.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                (fun uu____2834  ->
                   let uu____2835 = l1.FStar_Syntax_Syntax.comp () in
                   FStar_Syntax_Subst.subst_comp s uu____2835)
            } in
          Some (FStar_Util.Inl l2)
      | uu____2844 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____2882 =
        let uu____2883 =
          let uu____2886 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____2886 in
        uu____2883.FStar_Syntax_Syntax.n in
      match uu____2882 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____2924 = aux t2 what in
          (match uu____2924 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____2981 -> ([], t1, abs_body_lcomp) in
    let uu____2993 = aux t None in
    match uu____2993 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____3041 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____3041 with
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
                | (None ,uu____3131) -> def
                | (uu____3137,[]) -> def
                | (Some fvs,uu____3144) ->
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
            let uu____3205 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____3205 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____3221 ->
            let t' = arrow binders c in
            let uu____3228 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____3228 with
             | (uvs1,t'1) ->
                 let uu____3239 =
                   let uu____3240 = FStar_Syntax_Subst.compress t'1 in
                   uu____3240.FStar_Syntax_Syntax.n in
                 (match uu____3239 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____3266 -> failwith "Impossible"))
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
    | uu____3303 -> false
let mk_tuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3311 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "tuple%s" uu____3311 in
      let uu____3312 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3312 r
let mk_tuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3320 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mktuple%s" uu____3320 in
      let uu____3321 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3321 r
let is_tuple_data_lid: FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____3328 = mk_tuple_data_lid n1 FStar_Range.dummyRange in
      FStar_Ident.lid_equals f uu____3328
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
    | uu____3346 -> false
let mk_dtuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3354 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "dtuple%s" uu____3354 in
      let uu____3355 = let uu____3356 = mod_prefix_dtuple n1 in uu____3356 t in
      FStar_Ident.set_lid_range uu____3355 r
let mk_dtuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3366 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mkdtuple%s" uu____3366 in
      let uu____3367 = let uu____3368 = mod_prefix_dtuple n1 in uu____3368 t in
      FStar_Ident.set_lid_range uu____3367 r
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
      let uu____3408 =
        let uu____3409 = pre_typ t in uu____3409.FStar_Syntax_Syntax.n in
      match uu____3408 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3417 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3424 =
        let uu____3425 = pre_typ t in uu____3425.FStar_Syntax_Syntax.n in
      match uu____3424 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3428 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____3430) ->
          is_constructed_typ t1 lid
      | uu____3445 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term option =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____3452 -> Some t1
    | FStar_Syntax_Syntax.Tm_name uu____3453 -> Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____3454 -> Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____3456) -> get_tycon t2
    | uu____3471 -> None
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
  fun uu____3501  ->
    let u =
      let uu____3505 = FStar_Syntax_Unionfind.univ_fresh () in
      FStar_All.pipe_left (fun _0_27  -> FStar_Syntax_Syntax.U_unif _0_27)
        uu____3505 in
    let uu____3510 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u) None
        FStar_Range.dummyRange in
    (uu____3510, u)
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
          let uu____3533 =
            let uu____3536 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____3537 =
              let uu____3540 =
                let uu____3541 =
                  let uu____3551 =
                    let uu____3553 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____3554 =
                      let uu____3556 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____3556] in
                    uu____3553 :: uu____3554 in
                  (tand, uu____3551) in
                FStar_Syntax_Syntax.Tm_app uu____3541 in
              FStar_Syntax_Syntax.mk uu____3540 in
            uu____3537 None uu____3536 in
          Some uu____3533
let mk_binop op_t phi1 phi2 =
  let uu____3591 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos in
  let uu____3592 =
    let uu____3595 =
      let uu____3596 =
        let uu____3606 =
          let uu____3608 = FStar_Syntax_Syntax.as_arg phi1 in
          let uu____3609 =
            let uu____3611 = FStar_Syntax_Syntax.as_arg phi2 in [uu____3611] in
          uu____3608 :: uu____3609 in
        (op_t, uu____3606) in
      FStar_Syntax_Syntax.Tm_app uu____3596 in
    FStar_Syntax_Syntax.mk uu____3595 in
  uu____3592 None uu____3591
let mk_neg phi =
  let uu____3632 =
    let uu____3635 =
      let uu____3636 =
        let uu____3646 =
          let uu____3648 = FStar_Syntax_Syntax.as_arg phi in [uu____3648] in
        (t_not, uu____3646) in
      FStar_Syntax_Syntax.Tm_app uu____3636 in
    FStar_Syntax_Syntax.mk uu____3635 in
  uu____3632 None phi.FStar_Syntax_Syntax.pos
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
  let uu____3739 =
    let uu____3742 =
      let uu____3743 =
        let uu____3753 =
          let uu____3755 = FStar_Syntax_Syntax.as_arg e in [uu____3755] in
        (b2t_v, uu____3753) in
      FStar_Syntax_Syntax.Tm_app uu____3743 in
    FStar_Syntax_Syntax.mk uu____3742 in
  uu____3739 None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid
let mk_untyped_eq2 e1 e2 =
  let uu____3779 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos in
  let uu____3780 =
    let uu____3783 =
      let uu____3784 =
        let uu____3794 =
          let uu____3796 = FStar_Syntax_Syntax.as_arg e1 in
          let uu____3797 =
            let uu____3799 = FStar_Syntax_Syntax.as_arg e2 in [uu____3799] in
          uu____3796 :: uu____3797 in
        (teq, uu____3794) in
      FStar_Syntax_Syntax.Tm_app uu____3784 in
    FStar_Syntax_Syntax.mk uu____3783 in
  uu____3780 None uu____3779
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
          let uu____3822 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____3823 =
            let uu____3826 =
              let uu____3827 =
                let uu____3837 =
                  let uu____3839 = FStar_Syntax_Syntax.iarg t in
                  let uu____3840 =
                    let uu____3842 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____3843 =
                      let uu____3845 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____3845] in
                    uu____3842 :: uu____3843 in
                  uu____3839 :: uu____3840 in
                (eq_inst, uu____3837) in
              FStar_Syntax_Syntax.Tm_app uu____3827 in
            FStar_Syntax_Syntax.mk uu____3826 in
          uu____3823 None uu____3822
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange in
  let uu____3883 =
    let uu____3886 =
      let uu____3887 =
        let uu____3897 =
          let uu____3899 = FStar_Syntax_Syntax.iarg t in
          let uu____3900 =
            let uu____3902 = FStar_Syntax_Syntax.as_arg x in
            let uu____3903 =
              let uu____3905 = FStar_Syntax_Syntax.as_arg t' in [uu____3905] in
            uu____3902 :: uu____3903 in
          uu____3899 :: uu____3900 in
        (t_has_type1, uu____3897) in
      FStar_Syntax_Syntax.Tm_app uu____3887 in
    FStar_Syntax_Syntax.mk uu____3886 in
  uu____3883 None FStar_Range.dummyRange
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
    let uu____3924 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3931 ->
          (FStar_Syntax_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3938 ->
          (FStar_Syntax_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
    match uu____3924 with
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = ((fun uu____3951  -> c0))
        }
let mk_forall_aux fa x body =
  let uu____3975 =
    let uu____3978 =
      let uu____3979 =
        let uu____3989 =
          let uu____3991 =
            FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
          let uu____3992 =
            let uu____3994 =
              let uu____3995 =
                let uu____3996 =
                  let uu____3997 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____3997] in
                let uu____3998 =
                  let uu____4005 =
                    let uu____4011 =
                      let uu____4012 = FStar_Syntax_Syntax.mk_Total ktype0 in
                      FStar_All.pipe_left lcomp_of_comp uu____4012 in
                    FStar_Util.Inl uu____4011 in
                  Some uu____4005 in
                abs uu____3996 body uu____3998 in
              FStar_Syntax_Syntax.as_arg uu____3995 in
            [uu____3994] in
          uu____3991 :: uu____3992 in
        (fa, uu____3989) in
      FStar_Syntax_Syntax.Tm_app uu____3979 in
    FStar_Syntax_Syntax.mk uu____3978 in
  uu____3975 None FStar_Range.dummyRange
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
             let uu____4062 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____4062 then f1 else mk_forall_no_univ (fst b) f1) bs f
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____4075 -> true
  | uu____4076 -> false
let if_then_else b t1 t2 =
  let then_branch =
    let uu____4119 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos in
    (uu____4119, None, t1) in
  let else_branch =
    let uu____4142 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos in
    (uu____4142, None, t2) in
  let uu____4154 =
    let uu____4155 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4155 in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____4154
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | QEx of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | BaseConn of (FStar_Ident.lident* FStar_Syntax_Syntax.args)
let uu___is_QAll: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____4231 -> false
let __proj__QAll__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____4255 -> false
let __proj__QEx__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____4278 -> false
let __proj__BaseConn__item___0:
  connective -> (FStar_Ident.lident* FStar_Syntax_Syntax.args) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0
let destruct_typ_as_formula: FStar_Syntax_Syntax.term -> connective option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1 in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____4303) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____4313) ->
          unmeta_monadic t
      | uu____4323 -> f2 in
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
      let aux f2 uu____4368 =
        match uu____4368 with
        | (lid,arity) ->
            let uu____4374 =
              let uu____4384 = unmeta_monadic f2 in head_and_args uu____4384 in
            (match uu____4374 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____4403 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____4403 then Some (BaseConn (lid, args)) else None) in
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____4454 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____4454)
      | uu____4461 ->
          let uu____4462 = FStar_Syntax_Subst.compress t1 in ([], uu____4462) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____4504 = head_and_args t1 in
        match uu____4504 with
        | (t2,args) ->
            let uu____4535 = un_uinst t2 in
            let uu____4536 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____4552  ->
                      match uu____4552 with
                      | (t3,imp) ->
                          let uu____4559 = unascribe t3 in (uu____4559, imp))) in
            (uu____4535, uu____4536) in
      let rec aux qopt out t1 =
        let uu____4582 = let uu____4591 = flat t1 in (qopt, uu____4591) in
        match uu____4582 with
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____4606;
                 FStar_Syntax_Syntax.pos = uu____4607;
                 FStar_Syntax_Syntax.vars = uu____4608;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____4611);
                                                             FStar_Syntax_Syntax.tk
                                                               = uu____4612;
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____4613;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____4614;_},uu____4615)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____4676;
                 FStar_Syntax_Syntax.pos = uu____4677;
                 FStar_Syntax_Syntax.vars = uu____4678;_},uu____4679::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____4682);
                  FStar_Syntax_Syntax.tk = uu____4683;
                  FStar_Syntax_Syntax.pos = uu____4684;
                  FStar_Syntax_Syntax.vars = uu____4685;_},uu____4686)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____4754;
               FStar_Syntax_Syntax.pos = uu____4755;
               FStar_Syntax_Syntax.vars = uu____4756;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____4759);
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____4760;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____4761;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____4762;_},uu____4763)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____4831;
               FStar_Syntax_Syntax.pos = uu____4832;
               FStar_Syntax_Syntax.vars = uu____4833;_},uu____4834::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____4837);
                                                                    FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____4838;
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____4839;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____4840;_},uu____4841)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (Some b,uu____4917) ->
            let bs = FStar_List.rev out in
            let uu____4935 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____4935 with
             | (bs1,t2) ->
                 let uu____4941 = patterns t2 in
                 (match uu____4941 with
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs1, pats, body))
                      else Some (QEx (bs1, pats, body))))
        | uu____4979 -> None in
      aux None [] t in
    let phi = unmeta_monadic f in
    let uu____4991 = destruct_base_conn phi in
    match uu____4991 with | Some b -> Some b | None  -> destruct_q_conn phi
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____5002 =
          let uu____5005 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None in
          FStar_Util.Inr uu____5005 in
        let uu____5006 =
          let uu____5007 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____5007 in
        let uu____5010 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn None in
        close_univs_and_mk_letbinding None uu____5002
          a.FStar_Syntax_Syntax.action_univs uu____5006
          FStar_Syntax_Const.effect_Tot_lid uu____5010 in
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
  let uu____5043 =
    let uu____5046 =
      let uu____5047 =
        let uu____5057 =
          let uu____5059 = FStar_Syntax_Syntax.as_arg t in [uu____5059] in
        (reify_, uu____5057) in
      FStar_Syntax_Syntax.Tm_app uu____5047 in
    FStar_Syntax_Syntax.mk uu____5046 in
  uu____5043 None t.FStar_Syntax_Syntax.pos
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____5075 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____5097 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____5098 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____5099 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____5115 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____5124 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____5125 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____5126 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5135) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____5140;
           FStar_Syntax_Syntax.index = uu____5141;
           FStar_Syntax_Syntax.sort = t2;_},uu____5143)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____5151) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5157,uu____5158) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5188) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____5203,t2,uu____5205) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____5228,t2) -> delta_qualifier t2
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
  fun t  -> let uu____5248 = delta_qualifier t in incr_delta_depth uu____5248
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____5252 =
      let uu____5253 = FStar_Syntax_Subst.compress t in
      uu____5253.FStar_Syntax_Syntax.n in
    match uu____5252 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5256 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.list option =
  fun e  ->
    let uu____5264 = let uu____5274 = unmeta e in head_and_args uu____5274 in
    match uu____5264 with
    | (head1,args) ->
        let uu____5293 =
          let uu____5301 =
            let uu____5302 = un_uinst head1 in
            uu____5302.FStar_Syntax_Syntax.n in
          (uu____5301, args) in
        (match uu____5293 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5313) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____5326::(hd1,uu____5328)::(tl1,uu____5330)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____5364 =
               let uu____5368 =
                 let uu____5372 = list_elements tl1 in
                 FStar_Util.must uu____5372 in
               hd1 :: uu____5368 in
             Some uu____5364
         | uu____5381 -> None)
let rec apply_last f l =
  match l with
  | [] -> failwith "apply_last: got empty list"
  | a::[] -> let uu____5412 = f a in [uu____5412]
  | x::xs -> let uu____5416 = apply_last f xs in x :: uu____5416
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
let mk_squash p =
  let sq =
    FStar_Syntax_Syntax.fvar FStar_Syntax_Const.squash_lid
      (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")) None in
  let uu____5439 =
    FStar_Syntax_Syntax.mk_Tm_uinst sq [FStar_Syntax_Syntax.U_zero] in
  let uu____5442 =
    let uu____5448 = FStar_Syntax_Syntax.as_arg p in [uu____5448] in
  mk_app uu____5439 uu____5442
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option
  =
  fun t  ->
    let uu____5455 = head_and_args t in
    match uu____5455 with
    | (head1,args) ->
        let uu____5484 =
          let uu____5492 =
            let uu____5493 = un_uinst head1 in
            uu____5493.FStar_Syntax_Syntax.n in
          (uu____5492, args) in
        (match uu____5484 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____5506)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Syntax_Const.unit_lid
                  ->
                  let uu____5545 =
                    let uu____5548 =
                      let uu____5549 = FStar_Syntax_Syntax.mk_binder b in
                      [uu____5549] in
                    FStar_Syntax_Subst.open_term uu____5548 p in
                  (match uu____5545 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____5567 -> failwith "impossible" in
                       let uu____5570 =
                         let uu____5571 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (fst b1) uu____5571 in
                       if uu____5570 then None else Some p1)
              | uu____5579 -> None)
         | uu____5582 -> None)
let rec mk_list:
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____5609 =
            let uu____5612 =
              let uu____5613 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____5613 in
            FStar_Syntax_Syntax.mk uu____5612 in
          uu____5609 None rng in
        let cons1 args pos =
          let uu____5631 =
            let uu____5632 =
              let uu____5633 = ctor FStar_Syntax_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5633
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5632 args in
          uu____5631 None pos in
        let nil args pos =
          let uu____5647 =
            let uu____5648 =
              let uu____5649 = ctor FStar_Syntax_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5649
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5648 args in
          uu____5647 None pos in
        let uu____5654 =
          let uu____5655 =
            let uu____5656 = FStar_Syntax_Syntax.iarg typ in [uu____5656] in
          nil uu____5655 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____5659 =
                 let uu____5660 = FStar_Syntax_Syntax.iarg typ in
                 let uu____5661 =
                   let uu____5663 = FStar_Syntax_Syntax.as_arg t in
                   let uu____5664 =
                     let uu____5666 = FStar_Syntax_Syntax.as_arg a in
                     [uu____5666] in
                   uu____5663 :: uu____5664 in
                 uu____5660 :: uu____5661 in
               cons1 uu____5659 t.FStar_Syntax_Syntax.pos) l uu____5654
let rec eqlist eq1 xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
  | uu____5710 -> false
let eqsum e1 e2 x y =
  match (x, y) with
  | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
  | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
  | uu____5783 -> false
let eqprod e1 e2 x y =
  match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt e x y =
  match (x, y) with | (Some x1,Some y1) -> e x1 y1 | uu____5891 -> false
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
        | FStar_Syntax_Syntax.Tm_app uu____6004 ->
            let uu____6014 = head_and_args' t in
            (match uu____6014 with
             | (hd1,args) ->
                 let uu___179_6036 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.tk =
                     (uu___179_6036.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___179_6036.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___179_6036.FStar_Syntax_Syntax.vars)
                 })
        | uu____6048 -> t in
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
      | (uu____6269,uu____6270) -> false
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
      | (uu____6343,uu____6344) -> false
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
  fun uu____6349  ->
    fun uu____6350  ->
      match (uu____6349, uu____6350) with | ((p1,w1,t1),(p2,w2,t2)) -> false
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
        let uu____6460 = FStar_Syntax_Subst.compress t in
        uu____6460.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____6480 =
              let uu____6490 = ff f1 in
              let uu____6491 =
                FStar_List.map
                  (fun uu____6499  ->
                     match uu____6499 with
                     | (a,q) -> let uu____6506 = ff a in (uu____6506, q))
                  args in
              (uu____6490, uu____6491) in
            FStar_Syntax_Syntax.Tm_app uu____6480
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____6535 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____6535 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____6541 =
                   let uu____6556 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____6556, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____6541)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____6581 = let uu____6586 = ff t1 in (uu____6586, us) in
            FStar_Syntax_Syntax.Tm_uinst uu____6581
        | uu____6587 -> tn in
      f
        (let uu___180_6588 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.tk = (uu___180_6588.FStar_Syntax_Syntax.tk);
           FStar_Syntax_Syntax.pos = (uu___180_6588.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___180_6588.FStar_Syntax_Syntax.vars)
         })
let rec sizeof: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6596 ->
        let uu____6617 =
          let uu____6618 = FStar_Syntax_Subst.compress t in sizeof uu____6618 in
        (Prims.parse_int "1") + uu____6617
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____6620 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____6620
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____6622 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____6622
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____6629 = sizeof t1 in (FStar_List.length us) + uu____6629
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____6635) ->
        let uu____6658 = sizeof t1 in
        let uu____6659 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____6663  ->
                 match uu____6663 with
                 | (bv,uu____6667) ->
                     let uu____6668 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____6668) (Prims.parse_int "0") bs in
        uu____6658 + uu____6659
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____6685 = sizeof hd1 in
        let uu____6686 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____6690  ->
                 match uu____6690 with
                 | (arg,uu____6694) ->
                     let uu____6695 = sizeof arg in acc + uu____6695)
            (Prims.parse_int "0") args in
        uu____6685 + uu____6686
    | uu____6696 -> Prims.parse_int "1"