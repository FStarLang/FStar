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
          (fun uu____362  ->
             fun uu____363  ->
               match (uu____362, uu____363) with
               | ((x,uu____373),(y,uu____375)) ->
                   let uu____380 =
                     let uu____385 = FStar_Syntax_Syntax.bv_to_name y in
                     (x, uu____385) in
                   FStar_Syntax_Syntax.NT uu____380) replace_xs with_ys
      else failwith "Ill-formed substitution"
let rec unmeta: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,uu____392) -> unmeta e2
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____398,uu____399) -> unmeta e2
    | uu____428 -> e1
let rec univ_kernel:
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe* Prims.int) =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_name uu____436 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_unif uu____437 -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_zero  -> (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____441 = univ_kernel u1 in
        (match uu____441 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____448 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____452 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let constant_univ_as_nat: FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  -> let uu____458 = univ_kernel u in snd uu____458
let rec compare_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____467,uu____468) ->
          failwith "Impossible: compare_univs"
      | (uu____469,FStar_Syntax_Syntax.U_bvar uu____470) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_unknown ,uu____471) -> - (Prims.parse_int "1")
      | (uu____472,FStar_Syntax_Syntax.U_unknown ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_zero ,uu____473) -> - (Prims.parse_int "1")
      | (uu____474,FStar_Syntax_Syntax.U_zero ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____477,FStar_Syntax_Syntax.U_unif
         uu____478) -> - (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____481,FStar_Syntax_Syntax.U_name
         uu____482) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____491 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
          let uu____492 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
          uu____491 - uu____492
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1 in
          let n2 = FStar_List.length us2 in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____524 = FStar_List.zip us1 us2 in
               FStar_Util.find_map uu____524
                 (fun uu____530  ->
                    match uu____530 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21 in
                        if c <> (Prims.parse_int "0") then Some c else None) in
             match copt with | None  -> Prims.parse_int "0" | Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____540,uu____541) ->
          - (Prims.parse_int "1")
      | (uu____543,FStar_Syntax_Syntax.U_max uu____544) ->
          Prims.parse_int "1"
      | uu____546 ->
          let uu____549 = univ_kernel u1 in
          (match uu____549 with
           | (k1,n1) ->
               let uu____554 = univ_kernel u2 in
               (match uu____554 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2 in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
let eq_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____567 = compare_univs u1 u2 in
      uu____567 = (Prims.parse_int "0")
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
  | FStar_Syntax_Syntax.Total uu____594 -> FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.GTotal uu____600 ->
      FStar_Syntax_Const.effect_GTot_lid
let comp_flags c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____618 -> [FStar_Syntax_Syntax.TOTAL]
  | FStar_Syntax_Syntax.GTotal uu____624 -> [FStar_Syntax_Syntax.SOMETRIVIAL]
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
            let uu____654 =
              let uu____655 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____655 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____654;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____673 =
              let uu____674 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____674 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____673;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            } in
      let uu___174_684 = c in
      let uu____685 =
        let uu____686 =
          let uu___175_687 = comp_to_comp_typ c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___175_687.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___175_687.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___175_687.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___175_687.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____686 in
      {
        FStar_Syntax_Syntax.n = uu____685;
        FStar_Syntax_Syntax.tk = (uu___174_684.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___174_684.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___174_684.FStar_Syntax_Syntax.vars)
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
    | uu____718 ->
        failwith "Assertion failed: Computation type without universe"
let is_named_tot c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
        FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.Total uu____731 -> true
  | FStar_Syntax_Syntax.GTotal uu____737 -> false
let is_total_comp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___162_755  ->
          match uu___162_755 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____756 -> false))
let is_total_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Syntax_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___163_761  ->
               match uu___163_761 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____762 -> false)))
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
            (fun uu___164_767  ->
               match uu___164_767 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____768 -> false)))
let is_partial_return c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___165_781  ->
          match uu___165_781 with
          | FStar_Syntax_Syntax.RETURN  -> true
          | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
          | uu____782 -> false))
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___166_787  ->
            match uu___166_787 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____788 -> false))
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
  | FStar_Syntax_Syntax.Total uu____814 -> true
  | FStar_Syntax_Syntax.GTotal uu____820 -> false
  | FStar_Syntax_Syntax.Comp ct ->
      ((is_total_comp c) ||
         (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
        ||
        (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___167_828  ->
                 match uu___167_828 with
                 | FStar_Syntax_Syntax.LEMMA  -> true
                 | uu____829 -> false)))
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
            (fun uu___168_848  ->
               match uu___168_848 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____849 -> false)))
let is_pure_or_ghost_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
let is_pure_or_ghost_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____856 =
      let uu____857 = FStar_Syntax_Subst.compress t in
      uu____857.FStar_Syntax_Syntax.n in
    match uu____856 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____860,c) -> is_pure_or_ghost_comp c
    | uu____872 -> true
let is_lemma_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
        FStar_Syntax_Const.effect_Lemma_lid
  | uu____885 -> false
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____889 =
      let uu____890 = FStar_Syntax_Subst.compress t in
      uu____890.FStar_Syntax_Syntax.n in
    match uu____889 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____893,c) -> is_lemma_comp c
    | uu____905 -> false
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
    | uu____951 -> (t1, [])
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
        let uu____995 = head_and_args' head1 in
        (match uu____995 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1031 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1046) ->
        FStar_Syntax_Subst.compress t2
    | uu____1051 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1055 =
      let uu____1056 = FStar_Syntax_Subst.compress t in
      uu____1056.FStar_Syntax_Syntax.n in
    match uu____1055 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1059,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1075)::uu____1076 ->
                  let pats' = unmeta pats in
                  let uu____1107 = head_and_args pats' in
                  (match uu____1107 with
                   | (head1,uu____1118) ->
                       let uu____1133 =
                         let uu____1134 = un_uinst head1 in
                         uu____1134.FStar_Syntax_Syntax.n in
                       (match uu____1133 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.cons_lid
                        | uu____1138 -> false))
              | uu____1139 -> false)
         | uu____1145 -> false)
    | uu____1146 -> false
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
         FStar_Syntax_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___169_1160  ->
                 match uu___169_1160 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____1161 -> false)))
  | uu____1162 -> false
let comp_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____1177) -> t
  | FStar_Syntax_Syntax.GTotal (t,uu____1185) -> t
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let set_result_typ c t =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____1209 -> FStar_Syntax_Syntax.mk_Total t
  | FStar_Syntax_Syntax.GTotal uu____1215 -> FStar_Syntax_Syntax.mk_GTotal t
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Syntax_Syntax.mk_Comp
        (let uu___176_1222 = ct in
         {
           FStar_Syntax_Syntax.comp_univs =
             (uu___176_1222.FStar_Syntax_Syntax.comp_univs);
           FStar_Syntax_Syntax.effect_name =
             (uu___176_1222.FStar_Syntax_Syntax.effect_name);
           FStar_Syntax_Syntax.result_typ = t;
           FStar_Syntax_Syntax.effect_args =
             (uu___176_1222.FStar_Syntax_Syntax.effect_args);
           FStar_Syntax_Syntax.flags =
             (uu___176_1222.FStar_Syntax_Syntax.flags)
         })
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___170_1235  ->
          match uu___170_1235 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____1236 -> false))
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
  | uu____1258 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1264,uu____1265) ->
        unascribe e2
    | uu____1294 -> e1
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1336,uu____1337) ->
      ascribe t' k
  | uu____1366 ->
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (t, k, None))
        None t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal
  | NotEqual
  | Unknown
let uu___is_Equal: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1388 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1392 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1396 -> false
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let canon_app t =
        let uu____1417 =
          let uu____1425 = unascribe t in head_and_args' uu____1425 in
        match uu____1417 with
        | (hd1,args) ->
            FStar_Syntax_Syntax.mk_Tm_app hd1 args None
              t.FStar_Syntax_Syntax.pos in
      let t11 = canon_app t1 in
      let t21 = canon_app t2 in
      let equal_if uu___171_1451 = if uu___171_1451 then Equal else Unknown in
      let equal_iff uu___172_1456 = if uu___172_1456 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____1470 -> Unknown in
      let eq_inj f g =
        match (f, g) with
        | (Equal ,Equal ) -> Equal
        | (NotEqual ,uu____1478) -> NotEqual
        | (uu____1479,NotEqual ) -> NotEqual
        | (Unknown ,uu____1480) -> Unknown
        | (uu____1481,Unknown ) -> Unknown in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____1486 = FStar_Syntax_Syntax.fv_eq f g in
          equal_if uu____1486
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____1499 = eq_tm f g in
          eq_and uu____1499
            (fun uu____1500  ->
               let uu____1501 = eq_univs_list us vs in equal_if uu____1501)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____1504 = FStar_Const.eq_const c d in equal_iff uu____1504
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1506),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1508)) ->
          let uu____1533 = FStar_Syntax_Unionfind.equiv u1 u2 in
          equal_if uu____1533
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____1566 =
            let uu____1569 =
              let uu____1570 = un_uinst h1 in
              uu____1570.FStar_Syntax_Syntax.n in
            let uu____1573 =
              let uu____1574 = un_uinst h2 in
              uu____1574.FStar_Syntax_Syntax.n in
            (uu____1569, uu____1573) in
          (match uu____1566 with
           | (FStar_Syntax_Syntax.Tm_fvar f1,FStar_Syntax_Syntax.Tm_fvar f2)
               when
               (f1.FStar_Syntax_Syntax.fv_qual =
                  (Some FStar_Syntax_Syntax.Data_ctor))
                 &&
                 (f2.FStar_Syntax_Syntax.fv_qual =
                    (Some FStar_Syntax_Syntax.Data_ctor))
               ->
               let uu____1581 = FStar_Syntax_Syntax.fv_eq f1 f2 in
               if uu____1581
               then
                 let uu____1583 = FStar_List.zip args1 args2 in
                 FStar_All.pipe_left
                   (FStar_List.fold_left
                      (fun acc  ->
                         fun uu____1613  ->
                           match uu____1613 with
                           | ((a1,q1),(a2,q2)) ->
                               let uu____1629 = eq_tm a1 a2 in
                               eq_inj acc uu____1629) Equal) uu____1583
               else NotEqual
           | uu____1631 ->
               let uu____1634 = eq_tm h1 h2 in
               eq_and uu____1634 (fun uu____1635  -> eq_args args1 args2))
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____1638 = eq_univs u v1 in equal_if uu____1638
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1640),uu____1641) ->
          eq_tm t12 t21
      | (uu____1646,FStar_Syntax_Syntax.Tm_meta (t22,uu____1648)) ->
          eq_tm t11 t22
      | uu____1653 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1677)::a11,(b,uu____1680)::b1) ->
          let uu____1718 = eq_tm a b in
          (match uu____1718 with
           | Equal  -> eq_args a11 b1
           | uu____1719 -> Unknown)
      | uu____1720 -> Unknown
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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1738) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1744,uu____1745) ->
        unrefine t2
    | uu____1774 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1778 =
      let uu____1779 = unrefine t in uu____1779.FStar_Syntax_Syntax.n in
    match uu____1778 with
    | FStar_Syntax_Syntax.Tm_type uu____1782 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1785) -> is_unit t1
    | uu____1790 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1794 =
      let uu____1795 = unrefine t in uu____1795.FStar_Syntax_Syntax.n in
    match uu____1794 with
    | FStar_Syntax_Syntax.Tm_type uu____1798 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____1801) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1817) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____1822,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____1834 -> false
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1838 =
      let uu____1839 = FStar_Syntax_Subst.compress e in
      uu____1839.FStar_Syntax_Syntax.n in
    match uu____1838 with
    | FStar_Syntax_Syntax.Tm_abs uu____1842 -> true
    | uu____1857 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1861 =
      let uu____1862 = FStar_Syntax_Subst.compress t in
      uu____1862.FStar_Syntax_Syntax.n in
    match uu____1861 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1865 -> true
    | uu____1873 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1879) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1885,uu____1886) ->
        pre_typ t2
    | uu____1915 -> t1
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
      let uu____1929 =
        let uu____1930 = un_uinst typ1 in uu____1930.FStar_Syntax_Syntax.n in
      match uu____1929 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____1968 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____1984 -> None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____1995,lids,uu____1997) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____2002,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____2009,uu____2010,uu____2011,uu____2012,uu____2013) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____2019,uu____2020,uu____2021,uu____2022) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____2026,uu____2027,uu____2028,uu____2029,uu____2030) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2034,uu____2035) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____2037) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____2040 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____2041 -> []
    | FStar_Syntax_Syntax.Sig_main uu____2042 -> []
let lid_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident option =
  fun se  ->
    match lids_of_sigelt se with | l::[] -> Some l | uu____2050 -> None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb uu___173_2072 =
  match uu___173_2072 with
  | (FStar_Util.Inl x,uu____2079,uu____2080) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____2084,uu____2085) -> FStar_Ident.range_of_lid l
let range_of_arg uu____2102 =
  match uu____2102 with | (hd1,uu____2108) -> hd1.FStar_Syntax_Syntax.pos
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
      let uu____2222 =
        let uu____2225 =
          let uu____2226 =
            let uu____2231 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            (uu____2231,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app)) in
          FStar_Syntax_Syntax.Tm_meta uu____2226 in
        FStar_Syntax_Syntax.mk uu____2225 in
      uu____2222 None (FStar_Ident.range_of_lid l)
  | uu____2240 ->
      let e =
        let uu____2249 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor) in
        mk_app uu____2249 args in
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
      let uu____2264 =
        let uu____2267 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "7") in
        (uu____2267, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____2264
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
          let uu____2300 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____2300
          then
            let uu____2301 =
              let uu____2304 =
                let uu____2305 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____2305 in
              let uu____2306 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____2304, uu____2306) in
            FStar_Ident.mk_ident uu____2301
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___177_2309 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___177_2309.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___177_2309.FStar_Syntax_Syntax.sort)
          } in
        let uu____2310 = mk_field_projector_name_from_ident lid nm in
        (uu____2310, y)
let set_uvar:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____2317 = FStar_Syntax_Unionfind.find uv in
      match uu____2317 with
      | Some uu____2319 ->
          let uu____2320 =
            let uu____2321 =
              let uu____2322 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____2322 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2321 in
          failwith uu____2320
      | uu____2323 -> FStar_Syntax_Unionfind.change uv t
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
      | uu____2401 -> q1 = q2
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
          | Some (FStar_Util.Inr uu____2458) -> lopt1
          | Some (FStar_Util.Inl lc) ->
              let uu____2479 =
                let uu____2485 = FStar_Syntax_Subst.close_lcomp bs lc in
                FStar_Util.Inl uu____2485 in
              Some uu____2479 in
        match bs with
        | [] -> t
        | uu____2496 ->
            let body =
              let uu____2498 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____2498 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt'),None ) ->
                 let uu____2541 =
                   let uu____2544 =
                     let uu____2545 =
                       let uu____2560 =
                         let uu____2564 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____2564 bs' in
                       let uu____2570 = close_lopt lopt' in
                       (uu____2560, t1, uu____2570) in
                     FStar_Syntax_Syntax.Tm_abs uu____2545 in
                   FStar_Syntax_Syntax.mk uu____2544 in
                 uu____2541 None t1.FStar_Syntax_Syntax.pos
             | uu____2596 ->
                 let uu____2605 =
                   let uu____2608 =
                     let uu____2609 =
                       let uu____2624 = FStar_Syntax_Subst.close_binders bs in
                       let uu____2625 = close_lopt lopt in
                       (uu____2624, body, uu____2625) in
                     FStar_Syntax_Syntax.Tm_abs uu____2609 in
                   FStar_Syntax_Syntax.mk uu____2608 in
                 uu____2605 None t.FStar_Syntax_Syntax.pos)
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
      | uu____2668 ->
          let uu____2672 =
            let uu____2675 =
              let uu____2676 =
                let uu____2684 = FStar_Syntax_Subst.close_binders bs in
                let uu____2685 = FStar_Syntax_Subst.close_comp bs c in
                (uu____2684, uu____2685) in
              FStar_Syntax_Syntax.Tm_arrow uu____2676 in
            FStar_Syntax_Syntax.mk uu____2675 in
          uu____2672 None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____2715 =
        let uu____2716 = FStar_Syntax_Subst.compress t in
        uu____2716.FStar_Syntax_Syntax.n in
      match uu____2715 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2736) ->
               let uu____2743 =
                 let uu____2744 = FStar_Syntax_Subst.compress tres in
                 uu____2744.FStar_Syntax_Syntax.n in
               (match uu____2743 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____2761 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c')) uu____2761
                      t.FStar_Syntax_Syntax.pos
                | uu____2777 -> t)
           | uu____2778 -> t)
      | uu____2779 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____2788 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
      let uu____2793 =
        let uu____2794 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____2794 t.FStar_Syntax_Syntax.pos in
      let uu____2795 =
        let uu____2798 =
          let uu____2799 =
            let uu____2804 =
              let uu____2805 =
                let uu____2806 = FStar_Syntax_Syntax.mk_binder b in
                [uu____2806] in
              FStar_Syntax_Subst.close uu____2805 t in
            (b, uu____2804) in
          FStar_Syntax_Syntax.Tm_refine uu____2799 in
        FStar_Syntax_Syntax.mk uu____2798 in
      uu____2795 uu____2788 uu____2793
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
        let uu____2844 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____2844 with
         | (bs1,c1) ->
             let uu____2854 = is_tot_or_gtot_comp c1 in
             if uu____2854
             then
               let uu____2860 = arrow_formals_comp (comp_result c1) in
               (match uu____2860 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____2885 ->
        let uu____2886 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2886)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
  =
  fun k  ->
    let uu____2902 = arrow_formals_comp k in
    match uu____2902 with | (bs,c) -> (bs, (comp_result c))
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
            let uu___178_2983 = l1 in
            let uu____2984 =
              FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.res_typ in
            {
              FStar_Syntax_Syntax.eff_name =
                (uu___178_2983.FStar_Syntax_Syntax.eff_name);
              FStar_Syntax_Syntax.res_typ = uu____2984;
              FStar_Syntax_Syntax.cflags =
                (uu___178_2983.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                (fun uu____2987  ->
                   let uu____2988 = l1.FStar_Syntax_Syntax.comp () in
                   FStar_Syntax_Subst.subst_comp s uu____2988)
            } in
          Some (FStar_Util.Inl l2)
      | uu____2997 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____3035 =
        let uu____3036 =
          let uu____3039 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____3039 in
        uu____3036.FStar_Syntax_Syntax.n in
      match uu____3035 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____3077 = aux t2 what in
          (match uu____3077 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____3134 -> ([], t1, abs_body_lcomp) in
    let uu____3146 = aux t None in
    match uu____3146 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____3194 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____3194 with
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
                | (None ,uu____3284) -> def
                | (uu____3290,[]) -> def
                | (Some fvs,uu____3297) ->
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
            let uu____3358 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____3358 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____3374 ->
            let t' = arrow binders c in
            let uu____3381 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____3381 with
             | (uvs1,t'1) ->
                 let uu____3392 =
                   let uu____3393 = FStar_Syntax_Subst.compress t'1 in
                   uu____3393.FStar_Syntax_Syntax.n in
                 (match uu____3392 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____3419 -> failwith "Impossible"))
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
    | uu____3456 -> false
let mk_tuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3464 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "tuple%s" uu____3464 in
      let uu____3465 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3465 r
let mk_tuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3473 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mktuple%s" uu____3473 in
      let uu____3474 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3474 r
let is_tuple_data_lid: FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____3481 = mk_tuple_data_lid n1 FStar_Range.dummyRange in
      FStar_Ident.lid_equals f uu____3481
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
    | uu____3499 -> false
let mk_dtuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3507 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "dtuple%s" uu____3507 in
      let uu____3508 = let uu____3509 = mod_prefix_dtuple n1 in uu____3509 t in
      FStar_Ident.set_lid_range uu____3508 r
let mk_dtuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3519 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mkdtuple%s" uu____3519 in
      let uu____3520 = let uu____3521 = mod_prefix_dtuple n1 in uu____3521 t in
      FStar_Ident.set_lid_range uu____3520 r
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
      let uu____3561 =
        let uu____3562 = pre_typ t in uu____3562.FStar_Syntax_Syntax.n in
      match uu____3561 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3570 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3577 =
        let uu____3578 = pre_typ t in uu____3578.FStar_Syntax_Syntax.n in
      match uu____3577 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3581 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____3583) ->
          is_constructed_typ t1 lid
      | uu____3598 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term option =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____3605 -> Some t1
    | FStar_Syntax_Syntax.Tm_name uu____3606 -> Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____3607 -> Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____3609) -> get_tycon t2
    | uu____3624 -> None
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
  fun uu____3654  ->
    let u =
      let uu____3658 = FStar_Syntax_Unionfind.univ_fresh () in
      FStar_All.pipe_left (fun _0_27  -> FStar_Syntax_Syntax.U_unif _0_27)
        uu____3658 in
    let uu____3663 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u) None
        FStar_Range.dummyRange in
    (uu____3663, u)
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
          let uu____3686 =
            let uu____3689 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____3690 =
              let uu____3693 =
                let uu____3694 =
                  let uu____3704 =
                    let uu____3706 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____3707 =
                      let uu____3709 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____3709] in
                    uu____3706 :: uu____3707 in
                  (tand, uu____3704) in
                FStar_Syntax_Syntax.Tm_app uu____3694 in
              FStar_Syntax_Syntax.mk uu____3693 in
            uu____3690 None uu____3689 in
          Some uu____3686
let mk_binop op_t phi1 phi2 =
  let uu____3744 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos in
  let uu____3745 =
    let uu____3748 =
      let uu____3749 =
        let uu____3759 =
          let uu____3761 = FStar_Syntax_Syntax.as_arg phi1 in
          let uu____3762 =
            let uu____3764 = FStar_Syntax_Syntax.as_arg phi2 in [uu____3764] in
          uu____3761 :: uu____3762 in
        (op_t, uu____3759) in
      FStar_Syntax_Syntax.Tm_app uu____3749 in
    FStar_Syntax_Syntax.mk uu____3748 in
  uu____3745 None uu____3744
let mk_neg phi =
  let uu____3785 =
    let uu____3788 =
      let uu____3789 =
        let uu____3799 =
          let uu____3801 = FStar_Syntax_Syntax.as_arg phi in [uu____3801] in
        (t_not, uu____3799) in
      FStar_Syntax_Syntax.Tm_app uu____3789 in
    FStar_Syntax_Syntax.mk uu____3788 in
  uu____3785 None phi.FStar_Syntax_Syntax.pos
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
  let uu____3892 =
    let uu____3895 =
      let uu____3896 =
        let uu____3906 =
          let uu____3908 = FStar_Syntax_Syntax.as_arg e in [uu____3908] in
        (b2t_v, uu____3906) in
      FStar_Syntax_Syntax.Tm_app uu____3896 in
    FStar_Syntax_Syntax.mk uu____3895 in
  uu____3892 None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid
let mk_untyped_eq2 e1 e2 =
  let uu____3932 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos in
  let uu____3933 =
    let uu____3936 =
      let uu____3937 =
        let uu____3947 =
          let uu____3949 = FStar_Syntax_Syntax.as_arg e1 in
          let uu____3950 =
            let uu____3952 = FStar_Syntax_Syntax.as_arg e2 in [uu____3952] in
          uu____3949 :: uu____3950 in
        (teq, uu____3947) in
      FStar_Syntax_Syntax.Tm_app uu____3937 in
    FStar_Syntax_Syntax.mk uu____3936 in
  uu____3933 None uu____3932
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
          let uu____3975 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____3976 =
            let uu____3979 =
              let uu____3980 =
                let uu____3990 =
                  let uu____3992 = FStar_Syntax_Syntax.iarg t in
                  let uu____3993 =
                    let uu____3995 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____3996 =
                      let uu____3998 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____3998] in
                    uu____3995 :: uu____3996 in
                  uu____3992 :: uu____3993 in
                (eq_inst, uu____3990) in
              FStar_Syntax_Syntax.Tm_app uu____3980 in
            FStar_Syntax_Syntax.mk uu____3979 in
          uu____3976 None uu____3975
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange in
  let uu____4036 =
    let uu____4039 =
      let uu____4040 =
        let uu____4050 =
          let uu____4052 = FStar_Syntax_Syntax.iarg t in
          let uu____4053 =
            let uu____4055 = FStar_Syntax_Syntax.as_arg x in
            let uu____4056 =
              let uu____4058 = FStar_Syntax_Syntax.as_arg t' in [uu____4058] in
            uu____4055 :: uu____4056 in
          uu____4052 :: uu____4053 in
        (t_has_type1, uu____4050) in
      FStar_Syntax_Syntax.Tm_app uu____4040 in
    FStar_Syntax_Syntax.mk uu____4039 in
  uu____4036 None FStar_Range.dummyRange
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
    let uu____4077 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____4084 ->
          (FStar_Syntax_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____4091 ->
          (FStar_Syntax_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
    match uu____4077 with
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = ((fun uu____4104  -> c0))
        }
let mk_forall_aux fa x body =
  let uu____4128 =
    let uu____4131 =
      let uu____4132 =
        let uu____4142 =
          let uu____4144 =
            FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
          let uu____4145 =
            let uu____4147 =
              let uu____4148 =
                let uu____4149 =
                  let uu____4150 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____4150] in
                let uu____4151 =
                  let uu____4158 =
                    let uu____4164 =
                      let uu____4165 = FStar_Syntax_Syntax.mk_Total ktype0 in
                      FStar_All.pipe_left lcomp_of_comp uu____4165 in
                    FStar_Util.Inl uu____4164 in
                  Some uu____4158 in
                abs uu____4149 body uu____4151 in
              FStar_Syntax_Syntax.as_arg uu____4148 in
            [uu____4147] in
          uu____4144 :: uu____4145 in
        (fa, uu____4142) in
      FStar_Syntax_Syntax.Tm_app uu____4132 in
    FStar_Syntax_Syntax.mk uu____4131 in
  uu____4128 None FStar_Range.dummyRange
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
             let uu____4215 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____4215 then f1 else mk_forall_no_univ (fst b) f1) bs f
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____4228 -> true
  | uu____4229 -> false
let if_then_else b t1 t2 =
  let then_branch =
    let uu____4272 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos in
    (uu____4272, None, t1) in
  let else_branch =
    let uu____4295 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos in
    (uu____4295, None, t2) in
  let uu____4307 =
    let uu____4308 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4308 in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____4307
let mk_squash p =
  let sq =
    FStar_Syntax_Syntax.fvar FStar_Syntax_Const.squash_lid
      (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")) None in
  let uu____4366 =
    FStar_Syntax_Syntax.mk_Tm_uinst sq [FStar_Syntax_Syntax.U_zero] in
  let uu____4369 =
    let uu____4375 = FStar_Syntax_Syntax.as_arg p in [uu____4375] in
  mk_app uu____4366 uu____4369
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option
  =
  fun t  ->
    let uu____4382 = head_and_args t in
    match uu____4382 with
    | (head1,args) ->
        let uu____4411 =
          let uu____4419 =
            let uu____4420 = un_uinst head1 in
            uu____4420.FStar_Syntax_Syntax.n in
          (uu____4419, args) in
        (match uu____4411 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____4433)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine (b,p),[]) ->
             (match (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Syntax_Const.unit_lid
                  ->
                  let uu____4472 =
                    let uu____4475 =
                      let uu____4476 = FStar_Syntax_Syntax.mk_binder b in
                      [uu____4476] in
                    FStar_Syntax_Subst.open_term uu____4475 p in
                  (match uu____4472 with
                   | (bs,p1) ->
                       let b1 =
                         match bs with
                         | b1::[] -> b1
                         | uu____4494 -> failwith "impossible" in
                       let uu____4497 =
                         let uu____4498 = FStar_Syntax_Free.names p1 in
                         FStar_Util.set_mem (fst b1) uu____4498 in
                       if uu____4497 then None else Some p1)
              | uu____4506 -> None)
         | uu____4509 -> None)
let arrow_one:
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.comp) option
  =
  fun t  ->
    let uu____4528 =
      let uu____4529 = FStar_Syntax_Subst.compress t in
      uu____4529.FStar_Syntax_Syntax.n in
    match uu____4528 with
    | FStar_Syntax_Syntax.Tm_arrow ([],c) ->
        failwith "fatal: empty binders on arrow?"
    | FStar_Syntax_Syntax.Tm_arrow (b::[],c) -> Some (b, c)
    | FStar_Syntax_Syntax.Tm_arrow (b::bs,c) ->
        let uu____4590 =
          let uu____4595 =
            let uu____4596 = arrow bs c in
            FStar_Syntax_Syntax.mk_Total uu____4596 in
          (b, uu____4595) in
        Some uu____4590
    | uu____4603 -> None
let is_free_in:
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun bv  ->
    fun t  ->
      let uu____4612 = FStar_Syntax_Free.names t in
      FStar_Util.set_mem bv uu____4612
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | QEx of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | BaseConn of (FStar_Ident.lident* FStar_Syntax_Syntax.args)
let uu___is_QAll: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____4642 -> false
let __proj__QAll__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____4666 -> false
let __proj__QEx__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____4689 -> false
let __proj__BaseConn__item___0:
  connective -> (FStar_Ident.lident* FStar_Syntax_Syntax.args) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0
let destruct_typ_as_formula: FStar_Syntax_Syntax.term -> connective option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1 in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____4714) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____4724) ->
          unmeta_monadic t
      | uu____4734 -> f2 in
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
      let aux f2 uu____4779 =
        match uu____4779 with
        | (lid,arity) ->
            let uu____4785 =
              let uu____4795 = unmeta_monadic f2 in head_and_args uu____4795 in
            (match uu____4785 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____4814 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____4814 then Some (BaseConn (lid, args)) else None) in
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____4869 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____4869)
      | uu____4876 ->
          let uu____4877 = FStar_Syntax_Subst.compress t1 in ([], uu____4877) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____4919 = head_and_args t1 in
        match uu____4919 with
        | (t2,args) ->
            let uu____4950 = un_uinst t2 in
            let uu____4951 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____4967  ->
                      match uu____4967 with
                      | (t3,imp) ->
                          let uu____4974 = unascribe t3 in (uu____4974, imp))) in
            (uu____4950, uu____4951) in
      let rec aux qopt out t1 =
        let uu____4997 = let uu____5006 = flat t1 in (qopt, uu____5006) in
        match uu____4997 with
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____5021;
                 FStar_Syntax_Syntax.pos = uu____5022;
                 FStar_Syntax_Syntax.vars = uu____5023;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____5026);
                                                             FStar_Syntax_Syntax.tk
                                                               = uu____5027;
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____5028;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____5029;_},uu____5030)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____5091;
                 FStar_Syntax_Syntax.pos = uu____5092;
                 FStar_Syntax_Syntax.vars = uu____5093;_},uu____5094::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____5097);
                  FStar_Syntax_Syntax.tk = uu____5098;
                  FStar_Syntax_Syntax.pos = uu____5099;
                  FStar_Syntax_Syntax.vars = uu____5100;_},uu____5101)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____5169;
               FStar_Syntax_Syntax.pos = uu____5170;
               FStar_Syntax_Syntax.vars = uu____5171;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____5174);
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____5175;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____5176;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____5177;_},uu____5178)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____5246;
               FStar_Syntax_Syntax.pos = uu____5247;
               FStar_Syntax_Syntax.vars = uu____5248;_},uu____5249::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____5252);
                                                                    FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____5253;
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____5254;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____5255;_},uu____5256)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (Some b,uu____5332) ->
            let bs = FStar_List.rev out in
            let uu____5350 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____5350 with
             | (bs1,t2) ->
                 let uu____5356 = patterns t2 in
                 (match uu____5356 with
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs1, pats, body))
                      else Some (QEx (bs1, pats, body))))
        | uu____5394 -> None in
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
      let uu____5430 = un_squash t in
      FStar_Util.bind_opt uu____5430
        (fun t1  ->
           let uu____5439 = head_and_args' t1 in
           match uu____5439 with
           | (hd1,args) ->
               let uu____5460 =
                 let uu____5463 =
                   let uu____5464 = un_uinst hd1 in
                   uu____5464.FStar_Syntax_Syntax.n in
                 (uu____5463, (FStar_List.length args)) in
               (match uu____5460 with
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
                | uu____5524 -> None)) in
    let rec destruct_sq_forall t =
      let uu____5541 = un_squash t in
      FStar_Util.bind_opt uu____5541
        (fun t1  ->
           let uu____5550 = arrow_one t1 in
           match uu____5550 with
           | Some (b,c) ->
               let uu____5559 =
                 let uu____5560 = is_tot_or_gtot_comp c in
                 Prims.op_Negation uu____5560 in
               if uu____5559
               then None
               else
                 (let q =
                    let uu____5566 = comp_to_comp_typ c in
                    uu____5566.FStar_Syntax_Syntax.result_typ in
                  let uu____5567 = FStar_Syntax_Subst.open_term [b] q in
                  match uu____5567 with
                  | (bs,q1) ->
                      let b1 =
                        match bs with
                        | b1::[] -> b1
                        | uu____5585 -> failwith "impossible" in
                      let uu____5588 = is_free_in (fst b1) q1 in
                      if uu____5588
                      then
                        let uu____5590 = patterns q1 in
                        (match uu____5590 with
                         | (pats,q2) ->
                             FStar_All.pipe_left maybe_collect
                               (Some (QAll ([b1], pats, q2))))
                      else
                        (let uu____5630 =
                           let uu____5631 =
                             let uu____5634 =
                               let uu____5636 =
                                 FStar_Syntax_Syntax.as_arg
                                   (fst b1).FStar_Syntax_Syntax.sort in
                               let uu____5637 =
                                 let uu____5639 =
                                   FStar_Syntax_Syntax.as_arg q1 in
                                 [uu____5639] in
                               uu____5636 :: uu____5637 in
                             (FStar_Syntax_Const.imp_lid, uu____5634) in
                           BaseConn uu____5631 in
                         Some uu____5630))
           | uu____5641 -> None)
    and destruct_sq_exists t =
      let uu____5646 = un_squash t in
      FStar_Util.bind_opt uu____5646
        (fun t1  ->
           let uu____5655 = head_and_args' t1 in
           match uu____5655 with
           | (hd1,args) ->
               let uu____5676 =
                 let uu____5684 =
                   let uu____5685 = un_uinst hd1 in
                   uu____5685.FStar_Syntax_Syntax.n in
                 (uu____5684, args) in
               (match uu____5676 with
                | (FStar_Syntax_Syntax.Tm_fvar
                   fv,(a1,uu____5696)::(a2,uu____5698)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Syntax_Const.dtuple2_lid
                    ->
                    let uu____5724 =
                      let uu____5725 = FStar_Syntax_Subst.compress a2 in
                      uu____5725.FStar_Syntax_Syntax.n in
                    (match uu____5724 with
                     | FStar_Syntax_Syntax.Tm_abs (b::[],q,uu____5731) ->
                         let uu____5757 = FStar_Syntax_Subst.open_term [b] q in
                         (match uu____5757 with
                          | (bs,q1) ->
                              let b1 =
                                match bs with
                                | b1::[] -> b1
                                | uu____5779 -> failwith "impossible" in
                              let uu____5782 = patterns q1 in
                              (match uu____5782 with
                               | (pats,q2) ->
                                   FStar_All.pipe_left maybe_collect
                                     (Some (QEx ([b1], pats, q2)))))
                     | uu____5821 -> None)
                | uu____5822 -> None))
    and maybe_collect f1 =
      match f1 with
      | Some (QAll (bs,pats,phi)) ->
          let uu____5836 = destruct_sq_forall phi in
          (match uu____5836 with
           | Some (QAll (bs',pats',psi)) ->
               FStar_All.pipe_left (fun _0_36  -> Some _0_36)
                 (QAll
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____5849 -> f1)
      | Some (QEx (bs,pats,phi)) ->
          let uu____5854 = destruct_sq_exists phi in
          (match uu____5854 with
           | Some (QEx (bs',pats',psi)) ->
               FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                 (QEx
                    ((FStar_List.append bs bs'),
                      (FStar_List.append pats pats'), psi))
           | uu____5867 -> f1)
      | uu____5869 -> f1 in
    let phi = unmeta_monadic f in
    let uu____5872 = destruct_base_conn phi in
    FStar_Util.catch_opt uu____5872
      (fun uu____5874  ->
         let uu____5875 = destruct_q_conn phi in
         FStar_Util.catch_opt uu____5875
           (fun uu____5877  ->
              let uu____5878 = destruct_sq_base_conn phi in
              FStar_Util.catch_opt uu____5878
                (fun uu____5880  ->
                   let uu____5881 = destruct_sq_forall phi in
                   FStar_Util.catch_opt uu____5881
                     (fun uu____5883  ->
                        let uu____5884 = destruct_sq_exists phi in
                        FStar_Util.catch_opt uu____5884
                          (fun uu____5886  -> None)))))
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____5894 =
          let uu____5897 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None in
          FStar_Util.Inr uu____5897 in
        let uu____5898 =
          let uu____5899 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____5899 in
        let uu____5902 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn None in
        close_univs_and_mk_letbinding None uu____5894
          a.FStar_Syntax_Syntax.action_univs uu____5898
          FStar_Syntax_Const.effect_Tot_lid uu____5902 in
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
  let uu____5935 =
    let uu____5938 =
      let uu____5939 =
        let uu____5949 =
          let uu____5951 = FStar_Syntax_Syntax.as_arg t in [uu____5951] in
        (reify_, uu____5949) in
      FStar_Syntax_Syntax.Tm_app uu____5939 in
    FStar_Syntax_Syntax.mk uu____5938 in
  uu____5935 None t.FStar_Syntax_Syntax.pos
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____5967 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____5989 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____5990 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____5991 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____6007 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____6016 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____6017 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____6018 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____6027) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____6032;
           FStar_Syntax_Syntax.index = uu____6033;
           FStar_Syntax_Syntax.sort = t2;_},uu____6035)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____6043) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____6049,uu____6050) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____6080) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____6095,t2,uu____6097) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____6120,t2) -> delta_qualifier t2
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
  fun t  -> let uu____6140 = delta_qualifier t in incr_delta_depth uu____6140
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____6144 =
      let uu____6145 = FStar_Syntax_Subst.compress t in
      uu____6145.FStar_Syntax_Syntax.n in
    match uu____6144 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____6148 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.list option =
  fun e  ->
    let uu____6156 = let uu____6166 = unmeta e in head_and_args uu____6166 in
    match uu____6156 with
    | (head1,args) ->
        let uu____6185 =
          let uu____6193 =
            let uu____6194 = un_uinst head1 in
            uu____6194.FStar_Syntax_Syntax.n in
          (uu____6193, args) in
        (match uu____6185 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____6205) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____6218::(hd1,uu____6220)::(tl1,uu____6222)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____6256 =
               let uu____6260 =
                 let uu____6264 = list_elements tl1 in
                 FStar_Util.must uu____6264 in
               hd1 :: uu____6260 in
             Some uu____6256
         | uu____6273 -> None)
let rec apply_last f l =
  match l with
  | [] -> failwith "apply_last: got empty list"
  | a::[] -> let uu____6304 = f a in [uu____6304]
  | x::xs -> let uu____6308 = apply_last f xs in x :: uu____6308
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
          let uu____6338 =
            let uu____6341 =
              let uu____6342 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____6342 in
            FStar_Syntax_Syntax.mk uu____6341 in
          uu____6338 None rng in
        let cons1 args pos =
          let uu____6360 =
            let uu____6361 =
              let uu____6362 = ctor FStar_Syntax_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____6362
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____6361 args in
          uu____6360 None pos in
        let nil args pos =
          let uu____6376 =
            let uu____6377 =
              let uu____6378 = ctor FStar_Syntax_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____6378
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____6377 args in
          uu____6376 None pos in
        let uu____6383 =
          let uu____6384 =
            let uu____6385 = FStar_Syntax_Syntax.iarg typ in [uu____6385] in
          nil uu____6384 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____6388 =
                 let uu____6389 = FStar_Syntax_Syntax.iarg typ in
                 let uu____6390 =
                   let uu____6392 = FStar_Syntax_Syntax.as_arg t in
                   let uu____6393 =
                     let uu____6395 = FStar_Syntax_Syntax.as_arg a in
                     [uu____6395] in
                   uu____6392 :: uu____6393 in
                 uu____6389 :: uu____6390 in
               cons1 uu____6388 t.FStar_Syntax_Syntax.pos) l uu____6383
let rec eqlist eq1 xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
  | uu____6439 -> false
let eqsum e1 e2 x y =
  match (x, y) with
  | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
  | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
  | uu____6512 -> false
let eqprod e1 e2 x y =
  match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt e x y =
  match (x, y) with | (Some x1,Some y1) -> e x1 y1 | uu____6620 -> false
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
        | FStar_Syntax_Syntax.Tm_app uu____6733 ->
            let uu____6743 = head_and_args' t in
            (match uu____6743 with
             | (hd1,args) ->
                 let uu___179_6765 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.tk =
                     (uu___179_6765.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___179_6765.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___179_6765.FStar_Syntax_Syntax.vars)
                 })
        | uu____6777 -> t in
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
      | (uu____6998,uu____6999) -> false
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
      | (uu____7072,uu____7073) -> false
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
  fun uu____7078  ->
    fun uu____7079  ->
      match (uu____7078, uu____7079) with | ((p1,w1,t1),(p2,w2,t2)) -> false
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
        let uu____7189 = FStar_Syntax_Subst.compress t in
        uu____7189.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____7209 =
              let uu____7219 = ff f1 in
              let uu____7220 =
                FStar_List.map
                  (fun uu____7228  ->
                     match uu____7228 with
                     | (a,q) -> let uu____7235 = ff a in (uu____7235, q))
                  args in
              (uu____7219, uu____7220) in
            FStar_Syntax_Syntax.Tm_app uu____7209
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____7264 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____7264 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____7270 =
                   let uu____7285 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____7285, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____7270)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____7310 = let uu____7315 = ff t1 in (uu____7315, us) in
            FStar_Syntax_Syntax.Tm_uinst uu____7310
        | uu____7316 -> tn in
      f
        (let uu___180_7317 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.tk = (uu___180_7317.FStar_Syntax_Syntax.tk);
           FStar_Syntax_Syntax.pos = (uu___180_7317.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___180_7317.FStar_Syntax_Syntax.vars)
         })
let rec sizeof: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____7325 ->
        let uu____7346 =
          let uu____7347 = FStar_Syntax_Subst.compress t in sizeof uu____7347 in
        (Prims.parse_int "1") + uu____7346
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____7349 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____7349
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____7351 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____7351
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____7358 = sizeof t1 in (FStar_List.length us) + uu____7358
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____7367) ->
        let uu____7390 = sizeof t1 in
        let uu____7391 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____7395  ->
                 match uu____7395 with
                 | (bv,uu____7399) ->
                     let uu____7400 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____7400) (Prims.parse_int "0") bs in
        uu____7390 + uu____7391
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____7417 = sizeof hd1 in
        let uu____7418 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____7422  ->
                 match uu____7422 with
                 | (arg,uu____7426) ->
                     let uu____7427 = sizeof arg in acc + uu____7427)
            (Prims.parse_int "0") args in
        uu____7417 + uu____7418
    | uu____7428 -> Prims.parse_int "1"