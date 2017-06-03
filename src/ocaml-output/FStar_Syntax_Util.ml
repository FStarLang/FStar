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
      let uu___173_684 = c in
      let uu____685 =
        let uu____686 =
          let uu___174_687 = comp_to_comp_typ c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___174_687.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___174_687.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___174_687.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___174_687.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____686 in
      {
        FStar_Syntax_Syntax.n = uu____685;
        FStar_Syntax_Syntax.tk = (uu___173_684.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___173_684.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___173_684.FStar_Syntax_Syntax.vars)
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
       (fun uu___161_755  ->
          match uu___161_755 with
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
            (fun uu___162_761  ->
               match uu___162_761 with
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
            (fun uu___163_767  ->
               match uu___163_767 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____768 -> false)))
let is_partial_return c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___164_781  ->
          match uu___164_781 with
          | FStar_Syntax_Syntax.RETURN  -> true
          | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
          | uu____782 -> false))
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___165_787  ->
            match uu___165_787 with
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
              (fun uu___166_828  ->
                 match uu___166_828 with
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
            (fun uu___167_848  ->
               match uu___167_848 with
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
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____876 =
      let uu____877 = FStar_Syntax_Subst.compress t in
      uu____877.FStar_Syntax_Syntax.n in
    match uu____876 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____880,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct ->
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
         | uu____893 -> false)
    | uu____894 -> false
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
    | uu____940 -> (t1, [])
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
        let uu____984 = head_and_args' head1 in
        (match uu____984 with
         | (head2,args') -> (head2, (FStar_List.append args' args)))
    | uu____1020 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____1035) ->
        FStar_Syntax_Subst.compress t2
    | uu____1040 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1044 =
      let uu____1045 = FStar_Syntax_Subst.compress t in
      uu____1045.FStar_Syntax_Syntax.n in
    match uu____1044 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____1048,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____1064)::uu____1065 ->
                  let pats' = unmeta pats in
                  let uu____1096 = head_and_args pats' in
                  (match uu____1096 with
                   | (head1,uu____1107) ->
                       let uu____1122 =
                         let uu____1123 = un_uinst head1 in
                         uu____1123.FStar_Syntax_Syntax.n in
                       (match uu____1122 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.cons_lid
                        | uu____1127 -> false))
              | uu____1128 -> false)
         | uu____1134 -> false)
    | uu____1135 -> false
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
         FStar_Syntax_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___168_1149  ->
                 match uu___168_1149 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____1150 -> false)))
  | uu____1151 -> false
let comp_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____1166) -> t
  | FStar_Syntax_Syntax.GTotal (t,uu____1174) -> t
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let set_result_typ c t =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____1198 -> FStar_Syntax_Syntax.mk_Total t
  | FStar_Syntax_Syntax.GTotal uu____1204 -> FStar_Syntax_Syntax.mk_GTotal t
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Syntax_Syntax.mk_Comp
        (let uu___175_1211 = ct in
         {
           FStar_Syntax_Syntax.comp_univs =
             (uu___175_1211.FStar_Syntax_Syntax.comp_univs);
           FStar_Syntax_Syntax.effect_name =
             (uu___175_1211.FStar_Syntax_Syntax.effect_name);
           FStar_Syntax_Syntax.result_typ = t;
           FStar_Syntax_Syntax.effect_args =
             (uu___175_1211.FStar_Syntax_Syntax.effect_args);
           FStar_Syntax_Syntax.flags =
             (uu___175_1211.FStar_Syntax_Syntax.flags)
         })
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___169_1224  ->
          match uu___169_1224 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____1225 -> false))
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
  | uu____1247 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1253,uu____1254) ->
        unascribe e2
    | uu____1283 -> e1
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1325,uu____1326) ->
      ascribe t' k
  | uu____1355 ->
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (t, k, None))
        None t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal
  | NotEqual
  | Unknown
let uu___is_Equal: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1377 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1381 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1385 -> false
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let t11 = unascribe t1 in
      let t21 = unascribe t2 in
      let equal_if uu___170_1405 = if uu___170_1405 then Equal else Unknown in
      let equal_iff uu___171_1410 = if uu___171_1410 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____1424 -> Unknown in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____1429 = FStar_Syntax_Syntax.fv_eq f g in
          equal_if uu____1429
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____1442 = eq_tm f g in
          eq_and uu____1442
            (fun uu____1443  ->
               let uu____1444 = eq_univs_list us vs in equal_if uu____1444)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____1447 = FStar_Const.eq_const c d in equal_iff uu____1447
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1449),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1451)) ->
          let uu____1476 = FStar_Syntax_Unionfind.equiv u1 u2 in
          equal_if uu____1476
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____1509 = eq_tm h1 h2 in
          eq_and uu____1509 (fun uu____1510  -> eq_args args1 args2)
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____1513 = eq_univs u v1 in equal_if uu____1513
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1515),uu____1516) ->
          eq_tm t12 t21
      | (uu____1521,FStar_Syntax_Syntax.Tm_meta (t22,uu____1523)) ->
          eq_tm t11 t22
      | uu____1528 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1552)::a11,(b,uu____1555)::b1) ->
          let uu____1593 = eq_tm a b in
          (match uu____1593 with
           | Equal  -> eq_args a11 b1
           | uu____1594 -> Unknown)
      | uu____1595 -> Unknown
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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1613) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1619,uu____1620) ->
        unrefine t2
    | uu____1649 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1653 =
      let uu____1654 = unrefine t in uu____1654.FStar_Syntax_Syntax.n in
    match uu____1653 with
    | FStar_Syntax_Syntax.Tm_type uu____1657 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1660) -> is_unit t1
    | uu____1665 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1669 =
      let uu____1670 = unrefine t in uu____1670.FStar_Syntax_Syntax.n in
    match uu____1669 with
    | FStar_Syntax_Syntax.Tm_type uu____1673 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____1676) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1692) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____1697,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____1709 -> false
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1713 =
      let uu____1714 = FStar_Syntax_Subst.compress e in
      uu____1714.FStar_Syntax_Syntax.n in
    match uu____1713 with
    | FStar_Syntax_Syntax.Tm_abs uu____1717 -> true
    | uu____1732 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1736 =
      let uu____1737 = FStar_Syntax_Subst.compress t in
      uu____1737.FStar_Syntax_Syntax.n in
    match uu____1736 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1740 -> true
    | uu____1748 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1754) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1760,uu____1761) ->
        pre_typ t2
    | uu____1790 -> t1
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
      let uu____1804 =
        let uu____1805 = un_uinst typ1 in uu____1805.FStar_Syntax_Syntax.n in
      match uu____1804 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____1843 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____1859 -> None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____1870,lids,uu____1872) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____1877,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____1884,uu____1885,uu____1886,uu____1887,uu____1888) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____1894,uu____1895,uu____1896,uu____1897) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____1901,uu____1902,uu____1903,uu____1904,uu____1905) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1909,uu____1910) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____1912) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____1915 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____1916 -> []
    | FStar_Syntax_Syntax.Sig_main uu____1917 -> []
let lid_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident option =
  fun se  ->
    match lids_of_sigelt se with | l::[] -> Some l | uu____1925 -> None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb uu___172_1947 =
  match uu___172_1947 with
  | (FStar_Util.Inl x,uu____1954,uu____1955) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____1959,uu____1960) -> FStar_Ident.range_of_lid l
let range_of_arg uu____1977 =
  match uu____1977 with | (hd1,uu____1983) -> hd1.FStar_Syntax_Syntax.pos
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
      let uu____2097 =
        let uu____2100 =
          let uu____2101 =
            let uu____2106 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            (uu____2106,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app)) in
          FStar_Syntax_Syntax.Tm_meta uu____2101 in
        FStar_Syntax_Syntax.mk uu____2100 in
      uu____2097 None (FStar_Ident.range_of_lid l)
  | uu____2115 ->
      let e =
        let uu____2124 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor) in
        mk_app uu____2124 args in
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
      let uu____2139 =
        let uu____2142 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "7") in
        (uu____2142, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____2139
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
          let uu____2175 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____2175
          then
            let uu____2176 =
              let uu____2179 =
                let uu____2180 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____2180 in
              let uu____2181 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____2179, uu____2181) in
            FStar_Ident.mk_ident uu____2176
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___176_2184 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___176_2184.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___176_2184.FStar_Syntax_Syntax.sort)
          } in
        let uu____2185 = mk_field_projector_name_from_ident lid nm in
        (uu____2185, y)
let set_uvar:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____2192 = FStar_Syntax_Unionfind.find uv in
      match uu____2192 with
      | Some uu____2194 ->
          let uu____2195 =
            let uu____2196 =
              let uu____2197 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____2197 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2196 in
          failwith uu____2195
      | uu____2198 -> FStar_Syntax_Unionfind.change uv t
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
      | uu____2276 -> q1 = q2
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
          | Some (FStar_Util.Inr uu____2333) -> lopt1
          | Some (FStar_Util.Inl lc) ->
              let uu____2354 =
                let uu____2360 = FStar_Syntax_Subst.close_lcomp bs lc in
                FStar_Util.Inl uu____2360 in
              Some uu____2354 in
        match bs with
        | [] -> t
        | uu____2371 ->
            let body =
              let uu____2373 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____2373 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt'),None ) ->
                 let uu____2416 =
                   let uu____2419 =
                     let uu____2420 =
                       let uu____2435 =
                         let uu____2439 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____2439 bs' in
                       let uu____2445 = close_lopt lopt' in
                       (uu____2435, t1, uu____2445) in
                     FStar_Syntax_Syntax.Tm_abs uu____2420 in
                   FStar_Syntax_Syntax.mk uu____2419 in
                 uu____2416 None t1.FStar_Syntax_Syntax.pos
             | uu____2471 ->
                 let uu____2480 =
                   let uu____2483 =
                     let uu____2484 =
                       let uu____2499 = FStar_Syntax_Subst.close_binders bs in
                       let uu____2500 = close_lopt lopt in
                       (uu____2499, body, uu____2500) in
                     FStar_Syntax_Syntax.Tm_abs uu____2484 in
                   FStar_Syntax_Syntax.mk uu____2483 in
                 uu____2480 None t.FStar_Syntax_Syntax.pos)
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
      | uu____2543 ->
          let uu____2547 =
            let uu____2550 =
              let uu____2551 =
                let uu____2559 = FStar_Syntax_Subst.close_binders bs in
                let uu____2560 = FStar_Syntax_Subst.close_comp bs c in
                (uu____2559, uu____2560) in
              FStar_Syntax_Syntax.Tm_arrow uu____2551 in
            FStar_Syntax_Syntax.mk uu____2550 in
          uu____2547 None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____2590 =
        let uu____2591 = FStar_Syntax_Subst.compress t in
        uu____2591.FStar_Syntax_Syntax.n in
      match uu____2590 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2611) ->
               let uu____2618 =
                 let uu____2619 = FStar_Syntax_Subst.compress tres in
                 uu____2619.FStar_Syntax_Syntax.n in
               (match uu____2618 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____2636 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c')) uu____2636
                      t.FStar_Syntax_Syntax.pos
                | uu____2652 -> t)
           | uu____2653 -> t)
      | uu____2654 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____2663 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
      let uu____2668 =
        let uu____2669 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____2669 t.FStar_Syntax_Syntax.pos in
      let uu____2670 =
        let uu____2673 =
          let uu____2674 =
            let uu____2679 =
              let uu____2680 =
                let uu____2681 = FStar_Syntax_Syntax.mk_binder b in
                [uu____2681] in
              FStar_Syntax_Subst.close uu____2680 t in
            (b, uu____2679) in
          FStar_Syntax_Syntax.Tm_refine uu____2674 in
        FStar_Syntax_Syntax.mk uu____2673 in
      uu____2670 uu____2663 uu____2668
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
        let uu____2719 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____2719 with
         | (bs1,c1) ->
             let uu____2729 = is_tot_or_gtot_comp c1 in
             if uu____2729
             then
               let uu____2735 = arrow_formals_comp (comp_result c1) in
               (match uu____2735 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____2760 ->
        let uu____2761 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2761)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
  =
  fun k  ->
    let uu____2777 = arrow_formals_comp k in
    match uu____2777 with | (bs,c) -> (bs, (comp_result c))
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
            let uu___177_2858 = l1 in
            let uu____2859 =
              FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.res_typ in
            {
              FStar_Syntax_Syntax.eff_name =
                (uu___177_2858.FStar_Syntax_Syntax.eff_name);
              FStar_Syntax_Syntax.res_typ = uu____2859;
              FStar_Syntax_Syntax.cflags =
                (uu___177_2858.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                (fun uu____2862  ->
                   let uu____2863 = l1.FStar_Syntax_Syntax.comp () in
                   FStar_Syntax_Subst.subst_comp s uu____2863)
            } in
          Some (FStar_Util.Inl l2)
      | uu____2872 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____2910 =
        let uu____2911 =
          let uu____2914 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____2914 in
        uu____2911.FStar_Syntax_Syntax.n in
      match uu____2910 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____2952 = aux t2 what in
          (match uu____2952 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____3009 -> ([], t1, abs_body_lcomp) in
    let uu____3021 = aux t None in
    match uu____3021 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____3069 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____3069 with
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
                | (None ,uu____3159) -> def
                | (uu____3165,[]) -> def
                | (Some fvs,uu____3172) ->
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
            let uu____3233 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____3233 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____3249 ->
            let t' = arrow binders c in
            let uu____3256 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____3256 with
             | (uvs1,t'1) ->
                 let uu____3267 =
                   let uu____3268 = FStar_Syntax_Subst.compress t'1 in
                   uu____3268.FStar_Syntax_Syntax.n in
                 (match uu____3267 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____3294 -> failwith "Impossible"))
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
    | uu____3331 -> false
let mk_tuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3339 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "tuple%s" uu____3339 in
      let uu____3340 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3340 r
let mk_tuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3348 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mktuple%s" uu____3348 in
      let uu____3349 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3349 r
let is_tuple_data_lid: FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____3356 = mk_tuple_data_lid n1 FStar_Range.dummyRange in
      FStar_Ident.lid_equals f uu____3356
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
    | uu____3374 -> false
let mk_dtuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3382 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "dtuple%s" uu____3382 in
      let uu____3383 = let uu____3384 = mod_prefix_dtuple n1 in uu____3384 t in
      FStar_Ident.set_lid_range uu____3383 r
let mk_dtuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3394 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mkdtuple%s" uu____3394 in
      let uu____3395 = let uu____3396 = mod_prefix_dtuple n1 in uu____3396 t in
      FStar_Ident.set_lid_range uu____3395 r
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
      let uu____3436 =
        let uu____3437 = pre_typ t in uu____3437.FStar_Syntax_Syntax.n in
      match uu____3436 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3445 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3452 =
        let uu____3453 = pre_typ t in uu____3453.FStar_Syntax_Syntax.n in
      match uu____3452 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3456 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____3458) ->
          is_constructed_typ t1 lid
      | uu____3473 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term option =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____3480 -> Some t1
    | FStar_Syntax_Syntax.Tm_name uu____3481 -> Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____3482 -> Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____3484) -> get_tycon t2
    | uu____3499 -> None
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
  fun uu____3529  ->
    let u =
      let uu____3533 = FStar_Syntax_Unionfind.univ_fresh () in
      FStar_All.pipe_left (fun _0_27  -> FStar_Syntax_Syntax.U_unif _0_27)
        uu____3533 in
    let uu____3538 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u) None
        FStar_Range.dummyRange in
    (uu____3538, u)
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
          let uu____3561 =
            let uu____3564 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____3565 =
              let uu____3568 =
                let uu____3569 =
                  let uu____3579 =
                    let uu____3581 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____3582 =
                      let uu____3584 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____3584] in
                    uu____3581 :: uu____3582 in
                  (tand, uu____3579) in
                FStar_Syntax_Syntax.Tm_app uu____3569 in
              FStar_Syntax_Syntax.mk uu____3568 in
            uu____3565 None uu____3564 in
          Some uu____3561
let mk_binop op_t phi1 phi2 =
  let uu____3619 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos in
  let uu____3620 =
    let uu____3623 =
      let uu____3624 =
        let uu____3634 =
          let uu____3636 = FStar_Syntax_Syntax.as_arg phi1 in
          let uu____3637 =
            let uu____3639 = FStar_Syntax_Syntax.as_arg phi2 in [uu____3639] in
          uu____3636 :: uu____3637 in
        (op_t, uu____3634) in
      FStar_Syntax_Syntax.Tm_app uu____3624 in
    FStar_Syntax_Syntax.mk uu____3623 in
  uu____3620 None uu____3619
let mk_neg phi =
  let uu____3660 =
    let uu____3663 =
      let uu____3664 =
        let uu____3674 =
          let uu____3676 = FStar_Syntax_Syntax.as_arg phi in [uu____3676] in
        (t_not, uu____3674) in
      FStar_Syntax_Syntax.Tm_app uu____3664 in
    FStar_Syntax_Syntax.mk uu____3663 in
  uu____3660 None phi.FStar_Syntax_Syntax.pos
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
  let uu____3767 =
    let uu____3770 =
      let uu____3771 =
        let uu____3781 =
          let uu____3783 = FStar_Syntax_Syntax.as_arg e in [uu____3783] in
        (b2t_v, uu____3781) in
      FStar_Syntax_Syntax.Tm_app uu____3771 in
    FStar_Syntax_Syntax.mk uu____3770 in
  uu____3767 None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid
let mk_untyped_eq2 e1 e2 =
  let uu____3807 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos in
  let uu____3808 =
    let uu____3811 =
      let uu____3812 =
        let uu____3822 =
          let uu____3824 = FStar_Syntax_Syntax.as_arg e1 in
          let uu____3825 =
            let uu____3827 = FStar_Syntax_Syntax.as_arg e2 in [uu____3827] in
          uu____3824 :: uu____3825 in
        (teq, uu____3822) in
      FStar_Syntax_Syntax.Tm_app uu____3812 in
    FStar_Syntax_Syntax.mk uu____3811 in
  uu____3808 None uu____3807
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
          let uu____3850 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____3851 =
            let uu____3854 =
              let uu____3855 =
                let uu____3865 =
                  let uu____3867 = FStar_Syntax_Syntax.iarg t in
                  let uu____3868 =
                    let uu____3870 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____3871 =
                      let uu____3873 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____3873] in
                    uu____3870 :: uu____3871 in
                  uu____3867 :: uu____3868 in
                (eq_inst, uu____3865) in
              FStar_Syntax_Syntax.Tm_app uu____3855 in
            FStar_Syntax_Syntax.mk uu____3854 in
          uu____3851 None uu____3850
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange in
  let uu____3911 =
    let uu____3914 =
      let uu____3915 =
        let uu____3925 =
          let uu____3927 = FStar_Syntax_Syntax.iarg t in
          let uu____3928 =
            let uu____3930 = FStar_Syntax_Syntax.as_arg x in
            let uu____3931 =
              let uu____3933 = FStar_Syntax_Syntax.as_arg t' in [uu____3933] in
            uu____3930 :: uu____3931 in
          uu____3927 :: uu____3928 in
        (t_has_type1, uu____3925) in
      FStar_Syntax_Syntax.Tm_app uu____3915 in
    FStar_Syntax_Syntax.mk uu____3914 in
  uu____3911 None FStar_Range.dummyRange
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
    let uu____3952 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3959 ->
          (FStar_Syntax_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3966 ->
          (FStar_Syntax_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
    match uu____3952 with
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
          FStar_Syntax_Syntax.comp = ((fun uu____3979  -> c0))
        }
let mk_forall_aux fa x body =
  let uu____4003 =
    let uu____4006 =
      let uu____4007 =
        let uu____4017 =
          let uu____4019 =
            FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
          let uu____4020 =
            let uu____4022 =
              let uu____4023 =
                let uu____4024 =
                  let uu____4025 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____4025] in
                let uu____4026 =
                  let uu____4033 =
                    let uu____4039 =
                      let uu____4040 = FStar_Syntax_Syntax.mk_Total ktype0 in
                      FStar_All.pipe_left lcomp_of_comp uu____4040 in
                    FStar_Util.Inl uu____4039 in
                  Some uu____4033 in
                abs uu____4024 body uu____4026 in
              FStar_Syntax_Syntax.as_arg uu____4023 in
            [uu____4022] in
          uu____4019 :: uu____4020 in
        (fa, uu____4017) in
      FStar_Syntax_Syntax.Tm_app uu____4007 in
    FStar_Syntax_Syntax.mk uu____4006 in
  uu____4003 None FStar_Range.dummyRange
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
             let uu____4090 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____4090 then f1 else mk_forall_no_univ (fst b) f1) bs f
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____4103 -> true
  | uu____4104 -> false
let if_then_else b t1 t2 =
  let then_branch =
    let uu____4147 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos in
    (uu____4147, None, t1) in
  let else_branch =
    let uu____4170 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos in
    (uu____4170, None, t2) in
  let uu____4182 =
    let uu____4183 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4183 in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____4182
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | QEx of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | BaseConn of (FStar_Ident.lident* FStar_Syntax_Syntax.args)
let uu___is_QAll: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____4256 -> false
let __proj__QAll__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____4280 -> false
let __proj__QEx__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____4303 -> false
let __proj__BaseConn__item___0:
  connective -> (FStar_Ident.lident* FStar_Syntax_Syntax.args) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0
let destruct_typ_as_formula: FStar_Syntax_Syntax.term -> connective option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1 in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic uu____4328) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____4338) ->
          unmeta_monadic t
      | uu____4348 -> f2 in
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
      let aux f2 uu____4393 =
        match uu____4393 with
        | (lid,arity) ->
            let uu____4399 =
              let uu____4409 = unmeta_monadic f2 in head_and_args uu____4409 in
            (match uu____4399 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____4428 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____4428 then Some (BaseConn (lid, args)) else None) in
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____4483 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____4483)
      | uu____4490 ->
          let uu____4491 = FStar_Syntax_Subst.compress t1 in ([], uu____4491) in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
        let uu____4533 = head_and_args t1 in
        match uu____4533 with
        | (t2,args) ->
            let uu____4564 = un_uinst t2 in
            let uu____4565 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____4581  ->
                      match uu____4581 with
                      | (t3,imp) ->
                          let uu____4588 = unascribe t3 in (uu____4588, imp))) in
            (uu____4564, uu____4565) in
      let rec aux qopt out t1 =
        let uu____4611 = let uu____4620 = flat t1 in (qopt, uu____4620) in
        match uu____4611 with
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____4635;
                 FStar_Syntax_Syntax.pos = uu____4636;
                 FStar_Syntax_Syntax.vars = uu____4637;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____4640);
                                                             FStar_Syntax_Syntax.tk
                                                               = uu____4641;
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____4642;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____4643;_},uu____4644)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____4705;
                 FStar_Syntax_Syntax.pos = uu____4706;
                 FStar_Syntax_Syntax.vars = uu____4707;_},uu____4708::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____4711);
                  FStar_Syntax_Syntax.tk = uu____4712;
                  FStar_Syntax_Syntax.pos = uu____4713;
                  FStar_Syntax_Syntax.vars = uu____4714;_},uu____4715)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____4783;
               FStar_Syntax_Syntax.pos = uu____4784;
               FStar_Syntax_Syntax.vars = uu____4785;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____4788);
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____4789;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____4790;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____4791;_},uu____4792)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____4860;
               FStar_Syntax_Syntax.pos = uu____4861;
               FStar_Syntax_Syntax.vars = uu____4862;_},uu____4863::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____4866);
                                                                    FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____4867;
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____4868;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____4869;_},uu____4870)::[]))
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (Some b,uu____4946) ->
            let bs = FStar_List.rev out in
            let uu____4964 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____4964 with
             | (bs1,t2) ->
                 let uu____4970 = patterns t2 in
                 (match uu____4970 with
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs1, pats, body))
                      else Some (QEx (bs1, pats, body))))
        | uu____5008 -> None in
      aux None [] t in
    let phi = unmeta_monadic f in
    let uu____5020 = destruct_base_conn phi in
    match uu____5020 with | Some b -> Some b | None  -> destruct_q_conn phi
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____5031 =
          let uu____5034 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None in
          FStar_Util.Inr uu____5034 in
        let uu____5035 =
          let uu____5036 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____5036 in
        let uu____5039 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn None in
        close_univs_and_mk_letbinding None uu____5031
          a.FStar_Syntax_Syntax.action_univs uu____5035
          FStar_Syntax_Const.effect_Tot_lid uu____5039 in
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
  let uu____5072 =
    let uu____5075 =
      let uu____5076 =
        let uu____5086 =
          let uu____5088 = FStar_Syntax_Syntax.as_arg t in [uu____5088] in
        (reify_, uu____5086) in
      FStar_Syntax_Syntax.Tm_app uu____5076 in
    FStar_Syntax_Syntax.mk uu____5075 in
  uu____5072 None t.FStar_Syntax_Syntax.pos
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____5104 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____5126 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____5127 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____5128 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____5144 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____5153 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____5154 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____5155 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5164) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____5169;
           FStar_Syntax_Syntax.index = uu____5170;
           FStar_Syntax_Syntax.sort = t2;_},uu____5172)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____5180) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5186,uu____5187) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5217) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____5232,t2,uu____5234) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____5257,t2) -> delta_qualifier t2
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
  fun t  -> let uu____5277 = delta_qualifier t in incr_delta_depth uu____5277
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____5281 =
      let uu____5282 = FStar_Syntax_Subst.compress t in
      uu____5282.FStar_Syntax_Syntax.n in
    match uu____5281 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5285 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.list option =
  fun e  ->
    let uu____5293 = let uu____5303 = unmeta e in head_and_args uu____5303 in
    match uu____5293 with
    | (head1,args) ->
        let uu____5322 =
          let uu____5330 =
            let uu____5331 = un_uinst head1 in
            uu____5331.FStar_Syntax_Syntax.n in
          (uu____5330, args) in
        (match uu____5322 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5342) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____5355::(hd1,uu____5357)::(tl1,uu____5359)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____5393 =
               let uu____5397 =
                 let uu____5401 = list_elements tl1 in
                 FStar_Util.must uu____5401 in
               hd1 :: uu____5397 in
             Some uu____5393
         | uu____5410 -> None)
let rec apply_last f l =
  match l with
  | [] -> failwith "apply_last: got empty list"
  | a::[] -> let uu____5441 = f a in [uu____5441]
  | x::xs -> let uu____5445 = apply_last f xs in x :: uu____5445
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
  let uu____5468 =
    FStar_Syntax_Syntax.mk_Tm_uinst sq [FStar_Syntax_Syntax.U_zero] in
  let uu____5471 =
    let uu____5477 = FStar_Syntax_Syntax.as_arg p in [uu____5477] in
  mk_app uu____5468 uu____5471
let un_squash:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax option
  =
  fun t  ->
    let uu____5484 = head_and_args t in
    match uu____5484 with
    | (head1,args) ->
        let uu____5513 =
          let uu____5521 =
            let uu____5522 = un_uinst head1 in
            uu____5522.FStar_Syntax_Syntax.n in
          (uu____5521, args) in
        (match uu____5513 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,(p,uu____5535)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid
             -> Some p
         | (FStar_Syntax_Syntax.Tm_refine
            ({ FStar_Syntax_Syntax.ppname = uu____5555;
               FStar_Syntax_Syntax.index = uu____5556;
               FStar_Syntax_Syntax.sort =
                 { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                   FStar_Syntax_Syntax.tk = uu____5558;
                   FStar_Syntax_Syntax.pos = uu____5559;
                   FStar_Syntax_Syntax.vars = uu____5560;_};_},p),[])
             when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid ->
             Some p
         | uu____5579 -> None)
let rec mk_list:
  FStar_Syntax_Syntax.term ->
    FStar_Range.range ->
      FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term
  =
  fun typ  ->
    fun rng  ->
      fun l  ->
        let ctor l1 =
          let uu____5606 =
            let uu____5609 =
              let uu____5610 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____5610 in
            FStar_Syntax_Syntax.mk uu____5609 in
          uu____5606 None rng in
        let cons1 args pos =
          let uu____5628 =
            let uu____5629 =
              let uu____5630 = ctor FStar_Syntax_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5630
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5629 args in
          uu____5628 None pos in
        let nil args pos =
          let uu____5644 =
            let uu____5645 =
              let uu____5646 = ctor FStar_Syntax_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5646
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5645 args in
          uu____5644 None pos in
        let uu____5651 =
          let uu____5652 =
            let uu____5653 = FStar_Syntax_Syntax.iarg typ in [uu____5653] in
          nil uu____5652 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____5656 =
                 let uu____5657 = FStar_Syntax_Syntax.iarg typ in
                 let uu____5658 =
                   let uu____5660 = FStar_Syntax_Syntax.as_arg t in
                   let uu____5661 =
                     let uu____5663 = FStar_Syntax_Syntax.as_arg a in
                     [uu____5663] in
                   uu____5660 :: uu____5661 in
                 uu____5657 :: uu____5658 in
               cons1 uu____5656 t.FStar_Syntax_Syntax.pos) l uu____5651
let rec eqlist eq1 xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
  | uu____5707 -> false
let eqsum e1 e2 x y =
  match (x, y) with
  | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
  | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
  | uu____5780 -> false
let eqprod e1 e2 x y =
  match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt e x y =
  match (x, y) with | (Some x1,Some y1) -> e x1 y1 | uu____5888 -> false
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
        | FStar_Syntax_Syntax.Tm_app uu____6001 ->
            let uu____6011 = head_and_args' t in
            (match uu____6011 with
             | (hd1,args) ->
                 let uu___178_6033 = t in
                 {
                   FStar_Syntax_Syntax.n =
                     (FStar_Syntax_Syntax.Tm_app (hd1, args));
                   FStar_Syntax_Syntax.tk =
                     (uu___178_6033.FStar_Syntax_Syntax.tk);
                   FStar_Syntax_Syntax.pos =
                     (uu___178_6033.FStar_Syntax_Syntax.pos);
                   FStar_Syntax_Syntax.vars =
                     (uu___178_6033.FStar_Syntax_Syntax.vars)
                 })
        | uu____6045 -> t in
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
      | (uu____6254,uu____6255) -> false
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
      | (uu____6328,uu____6329) -> false
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
  fun uu____6334  ->
    fun uu____6335  ->
      match (uu____6334, uu____6335) with | ((p1,w1,t1),(p2,w2,t2)) -> false
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
        let uu____6445 = FStar_Syntax_Subst.compress t in
        uu____6445.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____6465 =
              let uu____6475 = ff f1 in
              let uu____6476 =
                FStar_List.map
                  (fun uu____6484  ->
                     match uu____6484 with
                     | (a,q) -> let uu____6491 = ff a in (uu____6491, q))
                  args in
              (uu____6475, uu____6476) in
            FStar_Syntax_Syntax.Tm_app uu____6465
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____6520 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____6520 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____6526 =
                   let uu____6541 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____6541, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____6526)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
            let uu____6566 = let uu____6571 = ff t1 in (uu____6571, us) in
            FStar_Syntax_Syntax.Tm_uinst uu____6566
        | uu____6572 -> tn in
      f
        (let uu___179_6573 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.tk = (uu___179_6573.FStar_Syntax_Syntax.tk);
           FStar_Syntax_Syntax.pos = (uu___179_6573.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___179_6573.FStar_Syntax_Syntax.vars)
         })
let rec sizeof: FStar_Syntax_Syntax.term -> Prims.int =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____6581 ->
        let uu____6602 =
          let uu____6603 = FStar_Syntax_Subst.compress t in sizeof uu____6603 in
        (Prims.parse_int "1") + uu____6602
    | FStar_Syntax_Syntax.Tm_bvar bv ->
        let uu____6605 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____6605
    | FStar_Syntax_Syntax.Tm_name bv ->
        let uu____6607 = sizeof bv.FStar_Syntax_Syntax.sort in
        (Prims.parse_int "1") + uu____6607
    | FStar_Syntax_Syntax.Tm_uinst (t1,us) ->
        let uu____6614 = sizeof t1 in (FStar_List.length us) + uu____6614
    | FStar_Syntax_Syntax.Tm_abs (bs,t1,uu____6623) ->
        let uu____6646 = sizeof t1 in
        let uu____6647 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____6651  ->
                 match uu____6651 with
                 | (bv,uu____6655) ->
                     let uu____6656 = sizeof bv.FStar_Syntax_Syntax.sort in
                     acc + uu____6656) (Prims.parse_int "0") bs in
        uu____6646 + uu____6647
    | FStar_Syntax_Syntax.Tm_app (hd1,args) ->
        let uu____6673 = sizeof hd1 in
        let uu____6674 =
          FStar_List.fold_left
            (fun acc  ->
               fun uu____6678  ->
                 match uu____6678 with
                 | (arg,uu____6682) ->
                     let uu____6683 = sizeof arg in acc + uu____6683)
            (Prims.parse_int "0") args in
        uu____6673 + uu____6674
    | uu____6684 -> Prims.parse_int "1"