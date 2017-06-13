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
        let uu____435 = univ_kernel u1 in
        (match uu____435 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____442 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____446 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
let constant_univ_as_nat: FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  -> let uu____452 = univ_kernel u in snd uu____452
let rec compare_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar uu____461,uu____462) ->
          failwith "Impossible: compare_univs"
      | (uu____463,FStar_Syntax_Syntax.U_bvar uu____464) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_unknown ,uu____465) -> - (Prims.parse_int "1")
      | (uu____466,FStar_Syntax_Syntax.U_unknown ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          Prims.parse_int "0"
      | (FStar_Syntax_Syntax.U_zero ,uu____467) -> - (Prims.parse_int "1")
      | (uu____468,FStar_Syntax_Syntax.U_zero ) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____471,FStar_Syntax_Syntax.U_unif
         uu____472) -> - (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____477,FStar_Syntax_Syntax.U_name
         uu____478) -> Prims.parse_int "1"
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____493 = FStar_Syntax_Unionfind.univ_uvar_id u11 in
          let uu____494 = FStar_Syntax_Unionfind.univ_uvar_id u21 in
          uu____493 - uu____494
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1 in
          let n2 = FStar_List.length us2 in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____515 = FStar_List.zip us1 us2 in
               FStar_Util.find_map uu____515
                 (fun uu____521  ->
                    match uu____521 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21 in
                        if c <> (Prims.parse_int "0") then Some c else None) in
             match copt with | None  -> Prims.parse_int "0" | Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____531,uu____532) ->
          - (Prims.parse_int "1")
      | (uu____534,FStar_Syntax_Syntax.U_max uu____535) ->
          Prims.parse_int "1"
      | uu____537 ->
          let uu____540 = univ_kernel u1 in
          (match uu____540 with
           | (k1,n1) ->
               let uu____545 = univ_kernel u2 in
               (match uu____545 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2 in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
let eq_univs:
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____558 = compare_univs u1 u2 in
      uu____558 = (Prims.parse_int "0")
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
  | FStar_Syntax_Syntax.Total uu____585 -> FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.GTotal uu____591 ->
      FStar_Syntax_Const.effect_GTot_lid
let comp_flags c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____609 -> [FStar_Syntax_Syntax.TOTAL]
  | FStar_Syntax_Syntax.GTotal uu____615 -> [FStar_Syntax_Syntax.SOMETRIVIAL]
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
            let uu____645 =
              let uu____646 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____646 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____645;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
        | FStar_Syntax_Syntax.GTotal (t,u_opt) ->
            let uu____664 =
              let uu____665 = FStar_Util.map_opt u_opt (fun x  -> [x]) in
              FStar_Util.dflt [] uu____665 in
            {
              FStar_Syntax_Syntax.comp_univs = uu____664;
              FStar_Syntax_Syntax.effect_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.result_typ = t;
              FStar_Syntax_Syntax.effect_args = [];
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            } in
      let uu___166_675 = c in
      let uu____676 =
        let uu____677 =
          let uu___167_678 = comp_to_comp_typ c in
          {
            FStar_Syntax_Syntax.comp_univs =
              (uu___167_678.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_name =
              (uu___167_678.FStar_Syntax_Syntax.effect_name);
            FStar_Syntax_Syntax.result_typ =
              (uu___167_678.FStar_Syntax_Syntax.result_typ);
            FStar_Syntax_Syntax.effect_args =
              (uu___167_678.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          } in
        FStar_Syntax_Syntax.Comp uu____677 in
      {
        FStar_Syntax_Syntax.n = uu____676;
        FStar_Syntax_Syntax.tk = (uu___166_675.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___166_675.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___166_675.FStar_Syntax_Syntax.vars)
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
    | uu____709 ->
        failwith "Assertion failed: Computation type without universe"
let is_named_tot c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
        FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.Total uu____722 -> true
  | FStar_Syntax_Syntax.GTotal uu____728 -> false
let is_total_comp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___154_746  ->
          match uu___154_746 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____747 -> false))
let is_total_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.eff_name
       FStar_Syntax_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
         (FStar_Util.for_some
            (fun uu___155_752  ->
               match uu___155_752 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____753 -> false)))
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
            (fun uu___156_758  ->
               match uu___156_758 with
               | FStar_Syntax_Syntax.TOTAL  -> true
               | FStar_Syntax_Syntax.RETURN  -> true
               | uu____759 -> false)))
let is_partial_return c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___157_772  ->
          match uu___157_772 with
          | FStar_Syntax_Syntax.RETURN  -> true
          | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
          | uu____773 -> false))
let is_lcomp_partial_return: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.cflags
      (FStar_Util.for_some
         (fun uu___158_778  ->
            match uu___158_778 with
            | FStar_Syntax_Syntax.RETURN  -> true
            | FStar_Syntax_Syntax.PARTIAL_RETURN  -> true
            | uu____779 -> false))
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
  | FStar_Syntax_Syntax.Total uu____805 -> true
  | FStar_Syntax_Syntax.GTotal uu____811 -> false
  | FStar_Syntax_Syntax.Comp ct ->
      ((is_total_comp c) ||
         (is_pure_effect ct.FStar_Syntax_Syntax.effect_name))
        ||
        (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___159_819  ->
                 match uu___159_819 with
                 | FStar_Syntax_Syntax.LEMMA  -> true
                 | uu____820 -> false)))
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
            (fun uu___160_839  ->
               match uu___160_839 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____840 -> false)))
let is_pure_or_ghost_lcomp: FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.eff_name)
let is_pure_or_ghost_function: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____847 =
      let uu____848 = FStar_Syntax_Subst.compress t in
      uu____848.FStar_Syntax_Syntax.n in
    match uu____847 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____851,c) -> is_pure_or_ghost_comp c
    | uu____863 -> true
let is_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____867 =
      let uu____868 = FStar_Syntax_Subst.compress t in
      uu____868.FStar_Syntax_Syntax.n in
    match uu____867 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____871,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct ->
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
         | uu____884 -> false)
    | uu____885 -> false
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
    | uu____931 -> (t1, [])
let un_uinst: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____946) ->
        FStar_Syntax_Subst.compress t2
    | uu____951 -> t1
let is_smt_lemma: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____955 =
      let uu____956 = FStar_Syntax_Subst.compress t in
      uu____956.FStar_Syntax_Syntax.n in
    match uu____955 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____959,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.effect_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____975)::uu____976 ->
                  let pats' = unmeta pats in
                  let uu____1007 = head_and_args pats' in
                  (match uu____1007 with
                   | (head1,uu____1018) ->
                       let uu____1033 =
                         let uu____1034 = un_uinst head1 in
                         uu____1034.FStar_Syntax_Syntax.n in
                       (match uu____1033 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.cons_lid
                        | uu____1038 -> false))
              | uu____1039 -> false)
         | uu____1045 -> false)
    | uu____1046 -> false
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.effect_name
         FStar_Syntax_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___161_1060  ->
                 match uu___161_1060 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____1061 -> false)))
  | uu____1062 -> false
let comp_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,uu____1077) -> t
  | FStar_Syntax_Syntax.GTotal (t,uu____1085) -> t
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.result_typ
let set_result_typ c t =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____1109 -> FStar_Syntax_Syntax.mk_Total t
  | FStar_Syntax_Syntax.GTotal uu____1115 -> FStar_Syntax_Syntax.mk_GTotal t
  | FStar_Syntax_Syntax.Comp ct ->
      FStar_Syntax_Syntax.mk_Comp
        (let uu___168_1122 = ct in
         {
           FStar_Syntax_Syntax.comp_univs =
             (uu___168_1122.FStar_Syntax_Syntax.comp_univs);
           FStar_Syntax_Syntax.effect_name =
             (uu___168_1122.FStar_Syntax_Syntax.effect_name);
           FStar_Syntax_Syntax.result_typ = t;
           FStar_Syntax_Syntax.effect_args =
             (uu___168_1122.FStar_Syntax_Syntax.effect_args);
           FStar_Syntax_Syntax.flags =
             (uu___168_1122.FStar_Syntax_Syntax.flags)
         })
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___162_1135  ->
          match uu___162_1135 with
          | FStar_Syntax_Syntax.TOTAL  -> true
          | FStar_Syntax_Syntax.RETURN  -> true
          | uu____1136 -> false))
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
  | uu____1158 -> false
let rec unascribe: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1164,uu____1165) ->
        unascribe e2
    | uu____1194 -> e1
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1236,uu____1237) ->
      ascribe t' k
  | uu____1266 ->
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (t, k, None))
        None t.FStar_Syntax_Syntax.pos
type eq_result =
  | Equal
  | NotEqual
  | Unknown
let uu___is_Equal: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1288 -> false
let uu___is_NotEqual: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1292 -> false
let uu___is_Unknown: eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1296 -> false
let rec eq_tm:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let t11 = unascribe t1 in
      let t21 = unascribe t2 in
      let equal_if uu___163_1316 = if uu___163_1316 then Equal else Unknown in
      let equal_iff uu___164_1321 = if uu___164_1321 then Equal else NotEqual in
      let eq_and f g = match f with | Equal  -> g () | uu____1335 -> Unknown in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____1340 = FStar_Syntax_Syntax.fv_eq f g in
          equal_if uu____1340
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____1353 = eq_tm f g in
          eq_and uu____1353
            (fun uu____1354  ->
               let uu____1355 = eq_univs_list us vs in equal_if uu____1355)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____1358 = FStar_Const.eq_const c d in equal_iff uu____1358
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1360),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1362)) ->
          let uu____1395 = FStar_Syntax_Unionfind.equiv u1 u2 in
          equal_if uu____1395
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____1428 = eq_tm h1 h2 in
          eq_and uu____1428 (fun uu____1429  -> eq_args args1 args2)
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____1432 = eq_univs u v1 in equal_if uu____1432
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1434),uu____1435) ->
          eq_tm t12 t21
      | (uu____1440,FStar_Syntax_Syntax.Tm_meta (t22,uu____1442)) ->
          eq_tm t11 t22
      | uu____1447 -> Unknown
and eq_args:
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1471)::a11,(b,uu____1474)::b1) ->
          let uu____1512 = eq_tm a b in
          (match uu____1512 with
           | Equal  -> eq_args a11 b1
           | uu____1513 -> Unknown)
      | uu____1514 -> Unknown
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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1528) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1534,uu____1535) ->
        unrefine t2
    | uu____1564 -> t1
let rec is_unit: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1568 =
      let uu____1569 = unrefine t in uu____1569.FStar_Syntax_Syntax.n in
    match uu____1568 with
    | FStar_Syntax_Syntax.Tm_type uu____1572 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1575) -> is_unit t1
    | uu____1580 -> false
let rec non_informative: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1584 =
      let uu____1585 = unrefine t in uu____1585.FStar_Syntax_Syntax.n in
    match uu____1584 with
    | FStar_Syntax_Syntax.Tm_type uu____1588 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid))
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.erased_lid)
    | FStar_Syntax_Syntax.Tm_app (head1,uu____1591) -> non_informative head1
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1607) -> non_informative t1
    | FStar_Syntax_Syntax.Tm_arrow (uu____1612,c) ->
        (is_tot_or_gtot_comp c) && (non_informative (comp_result c))
    | uu____1624 -> false
let is_fun: FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1628 =
      let uu____1629 = FStar_Syntax_Subst.compress e in
      uu____1629.FStar_Syntax_Syntax.n in
    match uu____1628 with
    | FStar_Syntax_Syntax.Tm_abs uu____1632 -> true
    | uu____1647 -> false
let is_function_typ: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1651 =
      let uu____1652 = FStar_Syntax_Subst.compress t in
      uu____1652.FStar_Syntax_Syntax.n in
    match uu____1651 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1655 -> true
    | uu____1663 -> false
let rec pre_typ: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1669) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1675,uu____1676) ->
        pre_typ t2
    | uu____1705 -> t1
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
      let uu____1719 =
        let uu____1720 = un_uinst typ1 in uu____1720.FStar_Syntax_Syntax.n in
      match uu____1719 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1 in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____1758 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____1774 -> None
let lids_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_let (uu____1785,lids,uu____1787) -> lids
    | FStar_Syntax_Syntax.Sig_bundle (uu____1792,lids) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ
        (lid,uu____1799,uu____1800,uu____1801,uu____1802,uu____1803) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_effect_abbrev
        (lid,uu____1809,uu____1810,uu____1811,uu____1812) -> [lid]
    | FStar_Syntax_Syntax.Sig_datacon
        (lid,uu____1816,uu____1817,uu____1818,uu____1819,uu____1820) -> 
        [lid]
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____1824,uu____1825) ->
        [lid]
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____1827,uu____1828) -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free n1 ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_new_effect n1 -> [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect uu____1831 -> []
    | FStar_Syntax_Syntax.Sig_pragma uu____1832 -> []
    | FStar_Syntax_Syntax.Sig_main uu____1833 -> []
let lid_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident option =
  fun se  ->
    match lids_of_sigelt se with | l::[] -> Some l | uu____1841 -> None
let quals_of_sigelt:
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  -> x.FStar_Syntax_Syntax.sigquals
let range_of_sigelt: FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  -> x.FStar_Syntax_Syntax.sigrng
let range_of_lb uu___165_1863 =
  match uu___165_1863 with
  | (FStar_Util.Inl x,uu____1870,uu____1871) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____1875,uu____1876) -> FStar_Ident.range_of_lid l
let range_of_arg uu____1893 =
  match uu____1893 with | (hd1,uu____1899) -> hd1.FStar_Syntax_Syntax.pos
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
      let uu____2013 =
        let uu____2016 =
          let uu____2017 =
            let uu____2022 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor) in
            (uu____2022,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app)) in
          FStar_Syntax_Syntax.Tm_meta uu____2017 in
        FStar_Syntax_Syntax.mk uu____2016 in
      uu____2013 None (FStar_Ident.range_of_lid l)
  | uu____2031 ->
      let e =
        let uu____2040 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor) in
        mk_app uu____2040 args in
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
      let uu____2055 =
        let uu____2058 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "7") in
        (uu____2058, (x.FStar_Ident.idRange)) in
      FStar_Ident.mk_ident uu____2055
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
          let uu____2091 = FStar_Syntax_Syntax.is_null_bv x in
          if uu____2091
          then
            let uu____2092 =
              let uu____2095 =
                let uu____2096 = FStar_Util.string_of_int i in
                Prims.strcat "_" uu____2096 in
              let uu____2097 = FStar_Syntax_Syntax.range_of_bv x in
              (uu____2095, uu____2097) in
            FStar_Ident.mk_ident uu____2092
          else x.FStar_Syntax_Syntax.ppname in
        let y =
          let uu___169_2100 = x in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___169_2100.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___169_2100.FStar_Syntax_Syntax.sort)
          } in
        let uu____2101 = mk_field_projector_name_from_ident lid nm in
        (uu____2101, y)
let set_uvar:
  FStar_Syntax_Syntax.uvar -> FStar_Syntax_Syntax.term -> Prims.unit =
  fun uv  ->
    fun t  ->
      let uu____2108 = FStar_Syntax_Unionfind.find uv in
      match uu____2108 with
      | Some uu____2110 ->
          let uu____2111 =
            let uu____2112 =
              let uu____2113 = FStar_Syntax_Unionfind.uvar_id uv in
              FStar_All.pipe_left FStar_Util.string_of_int uu____2113 in
            FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2112 in
          failwith uu____2111
      | uu____2114 -> FStar_Syntax_Unionfind.change uv t
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
      | uu____2176 -> q1 = q2
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
          | Some (FStar_Util.Inr uu____2233) -> lopt1
          | Some (FStar_Util.Inl lc) ->
              let uu____2254 =
                let uu____2260 = FStar_Syntax_Subst.close_lcomp bs lc in
                FStar_Util.Inl uu____2260 in
              Some uu____2254 in
        match bs with
        | [] -> t
        | uu____2271 ->
            let body =
              let uu____2273 = FStar_Syntax_Subst.close bs t in
              FStar_Syntax_Subst.compress uu____2273 in
            (match ((body.FStar_Syntax_Syntax.n), lopt) with
             | (FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt'),None ) ->
                 let uu____2316 =
                   let uu____2319 =
                     let uu____2320 =
                       let uu____2335 =
                         let uu____2339 = FStar_Syntax_Subst.close_binders bs in
                         FStar_List.append uu____2339 bs' in
                       let uu____2345 = close_lopt lopt' in
                       (uu____2335, t1, uu____2345) in
                     FStar_Syntax_Syntax.Tm_abs uu____2320 in
                   FStar_Syntax_Syntax.mk uu____2319 in
                 uu____2316 None t1.FStar_Syntax_Syntax.pos
             | uu____2371 ->
                 let uu____2380 =
                   let uu____2383 =
                     let uu____2384 =
                       let uu____2399 = FStar_Syntax_Subst.close_binders bs in
                       let uu____2400 = close_lopt lopt in
                       (uu____2399, body, uu____2400) in
                     FStar_Syntax_Syntax.Tm_abs uu____2384 in
                   FStar_Syntax_Syntax.mk uu____2383 in
                 uu____2380 None t.FStar_Syntax_Syntax.pos)
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
      | uu____2443 ->
          let uu____2447 =
            let uu____2450 =
              let uu____2451 =
                let uu____2459 = FStar_Syntax_Subst.close_binders bs in
                let uu____2460 = FStar_Syntax_Subst.close_comp bs c in
                (uu____2459, uu____2460) in
              FStar_Syntax_Syntax.Tm_arrow uu____2451 in
            FStar_Syntax_Syntax.mk uu____2450 in
          uu____2447 None c.FStar_Syntax_Syntax.pos
let flat_arrow:
  (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c in
      let uu____2490 =
        let uu____2491 = FStar_Syntax_Subst.compress t in
        uu____2491.FStar_Syntax_Syntax.n in
      match uu____2490 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2511) ->
               let uu____2518 =
                 let uu____2519 = FStar_Syntax_Subst.compress tres in
                 uu____2519.FStar_Syntax_Syntax.n in
               (match uu____2518 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____2536 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_arrow
                         ((FStar_List.append bs1 bs'), c')) uu____2536
                      t.FStar_Syntax_Syntax.pos
                | uu____2552 -> t)
           | uu____2553 -> t)
      | uu____2554 -> t
let refine:
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____2563 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk in
      let uu____2568 =
        let uu____2569 = FStar_Syntax_Syntax.range_of_bv b in
        FStar_Range.union_ranges uu____2569 t.FStar_Syntax_Syntax.pos in
      let uu____2570 =
        let uu____2573 =
          let uu____2574 =
            let uu____2579 =
              let uu____2580 =
                let uu____2581 = FStar_Syntax_Syntax.mk_binder b in
                [uu____2581] in
              FStar_Syntax_Subst.close uu____2580 t in
            (b, uu____2579) in
          FStar_Syntax_Syntax.Tm_refine uu____2574 in
        FStar_Syntax_Syntax.mk uu____2573 in
      uu____2570 uu____2563 uu____2568
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
        let uu____2619 = FStar_Syntax_Subst.open_comp bs c in
        (match uu____2619 with
         | (bs1,c1) ->
             let uu____2629 = is_tot_or_gtot_comp c1 in
             if uu____2629
             then
               let uu____2635 = arrow_formals_comp (comp_result c1) in
               (match uu____2635 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____2660 ->
        let uu____2661 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2661)
let rec arrow_formals:
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list*
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax)
  =
  fun k  ->
    let uu____2677 = arrow_formals_comp k in
    match uu____2677 with | (bs,c) -> (bs, (comp_result c))
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
            let uu___170_2758 = l1 in
            let uu____2759 =
              FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.res_typ in
            {
              FStar_Syntax_Syntax.eff_name =
                (uu___170_2758.FStar_Syntax_Syntax.eff_name);
              FStar_Syntax_Syntax.res_typ = uu____2759;
              FStar_Syntax_Syntax.cflags =
                (uu___170_2758.FStar_Syntax_Syntax.cflags);
              FStar_Syntax_Syntax.comp =
                (fun uu____2762  ->
                   let uu____2763 = l1.FStar_Syntax_Syntax.comp () in
                   FStar_Syntax_Subst.subst_comp s uu____2763)
            } in
          Some (FStar_Util.Inl l2)
      | uu____2772 -> l in
    let rec aux t1 abs_body_lcomp =
      let uu____2810 =
        let uu____2811 =
          let uu____2814 = FStar_Syntax_Subst.compress t1 in
          FStar_All.pipe_left unascribe uu____2814 in
        uu____2811.FStar_Syntax_Syntax.n in
      match uu____2810 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____2852 = aux t2 what in
          (match uu____2852 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____2909 -> ([], t1, abs_body_lcomp) in
    let uu____2921 = aux t None in
    match uu____2921 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____2969 = FStar_Syntax_Subst.open_term' bs t1 in
        (match uu____2969 with
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
                | (None ,uu____3059) -> def
                | (uu____3065,[]) -> def
                | (Some fvs,uu____3072) ->
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
            let uu____3133 = FStar_Syntax_Subst.open_univ_vars_comp uvs c in
            (match uu____3133 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____3149 ->
            let t' = arrow binders c in
            let uu____3156 = FStar_Syntax_Subst.open_univ_vars uvs t' in
            (match uu____3156 with
             | (uvs1,t'1) ->
                 let uu____3167 =
                   let uu____3168 = FStar_Syntax_Subst.compress t'1 in
                   uu____3168.FStar_Syntax_Syntax.n in
                 (match uu____3167 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____3194 -> failwith "Impossible"))
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
    | uu____3231 -> false
let mk_tuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3239 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "tuple%s" uu____3239 in
      let uu____3240 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3240 r
let mk_tuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3248 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mktuple%s" uu____3248 in
      let uu____3249 = FStar_Syntax_Const.psconst t in
      FStar_Ident.set_lid_range uu____3249 r
let is_tuple_data_lid: FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____3256 = mk_tuple_data_lid n1 FStar_Range.dummyRange in
      FStar_Ident.lid_equals f uu____3256
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
    | uu____3274 -> false
let mk_dtuple_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3282 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "dtuple%s" uu____3282 in
      let uu____3283 = let uu____3284 = mod_prefix_dtuple n1 in uu____3284 t in
      FStar_Ident.set_lid_range uu____3283 r
let mk_dtuple_data_lid: Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3294 = FStar_Util.string_of_int n1 in
        FStar_Util.format1 "Mkdtuple%s" uu____3294 in
      let uu____3295 = let uu____3296 = mod_prefix_dtuple n1 in uu____3296 t in
      FStar_Ident.set_lid_range uu____3295 r
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
      let uu____3336 =
        let uu____3337 = pre_typ t in uu____3337.FStar_Syntax_Syntax.n in
      match uu____3336 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3345 -> false
let rec is_constructed_typ:
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3352 =
        let uu____3353 = pre_typ t in uu____3353.FStar_Syntax_Syntax.n in
      match uu____3352 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3356 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____3358) ->
          is_constructed_typ t1 lid
      | uu____3373 -> false
let rec get_tycon:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term option =
  fun t  ->
    let t1 = pre_typ t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar uu____3380 -> Some t1
    | FStar_Syntax_Syntax.Tm_name uu____3381 -> Some t1
    | FStar_Syntax_Syntax.Tm_fvar uu____3382 -> Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____3384) -> get_tycon t2
    | uu____3399 -> None
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
  fun uu____3429  ->
    let u =
      let uu____3433 = FStar_Syntax_Unionfind.univ_fresh () in
      FStar_All.pipe_left (fun _0_27  -> FStar_Syntax_Syntax.U_unif _0_27)
        uu____3433 in
    let uu____3442 =
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u) None
        FStar_Range.dummyRange in
    (uu____3442, u)
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
          let uu____3465 =
            let uu____3468 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos in
            let uu____3469 =
              let uu____3472 =
                let uu____3473 =
                  let uu____3483 =
                    let uu____3485 = FStar_Syntax_Syntax.as_arg phi11 in
                    let uu____3486 =
                      let uu____3488 = FStar_Syntax_Syntax.as_arg phi2 in
                      [uu____3488] in
                    uu____3485 :: uu____3486 in
                  (tand, uu____3483) in
                FStar_Syntax_Syntax.Tm_app uu____3473 in
              FStar_Syntax_Syntax.mk uu____3472 in
            uu____3469 None uu____3468 in
          Some uu____3465
let mk_binop op_t phi1 phi2 =
  let uu____3523 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos in
  let uu____3524 =
    let uu____3527 =
      let uu____3528 =
        let uu____3538 =
          let uu____3540 = FStar_Syntax_Syntax.as_arg phi1 in
          let uu____3541 =
            let uu____3543 = FStar_Syntax_Syntax.as_arg phi2 in [uu____3543] in
          uu____3540 :: uu____3541 in
        (op_t, uu____3538) in
      FStar_Syntax_Syntax.Tm_app uu____3528 in
    FStar_Syntax_Syntax.mk uu____3527 in
  uu____3524 None uu____3523
let mk_neg phi =
  let uu____3564 =
    let uu____3567 =
      let uu____3568 =
        let uu____3578 =
          let uu____3580 = FStar_Syntax_Syntax.as_arg phi in [uu____3580] in
        (t_not, uu____3578) in
      FStar_Syntax_Syntax.Tm_app uu____3568 in
    FStar_Syntax_Syntax.mk uu____3567 in
  uu____3564 None phi.FStar_Syntax_Syntax.pos
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
<<<<<<< HEAD
  let uu____3671 =
    let uu____3674 =
      let uu____3675 =
        let uu____3685 =
          let uu____3687 = FStar_Syntax_Syntax.as_arg e in [uu____3687] in
        (b2t_v, uu____3685) in
      FStar_Syntax_Syntax.Tm_app uu____3675 in
    FStar_Syntax_Syntax.mk uu____3674 in
  uu____3671 None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid
let mk_untyped_eq2 e1 e2 =
  let uu____3711 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos in
  let uu____3712 =
    let uu____3715 =
      let uu____3716 =
        let uu____3726 =
          let uu____3728 = FStar_Syntax_Syntax.as_arg e1 in
          let uu____3729 =
            let uu____3731 = FStar_Syntax_Syntax.as_arg e2 in [uu____3731] in
          uu____3728 :: uu____3729 in
        (teq, uu____3726) in
      FStar_Syntax_Syntax.Tm_app uu____3716 in
    FStar_Syntax_Syntax.mk uu____3715 in
  uu____3712 None uu____3711
=======
  let uu____3651 =
    let uu____3654 =
      let uu____3655 =
        let uu____3665 =
          let uu____3667 = FStar_Syntax_Syntax.as_arg e in [uu____3667] in
        (b2t_v, uu____3665) in
      FStar_Syntax_Syntax.Tm_app uu____3655 in
    FStar_Syntax_Syntax.mk uu____3654 in
  uu____3651 None e.FStar_Syntax_Syntax.pos
let teq: FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid
let mk_untyped_eq2 e1 e2 =
  let uu____3691 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos in
  let uu____3692 =
    let uu____3695 =
      let uu____3696 =
        let uu____3706 =
          let uu____3708 = FStar_Syntax_Syntax.as_arg e1 in
          let uu____3709 =
            let uu____3711 = FStar_Syntax_Syntax.as_arg e2 in [uu____3711] in
          uu____3708 :: uu____3709 in
        (teq, uu____3706) in
      FStar_Syntax_Syntax.Tm_app uu____3696 in
    FStar_Syntax_Syntax.mk uu____3695 in
  uu____3692 None uu____3691
>>>>>>> origin/master
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
<<<<<<< HEAD
          let uu____3754 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____3755 =
            let uu____3758 =
              let uu____3759 =
                let uu____3769 =
                  let uu____3771 = FStar_Syntax_Syntax.iarg t in
                  let uu____3772 =
                    let uu____3774 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____3775 =
                      let uu____3777 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____3777] in
                    uu____3774 :: uu____3775 in
                  uu____3771 :: uu____3772 in
                (eq_inst, uu____3769) in
              FStar_Syntax_Syntax.Tm_app uu____3759 in
            FStar_Syntax_Syntax.mk uu____3758 in
          uu____3755 None uu____3754
=======
          let uu____3734 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos in
          let uu____3735 =
            let uu____3738 =
              let uu____3739 =
                let uu____3749 =
                  let uu____3751 = FStar_Syntax_Syntax.iarg t in
                  let uu____3752 =
                    let uu____3754 = FStar_Syntax_Syntax.as_arg e1 in
                    let uu____3755 =
                      let uu____3757 = FStar_Syntax_Syntax.as_arg e2 in
                      [uu____3757] in
                    uu____3754 :: uu____3755 in
                  uu____3751 :: uu____3752 in
                (eq_inst, uu____3749) in
              FStar_Syntax_Syntax.Tm_app uu____3739 in
            FStar_Syntax_Syntax.mk uu____3738 in
          uu____3735 None uu____3734
>>>>>>> origin/master
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange in
<<<<<<< HEAD
  let uu____3815 =
    let uu____3818 =
      let uu____3819 =
        let uu____3829 =
          let uu____3831 = FStar_Syntax_Syntax.iarg t in
          let uu____3832 =
            let uu____3834 = FStar_Syntax_Syntax.as_arg x in
            let uu____3835 =
              let uu____3837 = FStar_Syntax_Syntax.as_arg t' in [uu____3837] in
            uu____3834 :: uu____3835 in
          uu____3831 :: uu____3832 in
        (t_has_type1, uu____3829) in
      FStar_Syntax_Syntax.Tm_app uu____3819 in
    FStar_Syntax_Syntax.mk uu____3818 in
  uu____3815 None FStar_Range.dummyRange
=======
  let uu____3795 =
    let uu____3798 =
      let uu____3799 =
        let uu____3809 =
          let uu____3811 = FStar_Syntax_Syntax.iarg t in
          let uu____3812 =
            let uu____3814 = FStar_Syntax_Syntax.as_arg x in
            let uu____3815 =
              let uu____3817 = FStar_Syntax_Syntax.as_arg t' in [uu____3817] in
            uu____3814 :: uu____3815 in
          uu____3811 :: uu____3812 in
        (t_has_type1, uu____3809) in
      FStar_Syntax_Syntax.Tm_app uu____3799 in
    FStar_Syntax_Syntax.mk uu____3798 in
  uu____3795 None FStar_Range.dummyRange
>>>>>>> origin/master
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
<<<<<<< HEAD
    let uu____3856 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3863 ->
          (FStar_Syntax_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3870 ->
=======
    let uu____3836 =
      match c0.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total uu____3843 ->
          (FStar_Syntax_Const.effect_Tot_lid, [FStar_Syntax_Syntax.TOTAL])
      | FStar_Syntax_Syntax.GTotal uu____3850 ->
>>>>>>> origin/master
          (FStar_Syntax_Const.effect_GTot_lid,
            [FStar_Syntax_Syntax.SOMETRIVIAL])
      | FStar_Syntax_Syntax.Comp c ->
          ((c.FStar_Syntax_Syntax.effect_name),
            (c.FStar_Syntax_Syntax.flags)) in
<<<<<<< HEAD
    match uu____3856 with
=======
    match uu____3836 with
>>>>>>> origin/master
    | (eff_name,flags) ->
        {
          FStar_Syntax_Syntax.eff_name = eff_name;
          FStar_Syntax_Syntax.res_typ = (comp_result c0);
          FStar_Syntax_Syntax.cflags = flags;
<<<<<<< HEAD
          FStar_Syntax_Syntax.comp = ((fun uu____3883  -> c0))
        }
let mk_forall_aux fa x body =
  let uu____3907 =
    let uu____3910 =
      let uu____3911 =
        let uu____3921 =
          let uu____3923 =
            FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
          let uu____3924 =
            let uu____3926 =
              let uu____3927 =
                let uu____3928 =
                  let uu____3929 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____3929] in
                let uu____3930 =
                  let uu____3937 =
                    let uu____3943 =
                      let uu____3944 = FStar_Syntax_Syntax.mk_Total ktype0 in
                      FStar_All.pipe_left lcomp_of_comp uu____3944 in
                    FStar_Util.Inl uu____3943 in
                  Some uu____3937 in
                abs uu____3928 body uu____3930 in
              FStar_Syntax_Syntax.as_arg uu____3927 in
            [uu____3926] in
          uu____3923 :: uu____3924 in
        (fa, uu____3921) in
      FStar_Syntax_Syntax.Tm_app uu____3911 in
    FStar_Syntax_Syntax.mk uu____3910 in
  uu____3907 None FStar_Range.dummyRange
=======
          FStar_Syntax_Syntax.comp = ((fun uu____3863  -> c0))
        }
let mk_forall_aux fa x body =
  let uu____3887 =
    let uu____3890 =
      let uu____3891 =
        let uu____3901 =
          let uu____3903 =
            FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort in
          let uu____3904 =
            let uu____3906 =
              let uu____3907 =
                let uu____3908 =
                  let uu____3909 = FStar_Syntax_Syntax.mk_binder x in
                  [uu____3909] in
                let uu____3910 =
                  let uu____3917 =
                    let uu____3923 =
                      let uu____3924 = FStar_Syntax_Syntax.mk_Total ktype0 in
                      FStar_All.pipe_left lcomp_of_comp uu____3924 in
                    FStar_Util.Inl uu____3923 in
                  Some uu____3917 in
                abs uu____3908 body uu____3910 in
              FStar_Syntax_Syntax.as_arg uu____3907 in
            [uu____3906] in
          uu____3903 :: uu____3904 in
        (fa, uu____3901) in
      FStar_Syntax_Syntax.Tm_app uu____3891 in
    FStar_Syntax_Syntax.mk uu____3890 in
  uu____3887 None FStar_Range.dummyRange
>>>>>>> origin/master
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
<<<<<<< HEAD
             let uu____3994 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____3994 then f1 else mk_forall_no_univ (fst b) f1) bs f
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____4007 -> true
  | uu____4008 -> false
let if_then_else b t1 t2 =
  let then_branch =
    let uu____4051 =
=======
             let uu____3974 = FStar_Syntax_Syntax.is_null_binder b in
             if uu____3974 then f1 else mk_forall_no_univ (fst b) f1) bs f
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____3987 -> true
  | uu____3988 -> false
let if_then_else b t1 t2 =
  let then_branch =
    let uu____4031 =
>>>>>>> origin/master
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos in
<<<<<<< HEAD
    (uu____4051, None, t1) in
  let else_branch =
    let uu____4074 =
=======
    (uu____4031, None, t1) in
  let else_branch =
    let uu____4054 =
>>>>>>> origin/master
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos in
<<<<<<< HEAD
    (uu____4074, None, t2) in
  let uu____4086 =
    let uu____4087 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4087 in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____4086
=======
    (uu____4054, None, t2) in
  let uu____4066 =
    let uu____4067 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4067 in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____4066
>>>>>>> origin/master
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | QEx of (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  | BaseConn of (FStar_Ident.lident* FStar_Syntax_Syntax.args)
let uu___is_QAll: connective -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | QAll _0 -> true | uu____4160 -> false
=======
    match projectee with | QAll _0 -> true | uu____4143 -> false
>>>>>>> origin/master
let __proj__QAll__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0
let uu___is_QEx: connective -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | QEx _0 -> true | uu____4184 -> false
=======
    match projectee with | QEx _0 -> true | uu____4167 -> false
>>>>>>> origin/master
let __proj__QEx__item___0:
  connective -> (FStar_Syntax_Syntax.binders* qpats* FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0
let uu___is_BaseConn: connective -> Prims.bool =
  fun projectee  ->
<<<<<<< HEAD
    match projectee with | BaseConn _0 -> true | uu____4207 -> false
=======
    match projectee with | BaseConn _0 -> true | uu____4190 -> false
>>>>>>> origin/master
let __proj__BaseConn__item___0:
  connective -> (FStar_Ident.lident* FStar_Syntax_Syntax.args) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0
let destruct_typ_as_formula: FStar_Syntax_Syntax.term -> connective option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1 in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
<<<<<<< HEAD
          (t,FStar_Syntax_Syntax.Meta_monadic uu____4232) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____4242) ->
          unmeta_monadic t
      | uu____4252 -> f2 in
=======
          (t,FStar_Syntax_Syntax.Meta_monadic uu____4215) -> unmeta_monadic t
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic_lift uu____4225) ->
          unmeta_monadic t
      | uu____4235 -> f2 in
>>>>>>> origin/master
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
<<<<<<< HEAD
      let rec aux f2 uu____4297 =
        match uu____4297 with
        | (lid,arity) ->
            let uu____4303 =
              let uu____4313 = unmeta_monadic f2 in head_and_args uu____4313 in
            (match uu____4303 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____4332 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____4332 then Some (BaseConn (lid, args)) else None) in
=======
      let rec aux f2 uu____4280 =
        match uu____4280 with
        | (lid,arity) ->
            let uu____4286 =
              let uu____4296 = unmeta_monadic f2 in head_and_args uu____4296 in
            (match uu____4286 with
             | (t,args) ->
                 let t1 = un_uinst t in
                 let uu____4315 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity) in
                 if uu____4315 then Some (BaseConn (lid, args)) else None) in
>>>>>>> origin/master
      FStar_Util.find_map connectives (aux f1) in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
<<<<<<< HEAD
          let uu____4383 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____4383)
      | uu____4390 ->
          let uu____4391 = FStar_Syntax_Subst.compress t1 in ([], uu____4391) in
=======
          let uu____4366 = FStar_Syntax_Subst.compress t2 in
          (pats, uu____4366)
      | uu____4373 ->
          let uu____4374 = FStar_Syntax_Subst.compress t1 in ([], uu____4374) in
>>>>>>> origin/master
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
      let flat t1 =
<<<<<<< HEAD
        let uu____4433 = head_and_args t1 in
        match uu____4433 with
        | (t2,args) ->
            let uu____4464 = un_uinst t2 in
            let uu____4465 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____4481  ->
                      match uu____4481 with
                      | (t3,imp) ->
                          let uu____4488 = unascribe t3 in (uu____4488, imp))) in
            (uu____4464, uu____4465) in
      let rec aux qopt out t1 =
        let uu____4511 = let uu____4520 = flat t1 in (qopt, uu____4520) in
        match uu____4511 with
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____4535;
                 FStar_Syntax_Syntax.pos = uu____4536;
                 FStar_Syntax_Syntax.vars = uu____4537;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____4540);
                                                             FStar_Syntax_Syntax.tk
                                                               = uu____4541;
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____4542;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____4543;_},uu____4544)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____4605;
                 FStar_Syntax_Syntax.pos = uu____4606;
                 FStar_Syntax_Syntax.vars = uu____4607;_},uu____4608::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____4611);
                  FStar_Syntax_Syntax.tk = uu____4612;
                  FStar_Syntax_Syntax.pos = uu____4613;
                  FStar_Syntax_Syntax.vars = uu____4614;_},uu____4615)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____4683;
               FStar_Syntax_Syntax.pos = uu____4684;
               FStar_Syntax_Syntax.vars = uu____4685;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____4688);
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____4689;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____4690;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____4691;_},uu____4692)::[]))
=======
        let uu____4416 = head_and_args t1 in
        match uu____4416 with
        | (t2,args) ->
            let uu____4447 = un_uinst t2 in
            let uu____4448 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____4464  ->
                      match uu____4464 with
                      | (t3,imp) ->
                          let uu____4471 = unascribe t3 in (uu____4471, imp))) in
            (uu____4447, uu____4448) in
      let rec aux qopt out t1 =
        let uu____4494 = let uu____4503 = flat t1 in (qopt, uu____4503) in
        match uu____4494 with
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____4518;
                 FStar_Syntax_Syntax.pos = uu____4519;
                 FStar_Syntax_Syntax.vars = uu____4520;_},({
                                                             FStar_Syntax_Syntax.n
                                                               =
                                                               FStar_Syntax_Syntax.Tm_abs
                                                               (b::[],t2,uu____4523);
                                                             FStar_Syntax_Syntax.tk
                                                               = uu____4524;
                                                             FStar_Syntax_Syntax.pos
                                                               = uu____4525;
                                                             FStar_Syntax_Syntax.vars
                                                               = uu____4526;_},uu____4527)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (Some
           fa,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
                 FStar_Syntax_Syntax.tk = uu____4588;
                 FStar_Syntax_Syntax.pos = uu____4589;
                 FStar_Syntax_Syntax.vars = uu____4590;_},uu____4591::
               ({
                  FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                    (b::[],t2,uu____4594);
                  FStar_Syntax_Syntax.tk = uu____4595;
                  FStar_Syntax_Syntax.pos = uu____4596;
                  FStar_Syntax_Syntax.vars = uu____4597;_},uu____4598)::[]))
            when is_q fa tc -> aux qopt (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
               FStar_Syntax_Syntax.tk = uu____4666;
               FStar_Syntax_Syntax.pos = uu____4667;
               FStar_Syntax_Syntax.vars = uu____4668;_},({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_abs
                                                             (b::[],t2,uu____4671);
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____4672;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____4673;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____4674;_},uu____4675)::[]))
>>>>>>> origin/master
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
        | (None
           ,({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
<<<<<<< HEAD
               FStar_Syntax_Syntax.tk = uu____4760;
               FStar_Syntax_Syntax.pos = uu____4761;
               FStar_Syntax_Syntax.vars = uu____4762;_},uu____4763::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____4766);
                                                                    FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____4767;
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____4768;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____4769;_},uu____4770)::[]))
=======
               FStar_Syntax_Syntax.tk = uu____4743;
               FStar_Syntax_Syntax.pos = uu____4744;
               FStar_Syntax_Syntax.vars = uu____4745;_},uu____4746::({
                                                                    FStar_Syntax_Syntax.n
                                                                    =
                                                                    FStar_Syntax_Syntax.Tm_abs
                                                                    (b::[],t2,uu____4749);
                                                                    FStar_Syntax_Syntax.tk
                                                                    =
                                                                    uu____4750;
                                                                    FStar_Syntax_Syntax.pos
                                                                    =
                                                                    uu____4751;
                                                                    FStar_Syntax_Syntax.vars
                                                                    =
                                                                    uu____4752;_},uu____4753)::[]))
>>>>>>> origin/master
            when
            is_qlid (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v ->
            aux
              (Some
                 (is_forall
                    (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
              (b :: out) t2
<<<<<<< HEAD
        | (Some b,uu____4846) ->
            let bs = FStar_List.rev out in
            let uu____4864 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____4864 with
             | (bs1,t2) ->
                 let uu____4870 = patterns t2 in
                 (match uu____4870 with
=======
        | (Some b,uu____4829) ->
            let bs = FStar_List.rev out in
            let uu____4847 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____4847 with
             | (bs1,t2) ->
                 let uu____4853 = patterns t2 in
                 (match uu____4853 with
>>>>>>> origin/master
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs1, pats, body))
                      else Some (QEx (bs1, pats, body))))
<<<<<<< HEAD
        | uu____4908 -> None in
      aux None [] t in
    let phi = unmeta_monadic f in
    let uu____4920 = destruct_base_conn phi in
    match uu____4920 with | Some b -> Some b | None  -> destruct_q_conn phi
=======
        | uu____4891 -> None in
      aux None [] t in
    let phi = unmeta_monadic f in
    let uu____4903 = destruct_base_conn phi in
    match uu____4903 with | Some b -> Some b | None  -> destruct_q_conn phi
>>>>>>> origin/master
let action_as_lb:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
<<<<<<< HEAD
        let uu____4931 =
          let uu____4934 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None in
          FStar_Util.Inr uu____4934 in
        let uu____4935 =
          let uu____4936 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____4936 in
        let uu____4939 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn None in
        close_univs_and_mk_letbinding None uu____4931
          a.FStar_Syntax_Syntax.action_univs uu____4935
          FStar_Syntax_Const.effect_Tot_lid uu____4939 in
=======
        let uu____4914 =
          let uu____4917 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None in
          FStar_Util.Inr uu____4917 in
        let uu____4918 =
          let uu____4919 =
            FStar_Syntax_Syntax.mk_Total a.FStar_Syntax_Syntax.action_typ in
          arrow a.FStar_Syntax_Syntax.action_params uu____4919 in
        let uu____4922 =
          abs a.FStar_Syntax_Syntax.action_params
            a.FStar_Syntax_Syntax.action_defn None in
        close_univs_and_mk_letbinding None uu____4914
          a.FStar_Syntax_Syntax.action_univs uu____4918
          FStar_Syntax_Const.effect_Tot_lid uu____4922 in
>>>>>>> origin/master
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
<<<<<<< HEAD
  let uu____4972 =
    let uu____4975 =
      let uu____4976 =
        let uu____4986 =
          let uu____4988 = FStar_Syntax_Syntax.as_arg t in [uu____4988] in
        (reify_, uu____4986) in
      FStar_Syntax_Syntax.Tm_app uu____4976 in
    FStar_Syntax_Syntax.mk uu____4975 in
  uu____4972 None t.FStar_Syntax_Syntax.pos
=======
  let uu____4955 =
    let uu____4958 =
      let uu____4959 =
        let uu____4969 =
          let uu____4971 = FStar_Syntax_Syntax.as_arg t in [uu____4971] in
        (reify_, uu____4969) in
      FStar_Syntax_Syntax.Tm_app uu____4959 in
    FStar_Syntax_Syntax.mk uu____4958 in
  uu____4955 None t.FStar_Syntax_Syntax.pos
>>>>>>> origin/master
let rec delta_qualifier:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
<<<<<<< HEAD
    | FStar_Syntax_Syntax.Tm_delayed uu____5004 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____5026 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____5027 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____5028 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____5044 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____5055 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____5056 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____5057 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5066) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____5071;
           FStar_Syntax_Syntax.index = uu____5072;
           FStar_Syntax_Syntax.sort = t2;_},uu____5074)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____5082) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5088,uu____5089) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5119) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____5134,t2,uu____5136) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____5159,t2) -> delta_qualifier t2
=======
    | FStar_Syntax_Syntax.Tm_delayed uu____4987 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar uu____5009 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_name uu____5010 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_match uu____5011 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_uvar uu____5027 ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_unknown  -> FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type uu____5036 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_constant uu____5037 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_arrow uu____5038 ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____5047) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_refine
        ({ FStar_Syntax_Syntax.ppname = uu____5052;
           FStar_Syntax_Syntax.index = uu____5053;
           FStar_Syntax_Syntax.sort = t2;_},uu____5055)
        -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_meta (t2,uu____5063) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____5069,uu____5070) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_app (t2,uu____5100) -> delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_abs (uu____5115,t2,uu____5117) ->
        delta_qualifier t2
    | FStar_Syntax_Syntax.Tm_let (uu____5140,t2) -> delta_qualifier t2
>>>>>>> origin/master
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
<<<<<<< HEAD
  fun t  -> let uu____5179 = delta_qualifier t in incr_delta_depth uu____5179
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____5183 =
      let uu____5184 = FStar_Syntax_Subst.compress t in
      uu____5184.FStar_Syntax_Syntax.n in
    match uu____5183 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5187 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.list option =
  fun e  ->
    let uu____5195 = let uu____5205 = unmeta e in head_and_args uu____5205 in
    match uu____5195 with
    | (head1,args) ->
        let uu____5224 =
          let uu____5232 =
            let uu____5233 = un_uinst head1 in
            uu____5233.FStar_Syntax_Syntax.n in
          (uu____5232, args) in
        (match uu____5224 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5244) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____5257::(hd1,uu____5259)::(tl1,uu____5261)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____5295 =
               let uu____5299 =
                 let uu____5303 = list_elements tl1 in
                 FStar_Util.must uu____5303 in
               hd1 :: uu____5299 in
             Some uu____5295
         | uu____5312 -> None)
let rec apply_last f l =
  match l with
  | [] -> failwith "apply_last: got empty list"
  | a::[] -> let uu____5343 = f a in [uu____5343]
  | x::xs -> let uu____5347 = apply_last f xs in x :: uu____5347
=======
  fun t  -> let uu____5160 = delta_qualifier t in incr_delta_depth uu____5160
let is_unknown: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____5164 =
      let uu____5165 = FStar_Syntax_Subst.compress t in
      uu____5165.FStar_Syntax_Syntax.n in
    match uu____5164 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____5168 -> false
let rec list_elements:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.list option =
  fun e  ->
    let uu____5176 = let uu____5186 = unmeta e in head_and_args uu____5186 in
    match uu____5176 with
    | (head1,args) ->
        let uu____5205 =
          let uu____5213 =
            let uu____5214 = un_uinst head1 in
            uu____5214.FStar_Syntax_Syntax.n in
          (uu____5213, args) in
        (match uu____5205 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5225) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____5238::(hd1,uu____5240)::(tl1,uu____5242)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____5276 =
               let uu____5280 =
                 let uu____5284 = list_elements tl1 in
                 FStar_Util.must uu____5284 in
               hd1 :: uu____5280 in
             Some uu____5276
         | uu____5293 -> None)
let rec apply_last f l =
  match l with
  | [] -> failwith "apply_last: got empty list"
  | a::[] -> let uu____5324 = f a in [uu____5324]
  | x::xs -> let uu____5328 = apply_last f xs in x :: uu____5328
>>>>>>> origin/master
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
<<<<<<< HEAD
          let uu____5377 =
            let uu____5380 =
              let uu____5381 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____5381 in
            FStar_Syntax_Syntax.mk uu____5380 in
          uu____5377 None rng in
        let cons1 args pos =
          let uu____5399 =
            let uu____5400 =
              let uu____5401 = ctor FStar_Syntax_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5401
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5400 args in
          uu____5399 None pos in
        let nil args pos =
          let uu____5415 =
            let uu____5416 =
              let uu____5417 = ctor FStar_Syntax_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5417
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5416 args in
          uu____5415 None pos in
        let uu____5422 =
          let uu____5423 =
            let uu____5424 = FStar_Syntax_Syntax.iarg typ in [uu____5424] in
          nil uu____5423 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____5427 =
                 let uu____5428 = FStar_Syntax_Syntax.iarg typ in
                 let uu____5429 =
                   let uu____5431 = FStar_Syntax_Syntax.as_arg t in
                   let uu____5432 =
                     let uu____5434 = FStar_Syntax_Syntax.as_arg a in
                     [uu____5434] in
                   uu____5431 :: uu____5432 in
                 uu____5428 :: uu____5429 in
               cons1 uu____5427 t.FStar_Syntax_Syntax.pos) l uu____5422
=======
          let uu____5358 =
            let uu____5361 =
              let uu____5362 =
                FStar_Syntax_Syntax.lid_as_fv l1
                  FStar_Syntax_Syntax.Delta_constant
                  (Some FStar_Syntax_Syntax.Data_ctor) in
              FStar_Syntax_Syntax.Tm_fvar uu____5362 in
            FStar_Syntax_Syntax.mk uu____5361 in
          uu____5358 None rng in
        let cons1 args pos =
          let uu____5380 =
            let uu____5381 =
              let uu____5382 = ctor FStar_Syntax_Const.cons_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5382
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5381 args in
          uu____5380 None pos in
        let nil args pos =
          let uu____5396 =
            let uu____5397 =
              let uu____5398 = ctor FStar_Syntax_Const.nil_lid in
              FStar_Syntax_Syntax.mk_Tm_uinst uu____5398
                [FStar_Syntax_Syntax.U_zero] in
            FStar_Syntax_Syntax.mk_Tm_app uu____5397 args in
          uu____5396 None pos in
        let uu____5403 =
          let uu____5404 =
            let uu____5405 = FStar_Syntax_Syntax.iarg typ in [uu____5405] in
          nil uu____5404 rng in
        FStar_List.fold_right
          (fun t  ->
             fun a  ->
               let uu____5408 =
                 let uu____5409 = FStar_Syntax_Syntax.iarg typ in
                 let uu____5410 =
                   let uu____5412 = FStar_Syntax_Syntax.as_arg t in
                   let uu____5413 =
                     let uu____5415 = FStar_Syntax_Syntax.as_arg a in
                     [uu____5415] in
                   uu____5412 :: uu____5413 in
                 uu____5409 :: uu____5410 in
               cons1 uu____5408 t.FStar_Syntax_Syntax.pos) l uu____5403
>>>>>>> origin/master
let rec eqlist eq1 xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (eq1 x y) && (eqlist eq1 xs1 ys1)
<<<<<<< HEAD
  | uu____5478 -> false
=======
  | uu____5459 -> false
>>>>>>> origin/master
let eqsum e1 e2 x y =
  match (x, y) with
  | (FStar_Util.Inl x1,FStar_Util.Inl y1) -> e1 x1 y1
  | (FStar_Util.Inr x1,FStar_Util.Inr y1) -> e2 x1 y1
<<<<<<< HEAD
  | uu____5551 -> false
let eqprod e1 e2 x y =
  match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt e x y =
  match (x, y) with | (Some x1,Some y1) -> e x1 y1 | uu____5659 -> false
=======
  | uu____5532 -> false
let eqprod e1 e2 x y =
  match (x, y) with | ((x1,x2),(y1,y2)) -> (e1 x1 y1) && (e2 x2 y2)
let eqopt e x y =
  match (x, y) with | (Some x1,Some y1) -> e x1 y1 | uu____5640 -> false
>>>>>>> origin/master
let rec term_eq:
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun t1  ->
    fun t2  ->
<<<<<<< HEAD
      let uu____5752 =
        let uu____5755 =
          let uu____5756 = FStar_Syntax_Subst.compress t1 in
          uu____5756.FStar_Syntax_Syntax.n in
        let uu____5759 =
          let uu____5760 = FStar_Syntax_Subst.compress t2 in
          uu____5760.FStar_Syntax_Syntax.n in
        (uu____5755, uu____5759) in
      match uu____5752 with
=======
      let uu____5733 =
        let uu____5736 =
          let uu____5737 = FStar_Syntax_Subst.compress t1 in
          uu____5737.FStar_Syntax_Syntax.n in
        let uu____5740 =
          let uu____5741 = FStar_Syntax_Subst.compress t2 in
          uu____5741.FStar_Syntax_Syntax.n in
        (uu____5736, uu____5740) in
      match uu____5733 with
>>>>>>> origin/master
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
      | (FStar_Syntax_Syntax.Tm_abs (b1,t11,k1),FStar_Syntax_Syntax.Tm_abs
         (b2,t21,k2)) -> (eqlist binder_eq b1 b2) && (term_eq t11 t21)
      | (FStar_Syntax_Syntax.Tm_app (f1,a1),FStar_Syntax_Syntax.Tm_app
         (f2,a2)) -> (term_eq f1 f2) && (eqlist arg_eq a1 a2)
      | (FStar_Syntax_Syntax.Tm_arrow (b1,c1),FStar_Syntax_Syntax.Tm_arrow
         (b2,c2)) -> (eqlist binder_eq b1 b2) && (comp_eq c1 c2)
      | (FStar_Syntax_Syntax.Tm_refine (b1,t11),FStar_Syntax_Syntax.Tm_refine
         (b2,t21)) -> (FStar_Syntax_Syntax.bv_eq b1 b2) && (term_eq t11 t21)
      | (FStar_Syntax_Syntax.Tm_match (t11,bs1),FStar_Syntax_Syntax.Tm_match
         (t21,bs2)) -> (term_eq t11 t21) && (eqlist branch_eq bs1 bs2)
<<<<<<< HEAD
      | (uu____5965,uu____5966) -> false
=======
      | (uu____5946,uu____5947) -> false
>>>>>>> origin/master
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
<<<<<<< HEAD
      | (uu____6037,uu____6038) -> false
=======
      | (uu____6018,uu____6019) -> false
>>>>>>> origin/master
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
<<<<<<< HEAD
  fun uu____6043  ->
    fun uu____6044  ->
      match (uu____6043, uu____6044) with | ((p1,w1,t1),(p2,w2,t2)) -> false
=======
  fun uu____6024  ->
    fun uu____6025  ->
      match (uu____6024, uu____6025) with | ((p1,w1,t1),(p2,w2,t2)) -> false
>>>>>>> origin/master
let rec bottom_fold:
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun f  ->
    fun t  ->
      let ff = bottom_fold f in
      let tn =
<<<<<<< HEAD
        let uu____6154 = un_uinst t in uu____6154.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____6174 =
              let uu____6184 = ff f1 in
              let uu____6185 =
                FStar_List.map
                  (fun uu____6193  ->
                     match uu____6193 with
                     | (a,q) -> let uu____6200 = ff a in (uu____6200, q))
                  args in
              (uu____6184, uu____6185) in
            FStar_Syntax_Syntax.Tm_app uu____6174
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____6229 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____6229 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____6235 =
                   let uu____6250 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____6250, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____6235)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | uu____6269 -> tn in
      f
        (let uu___171_6270 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.tk = (uu___171_6270.FStar_Syntax_Syntax.tk);
           FStar_Syntax_Syntax.pos = (uu___171_6270.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___171_6270.FStar_Syntax_Syntax.vars)
=======
        let uu____6135 = un_uinst t in uu____6135.FStar_Syntax_Syntax.n in
      let tn1 =
        match tn with
        | FStar_Syntax_Syntax.Tm_app (f1,args) ->
            let uu____6155 =
              let uu____6165 = ff f1 in
              let uu____6166 =
                FStar_List.map
                  (fun uu____6174  ->
                     match uu____6174 with
                     | (a,q) -> let uu____6181 = ff a in (uu____6181, q))
                  args in
              (uu____6165, uu____6166) in
            FStar_Syntax_Syntax.Tm_app uu____6155
        | FStar_Syntax_Syntax.Tm_abs (bs,t1,k) ->
            let uu____6210 = FStar_Syntax_Subst.open_term bs t1 in
            (match uu____6210 with
             | (bs1,t') ->
                 let t'' = ff t' in
                 let uu____6216 =
                   let uu____6231 = FStar_Syntax_Subst.close bs1 t'' in
                   (bs1, uu____6231, k) in
                 FStar_Syntax_Syntax.Tm_abs uu____6216)
        | FStar_Syntax_Syntax.Tm_arrow (bs,k) -> tn
        | uu____6250 -> tn in
      f
        (let uu___168_6251 = t in
         {
           FStar_Syntax_Syntax.n = tn1;
           FStar_Syntax_Syntax.tk = (uu___168_6251.FStar_Syntax_Syntax.tk);
           FStar_Syntax_Syntax.pos = (uu___168_6251.FStar_Syntax_Syntax.pos);
           FStar_Syntax_Syntax.vars =
             (uu___168_6251.FStar_Syntax_Syntax.vars)
>>>>>>> origin/master
         })