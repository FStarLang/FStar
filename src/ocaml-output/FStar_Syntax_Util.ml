open Prims
let qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun id  ->
      let _0_200 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id])
         in
      FStar_Ident.set_lid_range _0_200 id.FStar_Ident.idRange
  
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
  
let arg_of_non_null_binder uu____24 =
  match uu____24 with
  | (b,imp) ->
      let _0_201 = FStar_Syntax_Syntax.bv_to_name b  in (_0_201, imp)
  
let args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____41 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____41
            then []
            else (let _0_202 = arg_of_non_null_binder b  in [_0_202])))
  
let args_of_binders :
  FStar_Syntax_Syntax.binders ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun binders  ->
    let _0_206 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____88 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____88
              then
                let b =
                  let _0_203 =
                    FStar_Syntax_Syntax.new_bv None
                      (Prims.fst b).FStar_Syntax_Syntax.sort
                     in
                  (_0_203, (Prims.snd b))  in
                let _0_204 = arg_of_non_null_binder b  in (b, _0_204)
              else (let _0_205 = arg_of_non_null_binder b  in (b, _0_205))))
       in
    FStar_All.pipe_right _0_206 FStar_List.unzip
  
let name_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____125 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____125
              then
                let uu____128 = b  in
                match uu____128 with
                | (a,imp) ->
                    let b =
                      FStar_Ident.id_of_text
                        (let _0_207 = FStar_Util.string_of_int i  in
                         Prims.strcat "_" _0_207)
                       in
                    let b =
                      {
                        FStar_Syntax_Syntax.ppname = b;
                        FStar_Syntax_Syntax.index = (Prims.parse_int "0");
                        FStar_Syntax_Syntax.sort =
                          (a.FStar_Syntax_Syntax.sort)
                      }  in
                    (b, imp)
              else b))
  
let name_function_binders t =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_arrow (binders,comp) ->
      (FStar_Syntax_Syntax.mk
         (FStar_Syntax_Syntax.Tm_arrow
            (let _0_208 = name_binders binders  in (_0_208, comp)))) None
        t.FStar_Syntax_Syntax.pos
  | uu____174 -> t 
let null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____194  ->
            match uu____194 with
            | (t,imp) ->
                let _0_210 =
                  let _0_209 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left Prims.fst _0_209  in
                (_0_210, imp)))
  
let binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____224  ->
            match uu____224 with
            | (t,imp) ->
                let _0_211 =
                  FStar_Syntax_Syntax.new_bv
                    (Some (t.FStar_Syntax_Syntax.pos)) t
                   in
                (_0_211, imp)))
  
let binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let _0_212 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right _0_212
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
               fun out  ->
                 (FStar_Syntax_Syntax.NT ((Prims.fst f), (Prims.fst a))) ::
                 out) formals actuals []
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
          (fun uu____309  ->
             fun uu____310  ->
               match (uu____309, uu____310) with
               | ((x,uu____320),(y,uu____322)) ->
                   FStar_Syntax_Syntax.NT
                     (let _0_213 = FStar_Syntax_Syntax.bv_to_name y  in
                      (x, _0_213))) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e = FStar_Syntax_Subst.compress e  in
    match e.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e,_)|FStar_Syntax_Syntax.Tm_ascribed
      (e,_,_) -> unmeta e
    | uu____351 -> e
  
let rec univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown 
      |FStar_Syntax_Syntax.U_name _
       |FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  ->
        (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u ->
        let uu____362 = univ_kernel u  in
        (match uu____362 with | (k,n) -> (k, (n + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____369 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____373 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  -> Prims.snd (univ_kernel u) 
let rec compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar _,_)|(_,FStar_Syntax_Syntax.U_bvar _) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____389) ->
          ~- (Prims.parse_int "1")
      | (uu____390,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____391) -> ~- (Prims.parse_int "1")
      | (uu____392,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u1,FStar_Syntax_Syntax.U_name u2) ->
          FStar_String.compare u1.FStar_Ident.idText u2.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____395,FStar_Syntax_Syntax.U_unif
         uu____396) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____399,FStar_Syntax_Syntax.U_name
         uu____400) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u1,FStar_Syntax_Syntax.U_unif u2) ->
          let _0_215 = FStar_Unionfind.uvar_id u1  in
          let _0_214 = FStar_Unionfind.uvar_id u2  in _0_215 - _0_214
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let _0_216 = FStar_List.zip us1 us2  in
               FStar_Util.find_map _0_216
                 (fun uu____433  ->
                    match uu____433 with
                    | (u1,u2) ->
                        let c = compare_univs u1 u2  in
                        if c <> (Prims.parse_int "0") then Some c else None)
                in
             match copt with | None  -> (Prims.parse_int "0") | Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____443,uu____444) ->
          ~- (Prims.parse_int "1")
      | (uu____446,FStar_Syntax_Syntax.U_max uu____447) ->
          (Prims.parse_int "1")
      | uu____449 ->
          let uu____452 = univ_kernel u1  in
          (match uu____452 with
           | (k1,n1) ->
               let uu____457 = univ_kernel u2  in
               (match uu____457 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let _0_217 = compare_univs u1 u2  in _0_217 = (Prims.parse_int "0")
  
let ml_comp :
  FStar_Syntax_Syntax.term -> FStar_Range.range -> FStar_Syntax_Syntax.comp =
  fun t  ->
    fun r  ->
      FStar_Syntax_Syntax.mk_Comp
        (let _0_221 =
           let _0_220 = FStar_Syntax_Syntax.as_arg t  in
           let _0_219 =
             let _0_218 = FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun
                in
             [_0_218]  in
           _0_220 :: _0_219  in
         {
           FStar_Syntax_Syntax.comp_typ_name =
             (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r);
           FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
           FStar_Syntax_Syntax.effect_args = _0_221;
           FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
         })
  
let comp_effect_name c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c -> c.FStar_Syntax_Syntax.comp_typ_name
  | FStar_Syntax_Syntax.Total uu____488 -> FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.GTotal uu____494 ->
      FStar_Syntax_Const.effect_GTot_lid
  
let comp_flags c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____512 -> [FStar_Syntax_Syntax.TOTAL]
  | FStar_Syntax_Syntax.GTotal uu____518 -> [FStar_Syntax_Syntax.SOMETRIVIAL]
  | FStar_Syntax_Syntax.Comp ct -> ct.FStar_Syntax_Syntax.flags 
let comp_set_flags :
  FStar_Syntax_Syntax.comp ->
    FStar_Syntax_Syntax.cflags Prims.list ->
      (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax
  =
  fun c  ->
    fun f  ->
      let comp_to_comp_typ c =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Comp c -> c
        | FStar_Syntax_Syntax.Total (t,u_opt)|FStar_Syntax_Syntax.GTotal
          (t,u_opt) ->
            let _0_225 =
              let _0_222 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
              FStar_Util.dflt [] _0_222  in
            let _0_224 =
              let _0_223 = FStar_Syntax_Syntax.as_arg t  in [_0_223]  in
            {
              FStar_Syntax_Syntax.comp_typ_name = (comp_effect_name c);
              FStar_Syntax_Syntax.comp_univs = _0_225;
              FStar_Syntax_Syntax.effect_args = _0_224;
              FStar_Syntax_Syntax.flags = (comp_flags c)
            }
         in
      let uu___176_557 = c  in
      let _0_226 =
        FStar_Syntax_Syntax.Comp
          (let uu___177_558 = comp_to_comp_typ c  in
           {
             FStar_Syntax_Syntax.comp_typ_name =
               (uu___177_558.FStar_Syntax_Syntax.comp_typ_name);
             FStar_Syntax_Syntax.comp_univs =
               (uu___177_558.FStar_Syntax_Syntax.comp_univs);
             FStar_Syntax_Syntax.effect_args =
               (uu___177_558.FStar_Syntax_Syntax.effect_args);
             FStar_Syntax_Syntax.flags = f
           })
         in
      {
        FStar_Syntax_Syntax.n = _0_226;
        FStar_Syntax_Syntax.tk = (uu___176_557.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___176_557.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___176_557.FStar_Syntax_Syntax.vars)
      }
  
let comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c -> c
    | FStar_Syntax_Syntax.Total (t,Some u)|FStar_Syntax_Syntax.GTotal
      (t,Some u) ->
        let _0_228 = let _0_227 = FStar_Syntax_Syntax.as_arg t  in [_0_227]
           in
        {
          FStar_Syntax_Syntax.comp_typ_name = (comp_effect_name c);
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_args = _0_228;
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu____579 ->
        failwith "Assertion failed: Computation type without universe"
  
let is_named_tot c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c ->
      FStar_Ident.lid_equals c.FStar_Syntax_Syntax.comp_typ_name
        FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.Total uu____592 -> true
  | FStar_Syntax_Syntax.GTotal uu____598 -> false 
let is_total_comp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___164_616  ->
          match uu___164_616 with
          | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  -> true
          | uu____617 -> false))
  
let is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.lcomp_name
       FStar_Syntax_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.lcomp_cflags
         (FStar_Util.for_some
            (fun uu___165_622  ->
               match uu___165_622 with
               | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  ->
                   true
               | uu____623 -> false)))
  
let is_tot_or_gtot_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    ((FStar_Ident.lid_equals c.FStar_Syntax_Syntax.lcomp_name
        FStar_Syntax_Const.effect_Tot_lid)
       ||
       (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.lcomp_name
          FStar_Syntax_Const.effect_GTot_lid))
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.lcomp_cflags
         (FStar_Util.for_some
            (fun uu___166_628  ->
               match uu___166_628 with
               | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  ->
                   true
               | uu____629 -> false)))
  
let is_partial_return c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___167_642  ->
          match uu___167_642 with
          | FStar_Syntax_Syntax.RETURN |FStar_Syntax_Syntax.PARTIAL_RETURN 
              -> true
          | uu____643 -> false))
  
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.lcomp_cflags
      (FStar_Util.for_some
         (fun uu___168_648  ->
            match uu___168_648 with
            | FStar_Syntax_Syntax.RETURN |FStar_Syntax_Syntax.PARTIAL_RETURN 
                -> true
            | uu____649 -> false))
  
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
  | FStar_Syntax_Syntax.Total uu____675 -> true
  | FStar_Syntax_Syntax.GTotal uu____681 -> false
  | FStar_Syntax_Syntax.Comp ct ->
      ((is_total_comp c) ||
         (is_pure_effect ct.FStar_Syntax_Syntax.comp_typ_name))
        ||
        (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___169_689  ->
                 match uu___169_689 with
                 | FStar_Syntax_Syntax.LEMMA  -> true
                 | uu____690 -> false)))
  
let is_ghost_effect : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid l) ||
       (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GHOST_lid l))
      || (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Ghost_lid l)
  
let is_pure_or_ghost_comp c =
  (is_pure_comp c) || (is_ghost_effect (comp_effect_name c)) 
let is_pure_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    ((is_total_lcomp lc) ||
       (is_pure_effect lc.FStar_Syntax_Syntax.lcomp_name))
      ||
      (FStar_All.pipe_right lc.FStar_Syntax_Syntax.lcomp_cflags
         (FStar_Util.for_some
            (fun uu___170_709  ->
               match uu___170_709 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____710 -> false)))
  
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.lcomp_name)
  
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____717 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
    match uu____717 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____718,c) -> is_pure_or_ghost_comp c
    | uu____730 -> true
  
let is_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____734 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
    match uu____734 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____735,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct ->
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_Lemma_lid
         | uu____748 -> false)
    | uu____749 -> false
  
let head_and_args :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax *
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun t  ->
    let t = FStar_Syntax_Subst.compress t  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_app (head,args) -> (head, args)
    | uu____795 -> (t, [])
  
let un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t = FStar_Syntax_Subst.compress t  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t,uu____810) ->
        FStar_Syntax_Subst.compress t
    | uu____815 -> t
  
let is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____819 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n  in
    match uu____819 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____820,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____836)::uu____837 ->
                  let pats' = unmeta pats  in
                  let uu____868 = head_and_args pats'  in
                  (match uu____868 with
                   | (head,uu____879) ->
                       let uu____894 = (un_uinst head).FStar_Syntax_Syntax.n
                          in
                       (match uu____894 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.cons_lid
                        | uu____896 -> false))
              | uu____897 -> false)
         | uu____903 -> false)
    | uu____904 -> false
  
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c ->
      (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.comp_typ_name
         FStar_Syntax_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___171_918  ->
                 match uu___171_918 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____919 -> false)))
  | uu____920 -> false 
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___172_933  ->
          match uu___172_933 with
          | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  -> true
          | uu____934 -> false))
  
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
  | uu____956 -> false 
let rec unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e = FStar_Syntax_Subst.compress e  in
    match e.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e,uu____962,uu____963) -> unascribe e
    | uu____982 -> e
  
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1014,uu____1015) ->
      ascribe t' k
  | uu____1034 ->
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (t, k, None))
        None t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let uu___is_Equal : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1051 -> false
  
let uu___is_NotEqual : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1055 -> false
  
let uu___is_Unknown : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1059 -> false
  
let rec eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let t1 = unascribe t1  in
      let t2 = unascribe t2  in
      let equal_if uu___173_1079 = if uu___173_1079 then Equal else Unknown
         in
      let equal_iff uu___174_1084 = if uu___174_1084 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____1098 -> Unknown
         in
      match ((t1.FStar_Syntax_Syntax.n), (t2.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          equal_if (FStar_Syntax_Syntax.fv_eq f g)
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let _0_229 = eq_tm f g  in
          eq_and _0_229 (fun uu____1115  -> equal_if (eq_univs_list us vs))
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          -> equal_iff (FStar_Const.eq_const c d)
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1119),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1121)) ->
          equal_if (FStar_Unionfind.equivalent u1 u2)
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let _0_230 = eq_tm h1 h2  in
          eq_and _0_230 (fun uu____1181  -> eq_args args1 args2)
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v) ->
          equal_if (eq_univs u v)
      | (FStar_Syntax_Syntax.Tm_meta (t1,uu____1185),uu____1186) ->
          eq_tm t1 t2
      | (uu____1191,FStar_Syntax_Syntax.Tm_meta (t2,uu____1193)) ->
          eq_tm t1 t2
      | uu____1198 -> Unknown

and eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1222)::a1,(b,uu____1225)::b1) ->
          let uu____1263 = eq_tm a b  in
          (match uu____1263 with
           | Equal  -> eq_args a1 b1
           | uu____1264 -> Unknown)
      | uu____1265 -> Unknown

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
    let t = FStar_Syntax_Subst.compress t  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1279) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1285,uu____1286) -> unrefine t
    | uu____1305 -> t
  
let rec is_unit : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1309 = (unrefine t).FStar_Syntax_Syntax.n  in
    match uu____1309 with
    | FStar_Syntax_Syntax.Tm_type uu____1310 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t,uu____1313) -> is_unit t
    | uu____1318 -> false
  
let is_fun : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1322 = (FStar_Syntax_Subst.compress e).FStar_Syntax_Syntax.n
       in
    match uu____1322 with
    | FStar_Syntax_Syntax.Tm_abs uu____1323 -> true
    | uu____1338 -> false
  
let is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1342 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
       in
    match uu____1342 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1343 -> true
    | uu____1351 -> false
  
let rec pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t = FStar_Syntax_Subst.compress t  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1357) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t,uu____1363,uu____1364) -> pre_typ t
    | uu____1383 -> t
  
let destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list
        Prims.option
  =
  fun typ  ->
    fun lid  ->
      let typ = FStar_Syntax_Subst.compress typ  in
      let uu____1397 = (un_uinst typ).FStar_Syntax_Syntax.n  in
      match uu____1397 with
      | FStar_Syntax_Syntax.Tm_app (head,args) ->
          let head = un_uinst head  in
          (match head.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____1433 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____1449 -> None
  
let lids_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.list =
  fun se  ->
    match se with
    | FStar_Syntax_Syntax.Sig_let (_,_,lids,_,_)
      |FStar_Syntax_Syntax.Sig_bundle (_,_,lids,_) -> lids
    | FStar_Syntax_Syntax.Sig_inductive_typ (lid,_,_,_,_,_,_,_)
      |FStar_Syntax_Syntax.Sig_effect_abbrev (lid,_,_,_,_,_,_)
       |FStar_Syntax_Syntax.Sig_datacon (lid,_,_,_,_,_,_,_)
        |FStar_Syntax_Syntax.Sig_declare_typ (lid,_,_,_,_)
         |FStar_Syntax_Syntax.Sig_assume (lid,_,_,_)
        -> [lid]
    | FStar_Syntax_Syntax.Sig_new_effect_for_free (n,_)
      |FStar_Syntax_Syntax.Sig_new_effect (n,_) ->
        [n.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect _
      |FStar_Syntax_Syntax.Sig_pragma _|FStar_Syntax_Syntax.Sig_main _ -> []
  
let lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.option =
  fun se  ->
    match lids_of_sigelt se with | l::[] -> Some l | uu____1526 -> None
  
let quals_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun x  ->
    match x with
    | FStar_Syntax_Syntax.Sig_bundle (_,quals,_,_)
      |FStar_Syntax_Syntax.Sig_inductive_typ (_,_,_,_,_,_,quals,_)
       |FStar_Syntax_Syntax.Sig_effect_abbrev (_,_,_,_,quals,_,_)
        |FStar_Syntax_Syntax.Sig_datacon (_,_,_,_,_,quals,_,_)
         |FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,quals,_)
          |FStar_Syntax_Syntax.Sig_assume (_,_,quals,_)
           |FStar_Syntax_Syntax.Sig_let (_,_,_,quals,_)
            |FStar_Syntax_Syntax.Sig_new_effect
             ({ FStar_Syntax_Syntax.qualifiers = quals;
                FStar_Syntax_Syntax.cattributes = _;
                FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _;
                FStar_Syntax_Syntax.binders = _;
                FStar_Syntax_Syntax.signature = _;
                FStar_Syntax_Syntax.ret_wp = _;
                FStar_Syntax_Syntax.bind_wp = _;
                FStar_Syntax_Syntax.if_then_else = _;
                FStar_Syntax_Syntax.ite_wp = _;
                FStar_Syntax_Syntax.stronger = _;
                FStar_Syntax_Syntax.close_wp = _;
                FStar_Syntax_Syntax.assert_p = _;
                FStar_Syntax_Syntax.assume_p = _;
                FStar_Syntax_Syntax.null_wp = _;
                FStar_Syntax_Syntax.trivial = _;
                FStar_Syntax_Syntax.repr = _;
                FStar_Syntax_Syntax.return_repr = _;
                FStar_Syntax_Syntax.bind_repr = _;
                FStar_Syntax_Syntax.actions = _;_},_)
             |FStar_Syntax_Syntax.Sig_new_effect_for_free
             ({ FStar_Syntax_Syntax.qualifiers = quals;
                FStar_Syntax_Syntax.cattributes = _;
                FStar_Syntax_Syntax.mname = _; FStar_Syntax_Syntax.univs = _;
                FStar_Syntax_Syntax.binders = _;
                FStar_Syntax_Syntax.signature = _;
                FStar_Syntax_Syntax.ret_wp = _;
                FStar_Syntax_Syntax.bind_wp = _;
                FStar_Syntax_Syntax.if_then_else = _;
                FStar_Syntax_Syntax.ite_wp = _;
                FStar_Syntax_Syntax.stronger = _;
                FStar_Syntax_Syntax.close_wp = _;
                FStar_Syntax_Syntax.assert_p = _;
                FStar_Syntax_Syntax.assume_p = _;
                FStar_Syntax_Syntax.null_wp = _;
                FStar_Syntax_Syntax.trivial = _;
                FStar_Syntax_Syntax.repr = _;
                FStar_Syntax_Syntax.return_repr = _;
                FStar_Syntax_Syntax.bind_repr = _;
                FStar_Syntax_Syntax.actions = _;_},_)
        -> quals
    | FStar_Syntax_Syntax.Sig_sub_effect (_,_)
      |FStar_Syntax_Syntax.Sig_pragma (_,_)|FStar_Syntax_Syntax.Sig_main
       (_,_) -> []
  
let range_of_sigelt : FStar_Syntax_Syntax.sigelt -> FStar_Range.range =
  fun x  ->
    match x with
    | FStar_Syntax_Syntax.Sig_bundle (_,_,_,r)
      |FStar_Syntax_Syntax.Sig_inductive_typ (_,_,_,_,_,_,_,r)
       |FStar_Syntax_Syntax.Sig_effect_abbrev (_,_,_,_,_,_,r)
        |FStar_Syntax_Syntax.Sig_datacon (_,_,_,_,_,_,_,r)
         |FStar_Syntax_Syntax.Sig_declare_typ (_,_,_,_,r)
          |FStar_Syntax_Syntax.Sig_assume (_,_,_,r)
           |FStar_Syntax_Syntax.Sig_let (_,r,_,_,_)
            |FStar_Syntax_Syntax.Sig_main (_,r)
             |FStar_Syntax_Syntax.Sig_pragma (_,r)
              |FStar_Syntax_Syntax.Sig_new_effect (_,r)
               |FStar_Syntax_Syntax.Sig_new_effect_for_free (_,r)
                |FStar_Syntax_Syntax.Sig_sub_effect (_,r)
        -> r
  
let range_of_lb uu___175_1709 =
  match uu___175_1709 with
  | (FStar_Util.Inl x,uu____1716,uu____1717) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____1721,uu____1722) -> FStar_Ident.range_of_lid l 
let range_of_arg uu____1739 =
  match uu____1739 with | (hd,uu____1745) -> hd.FStar_Syntax_Syntax.pos 
let range_of_args args r =
  FStar_All.pipe_right args
    (FStar_List.fold_left
       (fun r  -> fun a  -> FStar_Range.union_ranges r (range_of_arg a)) r)
  
let mk_app f args =
  let r = range_of_args args f.FStar_Syntax_Syntax.pos  in
  FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app (f, args)) None r 
let mk_data l args =
  match args with
  | [] ->
      (FStar_Syntax_Syntax.mk
         (FStar_Syntax_Syntax.Tm_meta
            (let _0_231 =
               FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                 (Some FStar_Syntax_Syntax.Data_ctor)
                in
             (_0_231,
               (FStar_Syntax_Syntax.Meta_desugared
                  FStar_Syntax_Syntax.Data_app))))) None
        (FStar_Ident.range_of_lid l)
  | uu____1867 ->
      let e =
        let _0_232 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor)
           in
        mk_app _0_232 args  in
      FStar_Syntax_Syntax.mk
        (FStar_Syntax_Syntax.Tm_meta
           (e,
             (FStar_Syntax_Syntax.Meta_desugared FStar_Syntax_Syntax.Data_app)))
        None e.FStar_Syntax_Syntax.pos
  
let mangle_field_name : FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    FStar_Ident.mk_ident
      ((Prims.strcat "^fname^" x.FStar_Ident.idText),
        (x.FStar_Ident.idRange))
  
let unmangle_field_name : FStar_Ident.ident -> FStar_Ident.ident =
  fun x  ->
    if FStar_Util.starts_with x.FStar_Ident.idText "^fname^"
    then
      FStar_Ident.mk_ident
        (let _0_233 =
           FStar_Util.substring_from x.FStar_Ident.idText
             (Prims.parse_int "7")
            in
         (_0_233, (x.FStar_Ident.idRange)))
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
          let uu____1920 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____1920
          then
            FStar_Ident.mk_ident
              (let _0_236 =
                 let _0_234 = FStar_Util.string_of_int i  in
                 Prims.strcat "_" _0_234  in
               let _0_235 = FStar_Syntax_Syntax.range_of_bv x  in
               (_0_236, _0_235))
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___178_1923 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___178_1923.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___178_1923.FStar_Syntax_Syntax.sort)
          }  in
        let _0_237 = mk_field_projector_name_from_ident lid nm  in
        (_0_237, y)
  
let set_uvar uv t =
  let uu____1940 = FStar_Unionfind.find uv  in
  match uu____1940 with
  | FStar_Syntax_Syntax.Fixed uu____1943 ->
      failwith
        (let _0_239 =
           let _0_238 = FStar_Unionfind.uvar_id uv  in
           FStar_All.pipe_left FStar_Util.string_of_int _0_238  in
         FStar_Util.format1 "Changing a fixed uvar! ?%s\n" _0_239)
  | uu____1945 -> FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed t) 
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
      | uu____1992 -> q1 = q2
  
let abs :
  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident *
                                   FStar_Syntax_Syntax.cflags Prims.list))
        FStar_Util.either Prims.option -> FStar_Syntax_Syntax.term
  =
  fun bs  ->
    fun t  ->
      fun lopt  ->
        if (FStar_List.length bs) = (Prims.parse_int "0")
        then t
        else
          (let close_lopt lopt =
             match lopt with
             | None |Some (FStar_Util.Inr _) -> lopt
             | Some (FStar_Util.Inl lc) ->
                 Some (FStar_Util.Inl (FStar_Syntax_Subst.close_lcomp bs lc))
              in
           match bs with
           | [] -> t
           | uu____2088 ->
               let body =
                 FStar_Syntax_Subst.compress (FStar_Syntax_Subst.close bs t)
                  in
               (match ((body.FStar_Syntax_Syntax.n), lopt) with
                | (FStar_Syntax_Syntax.Tm_abs (bs',t,lopt'),None ) ->
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_abs
                          (let _0_242 =
                             let _0_240 = FStar_Syntax_Subst.close_binders bs
                                in
                             FStar_List.append _0_240 bs'  in
                           let _0_241 = close_lopt lopt'  in
                           (_0_242, t, _0_241)))) None
                      t.FStar_Syntax_Syntax.pos
                | uu____2156 ->
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_abs
                          (let _0_244 = FStar_Syntax_Subst.close_binders bs
                              in
                           let _0_243 = close_lopt lopt  in
                           (_0_244, body, _0_243)))) None
                      t.FStar_Syntax_Syntax.pos))
  
let arrow :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      match bs with
      | [] -> failwith "Arrow with empty binders"
      | uu____2187 ->
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_arrow
                (let _0_246 = FStar_Syntax_Subst.close_binders bs  in
                 let _0_245 = FStar_Syntax_Subst.close_comp bs c  in
                 (_0_246, _0_245)))) None c.FStar_Syntax_Syntax.pos
  
let maybe_tot_arrow :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun t  ->
      match bs with
      | [] -> t
      | uu____2204 ->
          let c = FStar_Syntax_Syntax.mk_Total t  in
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_arrow
                (let _0_248 = FStar_Syntax_Subst.close_binders bs  in
                 let _0_247 = FStar_Syntax_Subst.close_comp bs c  in
                 (_0_248, _0_247)))) None c.FStar_Syntax_Syntax.pos
  
let flat_arrow :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____2223 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
         in
      match uu____2223 with
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          (match c.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2241) ->
               let uu____2248 =
                 (FStar_Syntax_Subst.compress tres).FStar_Syntax_Syntax.n  in
               (match uu____2248 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let _0_249 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_arrow
                          ((FStar_List.append bs bs'), c'))) _0_249
                      t.FStar_Syntax_Syntax.pos
                | uu____2281 -> t)
           | uu____2282 -> t)
      | uu____2283 -> t
  
let refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let _0_255 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk  in
      let _0_254 =
        let _0_253 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges _0_253 t.FStar_Syntax_Syntax.pos  in
      (FStar_Syntax_Syntax.mk
         (FStar_Syntax_Syntax.Tm_refine
            (let _0_252 =
               let _0_251 =
                 let _0_250 = FStar_Syntax_Syntax.mk_binder b  in [_0_250]
                  in
               FStar_Syntax_Subst.close _0_251 t  in
             (b, _0_252)))) _0_255 _0_254
  
let branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let tot_or_gtot_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,_)|FStar_Syntax_Syntax.GTotal (t,_) -> t
  | uu____2332 -> failwith "Expected a Tot or GTot computation" 
let rec arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k = FStar_Syntax_Subst.compress k  in
    match k.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____2361 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____2361 with
         | (bs,c) ->
             let uu____2371 = is_tot_or_gtot_comp c  in
             if uu____2371
             then
               let uu____2377 = arrow_formals_comp (tot_or_gtot_result c)  in
               (match uu____2377 with
                | (bs',k) -> ((FStar_List.append bs bs'), k))
             else (bs, c))
    | uu____2402 ->
        let _0_256 = FStar_Syntax_Syntax.mk_Total k  in ([], _0_256)
  
let abs_formals :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.term *
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident *
                                   FStar_Syntax_Syntax.cflags Prims.list))
      FStar_Util.either Prims.option)
  =
  fun t  ->
    let subst_lcomp_opt s l =
      match l with
      | Some (FStar_Util.Inl l) ->
          let l =
            let uu___179_2463 = l  in
            let _0_260 =
              FStar_List.map
                (fun uu____2468  ->
                   match uu____2468 with
                   | (t,imp) ->
                       let _0_257 = FStar_Syntax_Subst.subst s t  in
                       (_0_257, imp)) l.FStar_Syntax_Syntax.lcomp_indices
               in
            let _0_259 =
              FStar_Syntax_Subst.subst s l.FStar_Syntax_Syntax.lcomp_res_typ
               in
            {
              FStar_Syntax_Syntax.lcomp_name =
                (uu___179_2463.FStar_Syntax_Syntax.lcomp_name);
              FStar_Syntax_Syntax.lcomp_univs =
                (uu___179_2463.FStar_Syntax_Syntax.lcomp_univs);
              FStar_Syntax_Syntax.lcomp_indices = _0_260;
              FStar_Syntax_Syntax.lcomp_res_typ = _0_259;
              FStar_Syntax_Syntax.lcomp_cflags =
                (uu___179_2463.FStar_Syntax_Syntax.lcomp_cflags);
              FStar_Syntax_Syntax.lcomp_as_comp =
                (fun uu____2475  ->
                   let _0_258 = l.FStar_Syntax_Syntax.lcomp_as_comp ()  in
                   FStar_Syntax_Subst.subst_comp s _0_258)
            }  in
          Some (FStar_Util.Inl l)
      | uu____2484 -> l  in
    let rec aux t abs_body_lcomp =
      let uu____2522 =
        (let _0_261 = FStar_Syntax_Subst.compress t  in
         FStar_All.pipe_left unascribe _0_261).FStar_Syntax_Syntax.n
         in
      match uu____2522 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t,what) ->
          let uu____2560 = aux t what  in
          (match uu____2560 with
           | (bs',t,what) -> ((FStar_List.append bs bs'), t, what))
      | uu____2617 -> ([], t, abs_body_lcomp)  in
    let uu____2629 = aux t None  in
    match uu____2629 with
    | (bs,t,abs_body_lcomp) ->
        let uu____2677 = FStar_Syntax_Subst.open_term' bs t  in
        (match uu____2677 with
         | (bs,t,opening) ->
             let abs_body_lcomp = subst_lcomp_opt opening abs_body_lcomp  in
             (bs, t, abs_body_lcomp))
  
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
              let def =
                match (recs, univ_vars) with
                | (None ,_)|(_,[]) -> def
                | (Some fvs,uu____2777) ->
                    let universes =
                      FStar_All.pipe_right univ_vars
                        (FStar_List.map
                           (fun _0_262  -> FStar_Syntax_Syntax.U_name _0_262))
                       in
                    let inst =
                      FStar_All.pipe_right fvs
                        (FStar_List.map
                           (fun fv  ->
                              (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
                                universes)))
                       in
                    FStar_Syntax_InstFV.instantiate inst def
                 in
              let typ = FStar_Syntax_Subst.close_univ_vars univ_vars typ  in
              let def = FStar_Syntax_Subst.close_univ_vars univ_vars def  in
              mk_letbinding lbname univ_vars typ eff def
  
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
            let uu____2838 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____2838 with | (uvs,c) -> (uvs, [], c))
        | uu____2854 ->
            let t' = arrow binders c  in
            let uu____2859 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____2859 with
             | (uvs,t') ->
                 let uu____2870 =
                   (FStar_Syntax_Subst.compress t').FStar_Syntax_Syntax.n  in
                 (match uu____2870 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                      (uvs, binders, c)
                  | uu____2894 -> failwith "Impossible"))
  
let is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.starts_with
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          "Prims.tuple"
    | uu____2909 -> false
  
let mk_tuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n  ->
    fun r  ->
      let t =
        let _0_263 = FStar_Util.string_of_int n  in
        FStar_Util.format1 "tuple%s" _0_263  in
      let _0_264 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range _0_264 r
  
let mk_tuple_data_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n  ->
    fun r  ->
      let t =
        let _0_265 = FStar_Util.string_of_int n  in
        FStar_Util.format1 "Mktuple%s" _0_265  in
      let _0_266 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range _0_266 r
  
let is_tuple_data_lid : FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n  ->
      let _0_267 = mk_tuple_data_lid n FStar_Range.dummyRange  in
      FStar_Ident.lid_equals f _0_267
  
let is_tuple_data_lid' : FStar_Ident.lident -> Prims.bool =
  fun f  ->
    (f.FStar_Ident.nsstr = "Prims") &&
      (FStar_Util.starts_with (f.FStar_Ident.ident).FStar_Ident.idText
         "Mktuple")
  
let is_tuple_constructor_lid : FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    FStar_Util.starts_with (FStar_Ident.text_of_lid lid) "Prims.tuple"
  
let is_dtuple_constructor_lid : FStar_Ident.lident -> Prims.bool =
  fun lid  ->
    (lid.FStar_Ident.nsstr = "Prims") &&
      (FStar_Util.starts_with (lid.FStar_Ident.ident).FStar_Ident.idText
         "Prims.dtuple")
  
let is_dtuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        is_dtuple_constructor_lid
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
    | uu____2947 -> false
  
let mk_dtuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n  ->
    fun r  ->
      let t =
        let _0_268 = FStar_Util.string_of_int n  in
        FStar_Util.format1 "dtuple%s" _0_268  in
      let _0_269 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range _0_269 r
  
let mk_dtuple_data_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n  ->
    fun r  ->
      let t =
        let _0_270 = FStar_Util.string_of_int n  in
        FStar_Util.format1 "Mkdtuple%s" _0_270  in
      let _0_271 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range _0_271 r
  
let is_dtuple_data_lid' : FStar_Ident.lident -> Prims.bool =
  fun f  -> FStar_Util.starts_with (FStar_Ident.text_of_lid f) "Mkdtuple" 
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
      let uu____2999 = (pre_typ t).FStar_Syntax_Syntax.n  in
      match uu____2999 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3005 -> false
  
let rec is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3012 = (pre_typ t).FStar_Syntax_Syntax.n  in
      match uu____3012 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3013 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t,uu____3015) -> is_constructed_typ t lid
      | uu____3030 -> false
  
let rec get_tycon :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.option =
  fun t  ->
    let t = pre_typ t  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar _
      |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ -> 
        Some t
    | FStar_Syntax_Syntax.Tm_app (t,uu____3041) -> get_tycon t
    | uu____3056 -> None
  
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
  fun uu____3086  ->
    let u =
      let _0_273 = FStar_Unionfind.fresh None  in
      FStar_All.pipe_left (fun _0_272  -> FStar_Syntax_Syntax.U_unif _0_272)
        _0_273
       in
    let _0_274 =
      (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)) None
        FStar_Range.dummyRange
       in
    (_0_274, u)
  
let type_at_u :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax
  =
  fun u  ->
    (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)) None
      FStar_Range.dummyRange
  
let kt_kt : FStar_Syntax_Syntax.term =
  FStar_Syntax_Const.kunary ktype0 ktype0 
let kt_kt_kt : FStar_Syntax_Syntax.term =
  FStar_Syntax_Const.kbin ktype0 ktype0 ktype0 
let fvar_const : FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant None
  
let tand : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.and_lid 
let tor : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.or_lid 
let timp : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.imp_lid 
let tiff : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.iff_lid 
let t_bool : FStar_Syntax_Syntax.term =
  fvar_const FStar_Syntax_Const.bool_lid 
let t_false : FStar_Syntax_Syntax.term =
  fvar_const FStar_Syntax_Const.false_lid 
let t_true : FStar_Syntax_Syntax.term =
  fvar_const FStar_Syntax_Const.true_lid 
let b2t_v : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.b2t_lid 
let t_not : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.not_lid 
let mk_conj_opt :
  FStar_Syntax_Syntax.term Prims.option ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax Prims.option
  =
  fun phi1  ->
    fun phi2  ->
      match phi1 with
      | None  -> Some phi2
      | Some phi1 ->
          Some
            (let _0_279 =
               FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
                 phi2.FStar_Syntax_Syntax.pos
                in
             (FStar_Syntax_Syntax.mk
                (FStar_Syntax_Syntax.Tm_app
                   (let _0_278 =
                      let _0_277 = FStar_Syntax_Syntax.as_arg phi1  in
                      let _0_276 =
                        let _0_275 = FStar_Syntax_Syntax.as_arg phi2  in
                        [_0_275]  in
                      _0_277 :: _0_276  in
                    (tand, _0_278)))) None _0_279)
  
let mk_binop op_t phi1 phi2 =
  let _0_284 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos
     in
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_app
        (let _0_283 =
           let _0_282 = FStar_Syntax_Syntax.as_arg phi1  in
           let _0_281 =
             let _0_280 = FStar_Syntax_Syntax.as_arg phi2  in [_0_280]  in
           _0_282 :: _0_281  in
         (op_t, _0_283)))) None _0_284
  
let mk_neg phi =
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_app
        (let _0_286 =
           let _0_285 = FStar_Syntax_Syntax.as_arg phi  in [_0_285]  in
         (t_not, _0_286)))) None phi.FStar_Syntax_Syntax.pos
  
let mk_conj phi1 phi2 = mk_binop tand phi1 phi2 
let mk_conj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] ->
        FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
          FStar_Syntax_Syntax.Delta_constant None
    | hd::tl -> FStar_List.fold_right mk_conj tl hd
  
let mk_disj phi1 phi2 = mk_binop tor phi1 phi2 
let mk_disj_l :
  FStar_Syntax_Syntax.term Prims.list -> FStar_Syntax_Syntax.term =
  fun phi  ->
    match phi with
    | [] -> t_false
    | hd::tl -> FStar_List.fold_right mk_disj tl hd
  
let mk_imp :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun phi1  ->
    fun phi2  ->
      let uu____3249 =
        (FStar_Syntax_Subst.compress phi1).FStar_Syntax_Syntax.n  in
      match uu____3249 with
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid ->
          t_true
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
          phi2
      | uu____3252 ->
          let uu____3253 =
            (FStar_Syntax_Subst.compress phi2).FStar_Syntax_Syntax.n  in
          (match uu____3253 with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid tc
                    FStar_Syntax_Const.false_lid)
               -> phi2
           | uu____3255 -> mk_binop timp phi1 phi2)
  
let mk_iff phi1 phi2 = mk_binop tiff phi1 phi2 
let b2t e =
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_app
        (let _0_288 = let _0_287 = FStar_Syntax_Syntax.as_arg e  in [_0_287]
            in
         (b2t_v, _0_288)))) None e.FStar_Syntax_Syntax.pos
  
let teq : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid 
let mk_untyped_eq2 e1 e2 =
  let _0_293 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos
     in
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_app
        (let _0_292 =
           let _0_291 = FStar_Syntax_Syntax.as_arg e1  in
           let _0_290 =
             let _0_289 = FStar_Syntax_Syntax.as_arg e2  in [_0_289]  in
           _0_291 :: _0_290  in
         (teq, _0_292)))) None _0_293
  
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
          let _0_300 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          (FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_app
                (let _0_299 =
                   let _0_298 = FStar_Syntax_Syntax.iarg t  in
                   let _0_297 =
                     let _0_296 = FStar_Syntax_Syntax.as_arg e1  in
                     let _0_295 =
                       let _0_294 = FStar_Syntax_Syntax.as_arg e2  in
                       [_0_294]  in
                     _0_296 :: _0_295  in
                   _0_298 :: _0_297  in
                 (eq_inst, _0_299)))) None _0_300
  
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid  in
  let t_has_type =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange
     in
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_app
        (let _0_306 =
           let _0_305 = FStar_Syntax_Syntax.iarg t  in
           let _0_304 =
             let _0_303 = FStar_Syntax_Syntax.as_arg x  in
             let _0_302 =
               let _0_301 = FStar_Syntax_Syntax.as_arg t'  in [_0_301]  in
             _0_303 :: _0_302  in
           _0_305 :: _0_304  in
         (t_has_type, _0_306)))) None FStar_Range.dummyRange
  
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
  
let lc_tot_type0 : FStar_Syntax_Syntax.lcomp =
  {
    FStar_Syntax_Syntax.lcomp_name = FStar_Syntax_Const.effect_Tot_lid;
    FStar_Syntax_Syntax.lcomp_univs =
      [FStar_Syntax_Syntax.U_succ FStar_Syntax_Syntax.U_zero];
    FStar_Syntax_Syntax.lcomp_indices = [];
    FStar_Syntax_Syntax.lcomp_res_typ = ktype0;
    FStar_Syntax_Syntax.lcomp_cflags = [FStar_Syntax_Syntax.TOTAL];
    FStar_Syntax_Syntax.lcomp_as_comp =
      (fun uu____3376  -> FStar_Syntax_Syntax.mk_Total ktype0)
  } 
let mk_forall :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun x  ->
    fun body  ->
      (FStar_Syntax_Syntax.mk
         (FStar_Syntax_Syntax.Tm_app
            (let _0_312 =
               let _0_311 =
                 FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
               let _0_310 =
                 let _0_309 =
                   FStar_Syntax_Syntax.as_arg
                     (let _0_308 =
                        let _0_307 = FStar_Syntax_Syntax.mk_binder x  in
                        [_0_307]  in
                      abs _0_308 body (Some (FStar_Util.Inl lc_tot_type0)))
                    in
                 [_0_309]  in
               _0_311 :: _0_310  in
             (tforall, _0_312)))) None FStar_Range.dummyRange
  
let rec close_forall :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f  ->
             let uu____3410 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____3410 then f else mk_forall (Prims.fst b) f) bs f
  
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____3423 -> true
  | uu____3424 -> false 
let if_then_else b t1 t2 =
  let then_branch =
    let _0_313 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos
       in
    (_0_313, None, t1)  in
  let else_branch =
    let _0_314 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos
       in
    (_0_314, None, t2)  in
  let _0_316 =
    let _0_315 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos
       in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos _0_315  in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    _0_316
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let uu___is_QAll : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____3568 -> false
  
let __proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let uu___is_QEx : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____3592 -> false
  
let __proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let uu___is_BaseConn : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____3615 -> false
  
let __proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0 
let destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective Prims.option =
  fun f  ->
    let rec unmeta_monadic f =
      let f = FStar_Syntax_Subst.compress f  in
      match f.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_monadic _)
        |FStar_Syntax_Syntax.Tm_meta
        (t,FStar_Syntax_Syntax.Meta_monadic_lift _) -> unmeta_monadic t
      | uu____3650 -> f  in
    let destruct_base_conn f =
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
      let rec aux f uu____3695 =
        match uu____3695 with
        | (lid,arity) ->
            let uu____3701 = head_and_args (unmeta_monadic f)  in
            (match uu____3701 with
             | (t,args) ->
                 let t = un_uinst t  in
                 let uu____3729 =
                   (is_constructor t lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____3729 then Some (BaseConn (lid, args)) else None)
         in
      FStar_Util.find_map connectives (aux f)  in
    let patterns t =
      let t = FStar_Syntax_Subst.compress t  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern pats)
          -> let _0_317 = FStar_Syntax_Subst.compress t  in (pats, _0_317)
      | uu____3786 ->
          let _0_318 = FStar_Syntax_Subst.compress t  in ([], _0_318)
       in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t =
        let uu____3828 = head_and_args t  in
        match uu____3828 with
        | (t,args) ->
            let _0_321 = un_uinst t  in
            let _0_320 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____3874  ->
                      match uu____3874 with
                      | (t,imp) -> let _0_319 = unascribe t  in (_0_319, imp)))
               in
            (_0_321, _0_320)
         in
      let rec aux qopt out t =
        let uu____3900 = let _0_322 = flat t  in (qopt, _0_322)  in
        match uu____3900 with
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
        | (Some b,uu____4162) ->
            let bs = FStar_List.rev out  in
            let uu____4180 = FStar_Syntax_Subst.open_term bs t  in
            (match uu____4180 with
             | (bs,t) ->
                 let uu____4186 = patterns t  in
                 (match uu____4186 with
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs, pats, body))
                      else Some (QEx (bs, pats, body))))
        | uu____4224 -> None  in
      aux None [] t  in
    let phi = unmeta_monadic f  in
    let uu____4236 = destruct_base_conn phi  in
    match uu____4236 with | Some b -> Some b | None  -> destruct_q_conn phi
  
let action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let _0_323 =
          FStar_Util.Inr
            (FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
               FStar_Syntax_Syntax.Delta_equational None)
           in
        close_univs_and_mk_letbinding None _0_323
          a.FStar_Syntax_Syntax.action_univs a.FStar_Syntax_Syntax.action_typ
          FStar_Syntax_Const.effect_Tot_lid a.FStar_Syntax_Syntax.action_defn
         in
      FStar_Syntax_Syntax.Sig_let
        ((false, [lb]),
          ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos),
          [a.FStar_Syntax_Syntax.action_name],
          [FStar_Syntax_Syntax.Visible_default;
          FStar_Syntax_Syntax.Action eff_lid], [])
  
let mk_reify t =
  let reify_ =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_reify) None
      t.FStar_Syntax_Syntax.pos
     in
  (FStar_Syntax_Syntax.mk
     (FStar_Syntax_Syntax.Tm_app
        (let _0_325 = let _0_324 = FStar_Syntax_Syntax.as_arg t  in [_0_324]
            in
         (reify_, _0_325)))) None t.FStar_Syntax_Syntax.pos
  
let rec delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t = FStar_Syntax_Subst.compress t  in
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____4290 -> failwith "Impossible"
    | FStar_Syntax_Syntax.Tm_fvar fv -> fv.FStar_Syntax_Syntax.fv_delta
    | FStar_Syntax_Syntax.Tm_bvar _
      |FStar_Syntax_Syntax.Tm_name _
       |FStar_Syntax_Syntax.Tm_match _
        |FStar_Syntax_Syntax.Tm_uvar _|FStar_Syntax_Syntax.Tm_unknown  ->
        FStar_Syntax_Syntax.Delta_equational
    | FStar_Syntax_Syntax.Tm_type _
      |FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_arrow _ ->
        FStar_Syntax_Syntax.Delta_constant
    | FStar_Syntax_Syntax.Tm_uinst (t,_)
      |FStar_Syntax_Syntax.Tm_refine
       ({ FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _;
          FStar_Syntax_Syntax.sort = t;_},_)
       |FStar_Syntax_Syntax.Tm_meta (t,_)
        |FStar_Syntax_Syntax.Tm_ascribed (t,_,_)
         |FStar_Syntax_Syntax.Tm_app (t,_)
          |FStar_Syntax_Syntax.Tm_abs (_,t,_)|FStar_Syntax_Syntax.Tm_let
           (_,t)
        -> delta_qualifier t
  
let incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let d = delta_qualifier t  in
    let rec aux d =
      match d with
      | FStar_Syntax_Syntax.Delta_equational  -> d
      | FStar_Syntax_Syntax.Delta_constant  ->
          FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Delta_defined_at_level i ->
          FStar_Syntax_Syntax.Delta_defined_at_level
            (i + (Prims.parse_int "1"))
      | FStar_Syntax_Syntax.Delta_abstract d -> aux d  in
    aux d
  
let is_unknown : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4396 = (FStar_Syntax_Subst.compress t).FStar_Syntax_Syntax.n
       in
    match uu____4396 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4397 -> false
  
let rec list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list Prims.option
  =
  fun e  ->
    let uu____4405 = head_and_args (unmeta e)  in
    match uu____4405 with
    | (head,args) ->
        let uu____4433 =
          let _0_326 = (un_uinst head).FStar_Syntax_Syntax.n  in
          (_0_326, args)  in
        (match uu____4433 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4449) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____4462::(hd,uu____4464)::(tl,uu____4466)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             Some
               (let _0_327 = FStar_Util.must (list_elements tl)  in hd ::
                  _0_327)
         | uu____4506 -> None)
  