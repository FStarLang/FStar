open Prims
let qual_id : FStar_Ident.lident -> FStar_Ident.ident -> FStar_Ident.lident =
  fun lid  ->
    fun id  ->
      let uu____7 =
        FStar_Ident.lid_of_ids
          (FStar_List.append lid.FStar_Ident.ns [lid.FStar_Ident.ident; id])
         in
      FStar_Ident.set_lid_range uu____7 id.FStar_Ident.idRange
  
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
  
let arg_of_non_null_binder uu____25 =
  match uu____25 with
  | (b,imp) ->
      let uu____30 = FStar_Syntax_Syntax.bv_to_name b  in (uu____30, imp)
  
let args_of_non_null_binders :
  FStar_Syntax_Syntax.binders ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.collect
         (fun b  ->
            let uu____43 = FStar_Syntax_Syntax.is_null_binder b  in
            if uu____43
            then []
            else (let uu____50 = arg_of_non_null_binder b  in [uu____50])))
  
let args_of_binders :
  FStar_Syntax_Syntax.binders ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list)
  =
  fun binders  ->
    let uu____64 =
      FStar_All.pipe_right binders
        (FStar_List.map
           (fun b  ->
              let uu____86 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____86
              then
                let b1 =
                  let uu____96 =
                    FStar_Syntax_Syntax.new_bv None
                      (Prims.fst b).FStar_Syntax_Syntax.sort
                     in
                  (uu____96, (Prims.snd b))  in
                let uu____97 = arg_of_non_null_binder b1  in (b1, uu____97)
              else
                (let uu____105 = arg_of_non_null_binder b  in (b, uu____105))))
       in
    FStar_All.pipe_right uu____64 FStar_List.unzip
  
let name_binders :
  FStar_Syntax_Syntax.binder Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_List.mapi
         (fun i  ->
            fun b  ->
              let uu____145 = FStar_Syntax_Syntax.is_null_binder b  in
              if uu____145
              then
                let uu____148 = b  in
                match uu____148 with
                | (a,imp) ->
                    let b1 =
                      let uu____154 =
                        let uu____155 = FStar_Util.string_of_int i  in
                        Prims.strcat "_" uu____155  in
                      FStar_Ident.id_of_text uu____154  in
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
      let uu____183 =
        let uu____186 =
          let uu____187 =
            let uu____195 = name_binders binders  in (uu____195, comp)  in
          FStar_Syntax_Syntax.Tm_arrow uu____187  in
        FStar_Syntax_Syntax.mk uu____186  in
      uu____183 None t.FStar_Syntax_Syntax.pos
  | uu____212 -> t 
let null_binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____232  ->
            match uu____232 with
            | (t,imp) ->
                let uu____239 =
                  let uu____240 = FStar_Syntax_Syntax.null_binder t  in
                  FStar_All.pipe_left Prims.fst uu____240  in
                (uu____239, imp)))
  
let binders_of_tks :
  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun tks  ->
    FStar_All.pipe_right tks
      (FStar_List.map
         (fun uu____266  ->
            match uu____266 with
            | (t,imp) ->
                let uu____279 =
                  FStar_Syntax_Syntax.new_bv
                    (Some (t.FStar_Syntax_Syntax.pos)) t
                   in
                (uu____279, imp)))
  
let binders_of_freevars :
  FStar_Syntax_Syntax.bv FStar_Util.set ->
    FStar_Syntax_Syntax.binder Prims.list
  =
  fun fvs  ->
    let uu____286 = FStar_Util.set_elements fvs  in
    FStar_All.pipe_right uu____286
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
          (fun uu____354  ->
             fun uu____355  ->
               match (uu____354, uu____355) with
               | ((x,uu____365),(y,uu____367)) ->
                   let uu____372 =
                     let uu____377 = FStar_Syntax_Syntax.bv_to_name y  in
                     (x, uu____377)  in
                   FStar_Syntax_Syntax.NT uu____372) replace_xs with_ys
      else failwith "Ill-formed substitution"
  
let rec unmeta : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta (e2,_)|FStar_Syntax_Syntax.Tm_ascribed
      (e2,_,_) -> unmeta e2
    | uu____402 -> e1
  
let rec univ_kernel :
  FStar_Syntax_Syntax.universe -> (FStar_Syntax_Syntax.universe * Prims.int)
  =
  fun u  ->
    match u with
    | FStar_Syntax_Syntax.U_unknown 
      |FStar_Syntax_Syntax.U_name _
       |FStar_Syntax_Syntax.U_unif _|FStar_Syntax_Syntax.U_zero  ->
        (u, (Prims.parse_int "0"))
    | FStar_Syntax_Syntax.U_succ u1 ->
        let uu____413 = univ_kernel u1  in
        (match uu____413 with | (k,n1) -> (k, (n1 + (Prims.parse_int "1"))))
    | FStar_Syntax_Syntax.U_max uu____420 ->
        failwith "Imposible: univ_kernel (U_max _)"
    | FStar_Syntax_Syntax.U_bvar uu____424 ->
        failwith "Imposible: univ_kernel (U_bvar _)"
  
let constant_univ_as_nat : FStar_Syntax_Syntax.universe -> Prims.int =
  fun u  -> let uu____430 = univ_kernel u  in Prims.snd uu____430 
let rec compare_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.int =
  fun u1  ->
    fun u2  ->
      match (u1, u2) with
      | (FStar_Syntax_Syntax.U_bvar _,_)|(_,FStar_Syntax_Syntax.U_bvar _) ->
          failwith "Impossible: compare_univs"
      | (FStar_Syntax_Syntax.U_unknown ,FStar_Syntax_Syntax.U_unknown ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_unknown ,uu____443) ->
          ~- (Prims.parse_int "1")
      | (uu____444,FStar_Syntax_Syntax.U_unknown ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_zero ,FStar_Syntax_Syntax.U_zero ) ->
          (Prims.parse_int "0")
      | (FStar_Syntax_Syntax.U_zero ,uu____445) -> ~- (Prims.parse_int "1")
      | (uu____446,FStar_Syntax_Syntax.U_zero ) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_name u11,FStar_Syntax_Syntax.U_name u21) ->
          FStar_String.compare u11.FStar_Ident.idText u21.FStar_Ident.idText
      | (FStar_Syntax_Syntax.U_name uu____449,FStar_Syntax_Syntax.U_unif
         uu____450) -> ~- (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif uu____453,FStar_Syntax_Syntax.U_name
         uu____454) -> (Prims.parse_int "1")
      | (FStar_Syntax_Syntax.U_unif u11,FStar_Syntax_Syntax.U_unif u21) ->
          let uu____463 = FStar_Unionfind.uvar_id u11  in
          let uu____465 = FStar_Unionfind.uvar_id u21  in
          uu____463 - uu____465
      | (FStar_Syntax_Syntax.U_max us1,FStar_Syntax_Syntax.U_max us2) ->
          let n1 = FStar_List.length us1  in
          let n2 = FStar_List.length us2  in
          if n1 <> n2
          then n1 - n2
          else
            (let copt =
               let uu____487 = FStar_List.zip us1 us2  in
               FStar_Util.find_map uu____487
                 (fun uu____493  ->
                    match uu____493 with
                    | (u11,u21) ->
                        let c = compare_univs u11 u21  in
                        if c <> (Prims.parse_int "0") then Some c else None)
                in
             match copt with | None  -> (Prims.parse_int "0") | Some c -> c)
      | (FStar_Syntax_Syntax.U_max uu____503,uu____504) ->
          ~- (Prims.parse_int "1")
      | (uu____506,FStar_Syntax_Syntax.U_max uu____507) ->
          (Prims.parse_int "1")
      | uu____509 ->
          let uu____512 = univ_kernel u1  in
          (match uu____512 with
           | (k1,n1) ->
               let uu____517 = univ_kernel u2  in
               (match uu____517 with
                | (k2,n2) ->
                    let r = compare_univs k1 k2  in
                    if r = (Prims.parse_int "0") then n1 - n2 else r))
  
let eq_univs :
  FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe -> Prims.bool
  =
  fun u1  ->
    fun u2  ->
      let uu____530 = compare_univs u1 u2  in
      uu____530 = (Prims.parse_int "0")
  
let ml_comp :
  FStar_Syntax_Syntax.term -> FStar_Range.range -> FStar_Syntax_Syntax.comp =
  fun t  ->
    fun r  ->
      let uu____537 =
        let uu____538 =
          let uu____544 = FStar_Syntax_Syntax.as_arg t  in
          let uu____545 =
            let uu____547 =
              FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.tun  in
            [uu____547]  in
          uu____544 :: uu____545  in
        {
          FStar_Syntax_Syntax.comp_typ_name =
            (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_ML_lid r);
          FStar_Syntax_Syntax.comp_univs = [FStar_Syntax_Syntax.U_unknown];
          FStar_Syntax_Syntax.effect_args = uu____538;
          FStar_Syntax_Syntax.flags = [FStar_Syntax_Syntax.MLEFFECT]
        }  in
      FStar_Syntax_Syntax.mk_Comp uu____537
  
let comp_effect_name c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 -> c1.FStar_Syntax_Syntax.comp_typ_name
  | FStar_Syntax_Syntax.Total uu____560 -> FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.GTotal uu____566 ->
      FStar_Syntax_Const.effect_GTot_lid
  
let comp_flags c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____584 -> [FStar_Syntax_Syntax.TOTAL]
  | FStar_Syntax_Syntax.GTotal uu____590 -> [FStar_Syntax_Syntax.SOMETRIVIAL]
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
        | FStar_Syntax_Syntax.Total (t,u_opt)|FStar_Syntax_Syntax.GTotal
          (t,u_opt) ->
            let uu____626 =
              let uu____627 = FStar_Util.map_opt u_opt (fun x  -> [x])  in
              FStar_Util.dflt [] uu____627  in
            let uu____633 =
              let uu____639 = FStar_Syntax_Syntax.as_arg t  in [uu____639]
               in
            {
              FStar_Syntax_Syntax.comp_typ_name = (comp_effect_name c1);
              FStar_Syntax_Syntax.comp_univs = uu____626;
              FStar_Syntax_Syntax.effect_args = uu____633;
              FStar_Syntax_Syntax.flags = (comp_flags c1)
            }
         in
      let uu___177_640 = c  in
      let uu____641 =
        let uu____642 =
          let uu___178_643 = comp_to_comp_typ c  in
          {
            FStar_Syntax_Syntax.comp_typ_name =
              (uu___178_643.FStar_Syntax_Syntax.comp_typ_name);
            FStar_Syntax_Syntax.comp_univs =
              (uu___178_643.FStar_Syntax_Syntax.comp_univs);
            FStar_Syntax_Syntax.effect_args =
              (uu___178_643.FStar_Syntax_Syntax.effect_args);
            FStar_Syntax_Syntax.flags = f
          }  in
        FStar_Syntax_Syntax.Comp uu____642  in
      {
        FStar_Syntax_Syntax.n = uu____641;
        FStar_Syntax_Syntax.tk = (uu___177_640.FStar_Syntax_Syntax.tk);
        FStar_Syntax_Syntax.pos = (uu___177_640.FStar_Syntax_Syntax.pos);
        FStar_Syntax_Syntax.vars = (uu___177_640.FStar_Syntax_Syntax.vars)
      }
  
let comp_to_comp_typ :
  FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.comp_typ =
  fun c  ->
    match c.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Comp c1 -> c1
    | FStar_Syntax_Syntax.Total (t,Some u)|FStar_Syntax_Syntax.GTotal
      (t,Some u) ->
        let uu____664 =
          let uu____670 = FStar_Syntax_Syntax.as_arg t  in [uu____670]  in
        {
          FStar_Syntax_Syntax.comp_typ_name = (comp_effect_name c);
          FStar_Syntax_Syntax.comp_univs = [u];
          FStar_Syntax_Syntax.effect_args = uu____664;
          FStar_Syntax_Syntax.flags = (comp_flags c)
        }
    | uu____671 ->
        failwith "Assertion failed: Computation type without universe"
  
let is_named_tot c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.comp_typ_name
        FStar_Syntax_Const.effect_Tot_lid
  | FStar_Syntax_Syntax.Total uu____684 -> true
  | FStar_Syntax_Syntax.GTotal uu____690 -> false 
let is_total_comp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___165_708  ->
          match uu___165_708 with
          | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  -> true
          | uu____709 -> false))
  
let is_total_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    (FStar_Ident.lid_equals c.FStar_Syntax_Syntax.lcomp_name
       FStar_Syntax_Const.effect_Tot_lid)
      ||
      (FStar_All.pipe_right c.FStar_Syntax_Syntax.lcomp_cflags
         (FStar_Util.for_some
            (fun uu___166_714  ->
               match uu___166_714 with
               | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  ->
                   true
               | uu____715 -> false)))
  
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
            (fun uu___167_720  ->
               match uu___167_720 with
               | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  ->
                   true
               | uu____721 -> false)))
  
let is_partial_return c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___168_734  ->
          match uu___168_734 with
          | FStar_Syntax_Syntax.RETURN |FStar_Syntax_Syntax.PARTIAL_RETURN 
              -> true
          | uu____735 -> false))
  
let is_lcomp_partial_return : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun c  ->
    FStar_All.pipe_right c.FStar_Syntax_Syntax.lcomp_cflags
      (FStar_Util.for_some
         (fun uu___169_740  ->
            match uu___169_740 with
            | FStar_Syntax_Syntax.RETURN |FStar_Syntax_Syntax.PARTIAL_RETURN 
                -> true
            | uu____741 -> false))
  
let is_tot_or_gtot_comp c =
  (is_total_comp c) ||
    (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid
       (comp_effect_name c))
  
let is_named_tot_or_gtot_comp c =
  let m = comp_effect_name c  in
  (FStar_Ident.lid_equals FStar_Syntax_Const.effect_Tot_lid m) ||
    (FStar_Ident.lid_equals FStar_Syntax_Const.effect_GTot_lid m)
  
let is_pure_effect : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Pure_lid)
  
let is_pure_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____779 -> true
  | FStar_Syntax_Syntax.GTotal uu____785 -> false
  | FStar_Syntax_Syntax.Comp ct ->
      ((is_total_comp c) ||
         (is_pure_effect ct.FStar_Syntax_Syntax.comp_typ_name))
        ||
        (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___170_793  ->
                 match uu___170_793 with
                 | FStar_Syntax_Syntax.LEMMA  -> true
                 | uu____794 -> false)))
  
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
            (fun uu___171_813  ->
               match uu___171_813 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____814 -> false)))
  
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.lcomp_name)
  
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____821 =
      let uu____822 = FStar_Syntax_Subst.compress t  in
      uu____822.FStar_Syntax_Syntax.n  in
    match uu____821 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____825,c) -> is_pure_or_ghost_comp c
    | uu____837 -> true
  
let is_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____841 =
      let uu____842 = FStar_Syntax_Subst.compress t  in
      uu____842.FStar_Syntax_Syntax.n  in
    match uu____841 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____845,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct ->
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_Lemma_lid
         | uu____858 -> false)
    | uu____859 -> false
  
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
    | uu____905 -> (t1, [])
  
let un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____920) ->
        FStar_Syntax_Subst.compress t2
    | uu____925 -> t1
  
let is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____929 =
      let uu____930 = FStar_Syntax_Subst.compress t  in
      uu____930.FStar_Syntax_Syntax.n  in
    match uu____929 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____933,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____949)::uu____950 ->
                  let pats' = unmeta pats  in
                  let uu____981 = head_and_args pats'  in
                  (match uu____981 with
                   | (head1,uu____992) ->
                       let uu____1007 =
                         let uu____1008 = un_uinst head1  in
                         uu____1008.FStar_Syntax_Syntax.n  in
                       (match uu____1007 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.cons_lid
                        | uu____1012 -> false))
              | uu____1013 -> false)
         | uu____1019 -> false)
    | uu____1020 -> false
  
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.comp_typ_name
         FStar_Syntax_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___172_1034  ->
                 match uu___172_1034 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____1035 -> false)))
  | uu____1036 -> false 
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___173_1049  ->
          match uu___173_1049 with
          | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  -> true
          | uu____1050 -> false))
  
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
  | uu____1072 -> false 
let rec unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1078,uu____1079) ->
        unascribe e2
    | uu____1098 -> e1
  
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1130,uu____1131) ->
      ascribe t' k
  | uu____1150 ->
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (t, k, None))
        None t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let uu___is_Equal : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1167 -> false
  
let uu___is_NotEqual : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1171 -> false
  
let uu___is_Unknown : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1175 -> false
  
let rec eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let t11 = unascribe t1  in
      let t21 = unascribe t2  in
      let equal_if uu___174_1195 = if uu___174_1195 then Equal else Unknown
         in
      let equal_iff uu___175_1200 = if uu___175_1200 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____1214 -> Unknown
         in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____1219 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____1219
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____1232 = eq_tm f g  in
          eq_and uu____1232
            (fun uu____1233  ->
               let uu____1234 = eq_univs_list us vs  in equal_if uu____1234)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____1237 = FStar_Const.eq_const c d  in equal_iff uu____1237
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1239),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1241)) ->
          let uu____1266 = FStar_Unionfind.equivalent u1 u2  in
          equal_if uu____1266
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____1302 = eq_tm h1 h2  in
          eq_and uu____1302 (fun uu____1303  -> eq_args args1 args2)
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____1306 = eq_univs u v1  in equal_if uu____1306
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1308),uu____1309) ->
          eq_tm t12 t21
      | (uu____1314,FStar_Syntax_Syntax.Tm_meta (t22,uu____1316)) ->
          eq_tm t11 t22
      | uu____1321 -> Unknown

and eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1345)::a11,(b,uu____1348)::b1) ->
          let uu____1386 = eq_tm a b  in
          (match uu____1386 with
           | Equal  -> eq_args a11 b1
           | uu____1387 -> Unknown)
      | uu____1388 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1402) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1408,uu____1409) ->
        unrefine t2
    | uu____1428 -> t1
  
let rec is_unit : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1432 =
      let uu____1433 = unrefine t  in uu____1433.FStar_Syntax_Syntax.n  in
    match uu____1432 with
    | FStar_Syntax_Syntax.Tm_type uu____1436 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1439) -> is_unit t1
    | uu____1444 -> false
  
let is_fun : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1448 =
      let uu____1449 = FStar_Syntax_Subst.compress e  in
      uu____1449.FStar_Syntax_Syntax.n  in
    match uu____1448 with
    | FStar_Syntax_Syntax.Tm_abs uu____1452 -> true
    | uu____1467 -> false
  
let is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1471 =
      let uu____1472 = FStar_Syntax_Subst.compress t  in
      uu____1472.FStar_Syntax_Syntax.n  in
    match uu____1471 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1475 -> true
    | uu____1483 -> false
  
let rec pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1489) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1495,uu____1496) ->
        pre_typ t2
    | uu____1515 -> t1
  
let destruct :
  FStar_Syntax_Syntax.term ->
    FStar_Ident.lident ->
      ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list
        Prims.option
  =
  fun typ  ->
    fun lid  ->
      let typ1 = FStar_Syntax_Subst.compress typ  in
      let uu____1529 =
        let uu____1530 = un_uinst typ1  in uu____1530.FStar_Syntax_Syntax.n
         in
      match uu____1529 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____1568 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____1584 -> None
  
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
    | FStar_Syntax_Syntax.Sig_new_effect_for_free (n1,_)
      |FStar_Syntax_Syntax.Sig_new_effect (n1,_) ->
        [n1.FStar_Syntax_Syntax.mname]
    | FStar_Syntax_Syntax.Sig_sub_effect _
      |FStar_Syntax_Syntax.Sig_pragma _|FStar_Syntax_Syntax.Sig_main _ -> []
  
let lid_of_sigelt :
  FStar_Syntax_Syntax.sigelt -> FStar_Ident.lident Prims.option =
  fun se  ->
    match lids_of_sigelt se with | l::[] -> Some l | uu____1661 -> None
  
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
  
let range_of_lb uu___176_1844 =
  match uu___176_1844 with
  | (FStar_Util.Inl x,uu____1851,uu____1852) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____1856,uu____1857) -> FStar_Ident.range_of_lid l 
let range_of_arg uu____1874 =
  match uu____1874 with | (hd1,uu____1880) -> hd1.FStar_Syntax_Syntax.pos 
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
      let uu____1994 =
        let uu____1997 =
          let uu____1998 =
            let uu____2003 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor)
               in
            (uu____2003,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app))
             in
          FStar_Syntax_Syntax.Tm_meta uu____1998  in
        FStar_Syntax_Syntax.mk uu____1997  in
      uu____1994 None (FStar_Ident.range_of_lid l)
  | uu____2012 ->
      let e =
        let uu____2021 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor)
           in
        mk_app uu____2021 args  in
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
      let uu____2036 =
        let uu____2039 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "7")
           in
        (uu____2039, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____2036
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
          let uu____2072 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____2072
          then
            let uu____2073 =
              let uu____2076 =
                let uu____2077 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____2077  in
              let uu____2078 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____2076, uu____2078)  in
            FStar_Ident.mk_ident uu____2073
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___179_2081 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___179_2081.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___179_2081.FStar_Syntax_Syntax.sort)
          }  in
        let uu____2082 = mk_field_projector_name_from_ident lid nm  in
        (uu____2082, y)
  
let set_uvar uv t =
  let uu____2099 = FStar_Unionfind.find uv  in
  match uu____2099 with
  | FStar_Syntax_Syntax.Fixed uu____2102 ->
      let uu____2103 =
        let uu____2104 =
          let uu____2105 = FStar_Unionfind.uvar_id uv  in
          FStar_All.pipe_left FStar_Util.string_of_int uu____2105  in
        FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2104  in
      failwith uu____2103
  | uu____2107 -> FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed t) 
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
      | uu____2154 -> q1 = q2
  
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
          (let close_lopt lopt1 =
             match lopt1 with
             | None |Some (FStar_Util.Inr _) -> lopt1
             | Some (FStar_Util.Inl lc) ->
                 let uu____2240 =
                   let uu____2246 = FStar_Syntax_Subst.close_lcomp bs lc  in
                   FStar_Util.Inl uu____2246  in
                 Some uu____2240
              in
           match bs with
           | [] -> t
           | uu____2257 ->
               let body =
                 let uu____2262 = FStar_Syntax_Subst.close bs t  in
                 FStar_Syntax_Subst.compress uu____2262  in
               (match ((body.FStar_Syntax_Syntax.n), lopt) with
                | (FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt'),None ) ->
                    let uu____2305 =
                      let uu____2308 =
                        let uu____2309 =
                          let uu____2324 =
                            let uu____2328 =
                              FStar_Syntax_Subst.close_binders bs  in
                            FStar_List.append uu____2328 bs'  in
                          let uu____2334 = close_lopt lopt'  in
                          (uu____2324, t1, uu____2334)  in
                        FStar_Syntax_Syntax.Tm_abs uu____2309  in
                      FStar_Syntax_Syntax.mk uu____2308  in
                    uu____2305 None t1.FStar_Syntax_Syntax.pos
                | uu____2360 ->
                    let uu____2369 =
                      let uu____2372 =
                        let uu____2373 =
                          let uu____2388 =
                            FStar_Syntax_Subst.close_binders bs  in
                          let uu____2389 = close_lopt lopt  in
                          (uu____2388, body, uu____2389)  in
                        FStar_Syntax_Syntax.Tm_abs uu____2373  in
                      FStar_Syntax_Syntax.mk uu____2372  in
                    uu____2369 None t.FStar_Syntax_Syntax.pos))
  
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
      | uu____2418 ->
          let uu____2419 =
            let uu____2422 =
              let uu____2423 =
                let uu____2431 = FStar_Syntax_Subst.close_binders bs  in
                let uu____2432 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____2431, uu____2432)  in
              FStar_Syntax_Syntax.Tm_arrow uu____2423  in
            FStar_Syntax_Syntax.mk uu____2422  in
          uu____2419 None c.FStar_Syntax_Syntax.pos
  
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
      | uu____2449 ->
          let c = FStar_Syntax_Syntax.mk_Total t  in
          let uu____2451 =
            let uu____2454 =
              let uu____2455 =
                let uu____2463 = FStar_Syntax_Subst.close_binders bs  in
                let uu____2464 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____2463, uu____2464)  in
              FStar_Syntax_Syntax.Tm_arrow uu____2455  in
            FStar_Syntax_Syntax.mk uu____2454  in
          uu____2451 None c.FStar_Syntax_Syntax.pos
  
let flat_arrow :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____2482 =
        let uu____2483 = FStar_Syntax_Subst.compress t  in
        uu____2483.FStar_Syntax_Syntax.n  in
      match uu____2482 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2503) ->
               let uu____2510 =
                 let uu____2511 = FStar_Syntax_Subst.compress tres  in
                 uu____2511.FStar_Syntax_Syntax.n  in
               (match uu____2510 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____2528 = FStar_ST.read t.FStar_Syntax_Syntax.tk
                       in
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_arrow
                          ((FStar_List.append bs1 bs'), c'))) uu____2528
                      t.FStar_Syntax_Syntax.pos
                | uu____2548 -> t)
           | uu____2549 -> t)
      | uu____2550 -> t
  
let refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____2559 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk  in
      let uu____2564 =
        let uu____2565 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____2565 t.FStar_Syntax_Syntax.pos  in
      let uu____2566 =
        let uu____2569 =
          let uu____2570 =
            let uu____2575 =
              let uu____2576 =
                let uu____2577 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____2577]  in
              FStar_Syntax_Subst.close uu____2576 t  in
            (b, uu____2575)  in
          FStar_Syntax_Syntax.Tm_refine uu____2570  in
        FStar_Syntax_Syntax.mk uu____2569  in
      uu____2566 uu____2559 uu____2564
  
let branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let tot_or_gtot_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,_)|FStar_Syntax_Syntax.GTotal (t,_) -> t
  | FStar_Syntax_Syntax.Comp c1 ->
      if
        (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.comp_typ_name
           FStar_Syntax_Const.effect_Tot_lid)
          ||
          (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.comp_typ_name
             FStar_Syntax_Const.effect_GTot_lid)
      then
        let uu____2618 = FStar_List.hd c1.FStar_Syntax_Syntax.effect_args  in
        FStar_All.pipe_left Prims.fst uu____2618
      else failwith "Expected a Tot or GTot computation"
  
let rec arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____2664 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____2664 with
         | (bs1,c1) ->
             if is_named_tot_or_gtot_comp c1
             then
               let uu____2679 =
                 let uu____2685 = tot_or_gtot_result c1  in
                 arrow_formals_comp uu____2685  in
               (match uu____2679 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____2705 ->
        let uu____2706 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____2706)
  
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
      | Some (FStar_Util.Inl l1) ->
          let l2 =
            let uu___180_2767 = l1  in
            let uu____2768 =
              FStar_List.map
                (fun uu____2778  ->
                   match uu____2778 with
                   | (t1,imp) ->
                       let uu____2785 = FStar_Syntax_Subst.subst s t1  in
                       (uu____2785, imp))
                l1.FStar_Syntax_Syntax.lcomp_indices
               in
            let uu____2786 =
              FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.lcomp_res_typ
               in
            {
              FStar_Syntax_Syntax.lcomp_name =
                (uu___180_2767.FStar_Syntax_Syntax.lcomp_name);
              FStar_Syntax_Syntax.lcomp_univs =
                (uu___180_2767.FStar_Syntax_Syntax.lcomp_univs);
              FStar_Syntax_Syntax.lcomp_indices = uu____2768;
              FStar_Syntax_Syntax.lcomp_res_typ = uu____2786;
              FStar_Syntax_Syntax.lcomp_cflags =
                (uu___180_2767.FStar_Syntax_Syntax.lcomp_cflags);
              FStar_Syntax_Syntax.lcomp_as_comp =
                (fun uu____2789  ->
                   let uu____2790 = l1.FStar_Syntax_Syntax.lcomp_as_comp ()
                      in
                   FStar_Syntax_Subst.subst_comp s uu____2790)
            }  in
          Some (FStar_Util.Inl l2)
      | uu____2799 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____2837 =
        let uu____2838 =
          let uu____2841 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____2841  in
        uu____2838.FStar_Syntax_Syntax.n  in
      match uu____2837 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____2879 = aux t2 what  in
          (match uu____2879 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____2936 -> ([], t1, abs_body_lcomp)  in
    let uu____2948 = aux t None  in
    match uu____2948 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____2996 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____2996 with
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
                | (Some fvs,uu____3096) ->
                    let universes =
                      FStar_All.pipe_right univ_vars
                        (FStar_List.map
                           (fun _0_25  -> FStar_Syntax_Syntax.U_name _0_25))
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
            let uu____3157 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____3157 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____3173 ->
            let t' = arrow binders c  in
            let uu____3178 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____3178 with
             | (uvs1,t'1) ->
                 let uu____3189 =
                   let uu____3190 = FStar_Syntax_Subst.compress t'1  in
                   uu____3190.FStar_Syntax_Syntax.n  in
                 (match uu____3189 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____3216 -> failwith "Impossible"))
  
let is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.starts_with
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          "Prims.tuple"
    | uu____3231 -> false
  
let mk_tuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3239 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "tuple%s" uu____3239  in
      let uu____3240 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range uu____3240 r
  
let mk_tuple_data_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3248 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "Mktuple%s" uu____3248  in
      let uu____3249 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range uu____3249 r
  
let is_tuple_data_lid : FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____3256 = mk_tuple_data_lid n1 FStar_Range.dummyRange  in
      FStar_Ident.lid_equals f uu____3256
  
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
    | uu____3274 -> false
  
let mk_dtuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3282 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "dtuple%s" uu____3282  in
      let uu____3283 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range uu____3283 r
  
let mk_dtuple_data_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3291 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "Mkdtuple%s" uu____3291  in
      let uu____3292 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range uu____3292 r
  
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
      let uu____3330 =
        let uu____3331 = pre_typ t  in uu____3331.FStar_Syntax_Syntax.n  in
      match uu____3330 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3339 -> false
  
let rec is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3346 =
        let uu____3347 = pre_typ t  in uu____3347.FStar_Syntax_Syntax.n  in
      match uu____3346 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3350 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____3352) ->
          is_constructed_typ t1 lid
      | uu____3367 -> false
  
let rec get_tycon :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.option =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar _
      |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ -> 
        Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____3378) -> get_tycon t2
    | uu____3393 -> None
  
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
  fun uu____3423  ->
    let u =
      let uu____3427 = FStar_Unionfind.fresh None  in
      FStar_All.pipe_left (fun _0_26  -> FStar_Syntax_Syntax.U_unif _0_26)
        uu____3427
       in
    let uu____3433 =
      (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)) None
        FStar_Range.dummyRange
       in
    (uu____3433, u)
  
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
      | Some phi11 ->
          let uu____3471 =
            let uu____3474 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____3475 =
              let uu____3478 =
                let uu____3479 =
                  let uu____3489 =
                    let uu____3491 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____3492 =
                      let uu____3494 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____3494]  in
                    uu____3491 :: uu____3492  in
                  (tand, uu____3489)  in
                FStar_Syntax_Syntax.Tm_app uu____3479  in
              FStar_Syntax_Syntax.mk uu____3478  in
            uu____3475 None uu____3474  in
          Some uu____3471
  
let mk_binop op_t phi1 phi2 =
  let uu____3529 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos
     in
  let uu____3530 =
    let uu____3533 =
      let uu____3534 =
        let uu____3544 =
          let uu____3546 = FStar_Syntax_Syntax.as_arg phi1  in
          let uu____3547 =
            let uu____3549 = FStar_Syntax_Syntax.as_arg phi2  in [uu____3549]
             in
          uu____3546 :: uu____3547  in
        (op_t, uu____3544)  in
      FStar_Syntax_Syntax.Tm_app uu____3534  in
    FStar_Syntax_Syntax.mk uu____3533  in
  uu____3530 None uu____3529 
let mk_neg phi =
  let uu____3570 =
    let uu____3573 =
      let uu____3574 =
        let uu____3584 =
          let uu____3586 = FStar_Syntax_Syntax.as_arg phi  in [uu____3586]
           in
        (t_not, uu____3584)  in
      FStar_Syntax_Syntax.Tm_app uu____3574  in
    FStar_Syntax_Syntax.mk uu____3573  in
  uu____3570 None phi.FStar_Syntax_Syntax.pos 
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
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun phi1  ->
    fun phi2  ->
      let uu____3646 =
        let uu____3647 = FStar_Syntax_Subst.compress phi1  in
        uu____3647.FStar_Syntax_Syntax.n  in
      match uu____3646 with
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid ->
          t_true
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
          phi2
      | uu____3652 ->
          let uu____3653 =
            let uu____3654 = FStar_Syntax_Subst.compress phi2  in
            uu____3654.FStar_Syntax_Syntax.n  in
          (match uu____3653 with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid tc
                    FStar_Syntax_Const.false_lid)
               -> phi2
           | uu____3658 -> mk_binop timp phi1 phi2)
  
let mk_iff phi1 phi2 = mk_binop tiff phi1 phi2 
let b2t e =
  let uu____3682 =
    let uu____3685 =
      let uu____3686 =
        let uu____3696 =
          let uu____3698 = FStar_Syntax_Syntax.as_arg e  in [uu____3698]  in
        (b2t_v, uu____3696)  in
      FStar_Syntax_Syntax.Tm_app uu____3686  in
    FStar_Syntax_Syntax.mk uu____3685  in
  uu____3682 None e.FStar_Syntax_Syntax.pos 
let teq : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid 
let mk_untyped_eq2 e1 e2 =
  let uu____3722 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos
     in
  let uu____3723 =
    let uu____3726 =
      let uu____3727 =
        let uu____3737 =
          let uu____3739 = FStar_Syntax_Syntax.as_arg e1  in
          let uu____3740 =
            let uu____3742 = FStar_Syntax_Syntax.as_arg e2  in [uu____3742]
             in
          uu____3739 :: uu____3740  in
        (teq, uu____3737)  in
      FStar_Syntax_Syntax.Tm_app uu____3727  in
    FStar_Syntax_Syntax.mk uu____3726  in
  uu____3723 None uu____3722 
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
          let uu____3765 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____3766 =
            let uu____3769 =
              let uu____3770 =
                let uu____3780 =
                  let uu____3782 = FStar_Syntax_Syntax.iarg t  in
                  let uu____3783 =
                    let uu____3785 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____3786 =
                      let uu____3788 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____3788]  in
                    uu____3785 :: uu____3786  in
                  uu____3782 :: uu____3783  in
                (eq_inst, uu____3780)  in
              FStar_Syntax_Syntax.Tm_app uu____3770  in
            FStar_Syntax_Syntax.mk uu____3769  in
          uu____3766 None uu____3765
  
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid  in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange
     in
  let uu____3826 =
    let uu____3829 =
      let uu____3830 =
        let uu____3840 =
          let uu____3842 = FStar_Syntax_Syntax.iarg t  in
          let uu____3843 =
            let uu____3845 = FStar_Syntax_Syntax.as_arg x  in
            let uu____3846 =
              let uu____3848 = FStar_Syntax_Syntax.as_arg t'  in [uu____3848]
               in
            uu____3845 :: uu____3846  in
          uu____3842 :: uu____3843  in
        (t_has_type1, uu____3840)  in
      FStar_Syntax_Syntax.Tm_app uu____3830  in
    FStar_Syntax_Syntax.mk uu____3829  in
  uu____3826 None FStar_Range.dummyRange 
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
      (fun uu____3864  -> FStar_Syntax_Syntax.mk_Total ktype0)
  } 
let mk_forall :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun x  ->
    fun body  ->
      let uu____3871 =
        let uu____3874 =
          let uu____3875 =
            let uu____3885 =
              let uu____3887 =
                FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
              let uu____3888 =
                let uu____3890 =
                  let uu____3891 =
                    let uu____3892 =
                      let uu____3896 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3896]  in
                    abs uu____3892 body (Some (FStar_Util.Inl lc_tot_type0))
                     in
                  FStar_Syntax_Syntax.as_arg uu____3891  in
                [uu____3890]  in
              uu____3887 :: uu____3888  in
            (tforall, uu____3885)  in
          FStar_Syntax_Syntax.Tm_app uu____3875  in
        FStar_Syntax_Syntax.mk uu____3874  in
      uu____3871 None FStar_Range.dummyRange
  
let rec close_forall :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____3924 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____3924 then f1 else mk_forall (Prims.fst b) f1) bs f
  
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____3937 -> true
  | uu____3938 -> false 
let if_then_else b t1 t2 =
  let then_branch =
    let uu____3981 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos
       in
    (uu____3981, None, t1)  in
  let else_branch =
    let uu____4004 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos
       in
    (uu____4004, None, t2)  in
  let uu____4016 =
    let uu____4017 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos
       in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____4017  in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____4016
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let uu___is_QAll : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____4090 -> false
  
let __proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let uu___is_QEx : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____4114 -> false
  
let __proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let uu___is_BaseConn : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____4137 -> false
  
let __proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args) =
  fun projectee  -> match projectee with | BaseConn _0 -> _0 
let destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective Prims.option =
  fun f  ->
    let rec unmeta_monadic f1 =
      let f2 = FStar_Syntax_Subst.compress f1  in
      match f2.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_monadic _)
        |FStar_Syntax_Syntax.Tm_meta
        (t,FStar_Syntax_Syntax.Meta_monadic_lift _) -> unmeta_monadic t
      | uu____4172 -> f2  in
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
      let rec aux f2 uu____4217 =
        match uu____4217 with
        | (lid,arity) ->
            let uu____4223 =
              let uu____4233 = unmeta_monadic f2  in head_and_args uu____4233
               in
            (match uu____4223 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____4252 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____4252 then Some (BaseConn (lid, args)) else None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____4303 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____4303)
      | uu____4310 ->
          let uu____4311 = FStar_Syntax_Subst.compress t1  in
          ([], uu____4311)
       in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____4353 = head_and_args t1  in
        match uu____4353 with
        | (t2,args) ->
            let uu____4384 = un_uinst t2  in
            let uu____4385 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____4401  ->
                      match uu____4401 with
                      | (t3,imp) ->
                          let uu____4408 = unascribe t3  in (uu____4408, imp)))
               in
            (uu____4384, uu____4385)
         in
      let rec aux qopt out t1 =
        let uu____4431 = let uu____4440 = flat t1  in (qopt, uu____4440)  in
        match uu____4431 with
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
        | (Some b,uu____4699) ->
            let bs = FStar_List.rev out  in
            let uu____4717 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____4717 with
             | (bs1,t2) ->
                 let uu____4723 = patterns t2  in
                 (match uu____4723 with
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs1, pats, body))
                      else Some (QEx (bs1, pats, body))))
        | uu____4761 -> None  in
      aux None [] t  in
    let phi = unmeta_monadic f  in
    let uu____4773 = destruct_base_conn phi  in
    match uu____4773 with | Some b -> Some b | None  -> destruct_q_conn phi
  
let action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____4784 =
          let uu____4787 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None
             in
          FStar_Util.Inr uu____4787  in
        close_univs_and_mk_letbinding None uu____4784
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
  let uu____4816 =
    let uu____4819 =
      let uu____4820 =
        let uu____4830 =
          let uu____4832 = FStar_Syntax_Syntax.as_arg t  in [uu____4832]  in
        (reify_, uu____4830)  in
      FStar_Syntax_Syntax.Tm_app uu____4820  in
    FStar_Syntax_Syntax.mk uu____4819  in
  uu____4816 None t.FStar_Syntax_Syntax.pos 
let rec delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____4848 -> failwith "Impossible"
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
  
let incr_delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let d = delta_qualifier t  in
    let rec aux d1 =
      match d1 with
      | FStar_Syntax_Syntax.Delta_equational  -> d1
      | FStar_Syntax_Syntax.Delta_constant  ->
          FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1")
      | FStar_Syntax_Syntax.Delta_defined_at_level i ->
          FStar_Syntax_Syntax.Delta_defined_at_level
            (i + (Prims.parse_int "1"))
      | FStar_Syntax_Syntax.Delta_abstract d2 -> aux d2  in
    aux d
  
let is_unknown : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____4954 =
      let uu____4955 = FStar_Syntax_Subst.compress t  in
      uu____4955.FStar_Syntax_Syntax.n  in
    match uu____4954 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4958 -> false
  
let rec list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list Prims.option
  =
  fun e  ->
    let uu____4966 = let uu____4976 = unmeta e  in head_and_args uu____4976
       in
    match uu____4966 with
    | (head1,args) ->
        let uu____4995 =
          let uu____5003 =
            let uu____5004 = un_uinst head1  in
            uu____5004.FStar_Syntax_Syntax.n  in
          (uu____5003, args)  in
        (match uu____4995 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____5015) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____5028::(hd1,uu____5030)::(tl1,uu____5032)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____5066 =
               let uu____5070 =
                 let uu____5074 = list_elements tl1  in
                 FStar_Util.must uu____5074  in
               hd1 :: uu____5070  in
             Some uu____5066
         | uu____5083 -> None)
  