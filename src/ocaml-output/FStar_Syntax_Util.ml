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
  
let is_pure_effect : FStar_Ident.lident -> Prims.bool =
  fun l  ->
    ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
       (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_PURE_lid))
      || (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Pure_lid)
  
let is_pure_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total uu____767 -> true
  | FStar_Syntax_Syntax.GTotal uu____773 -> false
  | FStar_Syntax_Syntax.Comp ct ->
      ((is_total_comp c) ||
         (is_pure_effect ct.FStar_Syntax_Syntax.comp_typ_name))
        ||
        (FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___170_781  ->
                 match uu___170_781 with
                 | FStar_Syntax_Syntax.LEMMA  -> true
                 | uu____782 -> false)))
  
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
            (fun uu___171_801  ->
               match uu___171_801 with
               | FStar_Syntax_Syntax.LEMMA  -> true
               | uu____802 -> false)))
  
let is_pure_or_ghost_lcomp : FStar_Syntax_Syntax.lcomp -> Prims.bool =
  fun lc  ->
    (is_pure_lcomp lc) || (is_ghost_effect lc.FStar_Syntax_Syntax.lcomp_name)
  
let is_pure_or_ghost_function : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____809 =
      let uu____810 = FStar_Syntax_Subst.compress t  in
      uu____810.FStar_Syntax_Syntax.n  in
    match uu____809 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____813,c) -> is_pure_or_ghost_comp c
    | uu____825 -> true
  
let is_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____829 =
      let uu____830 = FStar_Syntax_Subst.compress t  in
      uu____830.FStar_Syntax_Syntax.n  in
    match uu____829 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____833,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct ->
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_Lemma_lid
         | uu____846 -> false)
    | uu____847 -> false
  
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
    | uu____893 -> (t1, [])
  
let un_uinst : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_uinst (t2,uu____908) ->
        FStar_Syntax_Subst.compress t2
    | uu____913 -> t1
  
let is_smt_lemma : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____917 =
      let uu____918 = FStar_Syntax_Subst.compress t  in
      uu____918.FStar_Syntax_Syntax.n  in
    match uu____917 with
    | FStar_Syntax_Syntax.Tm_arrow (uu____921,c) ->
        (match c.FStar_Syntax_Syntax.n with
         | FStar_Syntax_Syntax.Comp ct when
             FStar_Ident.lid_equals ct.FStar_Syntax_Syntax.comp_typ_name
               FStar_Syntax_Const.effect_Lemma_lid
             ->
             (match ct.FStar_Syntax_Syntax.effect_args with
              | _req::_ens::(pats,uu____937)::uu____938 ->
                  let pats' = unmeta pats  in
                  let uu____969 = head_and_args pats'  in
                  (match uu____969 with
                   | (head1,uu____980) ->
                       let uu____995 =
                         let uu____996 = un_uinst head1  in
                         uu____996.FStar_Syntax_Syntax.n  in
                       (match uu____995 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Syntax_Const.cons_lid
                        | uu____1000 -> false))
              | uu____1001 -> false)
         | uu____1007 -> false)
    | uu____1008 -> false
  
let is_ml_comp c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Comp c1 ->
      (FStar_Ident.lid_equals c1.FStar_Syntax_Syntax.comp_typ_name
         FStar_Syntax_Const.effect_ML_lid)
        ||
        (FStar_All.pipe_right c1.FStar_Syntax_Syntax.flags
           (FStar_Util.for_some
              (fun uu___172_1022  ->
                 match uu___172_1022 with
                 | FStar_Syntax_Syntax.MLEFFECT  -> true
                 | uu____1023 -> false)))
  | uu____1024 -> false 
let is_trivial_wp c =
  FStar_All.pipe_right (comp_flags c)
    (FStar_Util.for_some
       (fun uu___173_1037  ->
          match uu___173_1037 with
          | FStar_Syntax_Syntax.TOTAL |FStar_Syntax_Syntax.RETURN  -> true
          | uu____1038 -> false))
  
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
  | uu____1060 -> false 
let rec unascribe : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun e  ->
    let e1 = FStar_Syntax_Subst.compress e  in
    match e1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_ascribed (e2,uu____1066,uu____1067) ->
        unascribe e2
    | uu____1086 -> e1
  
let rec ascribe t k =
  match t.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Tm_ascribed (t',uu____1118,uu____1119) ->
      ascribe t' k
  | uu____1138 ->
      FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_ascribed (t, k, None))
        None t.FStar_Syntax_Syntax.pos
  
type eq_result =
  | Equal 
  | NotEqual 
  | Unknown 
let uu___is_Equal : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Equal  -> true | uu____1155 -> false
  
let uu___is_NotEqual : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | NotEqual  -> true | uu____1159 -> false
  
let uu___is_Unknown : eq_result -> Prims.bool =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1163 -> false
  
let rec eq_tm :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term -> eq_result =
  fun t1  ->
    fun t2  ->
      let t11 = unascribe t1  in
      let t21 = unascribe t2  in
      let equal_if uu___174_1183 = if uu___174_1183 then Equal else Unknown
         in
      let equal_iff uu___175_1188 = if uu___175_1188 then Equal else NotEqual
         in
      let eq_and f g = match f with | Equal  -> g () | uu____1202 -> Unknown
         in
      match ((t11.FStar_Syntax_Syntax.n), (t21.FStar_Syntax_Syntax.n)) with
      | (FStar_Syntax_Syntax.Tm_name a,FStar_Syntax_Syntax.Tm_name b) ->
          equal_if (FStar_Syntax_Syntax.bv_eq a b)
      | (FStar_Syntax_Syntax.Tm_fvar f,FStar_Syntax_Syntax.Tm_fvar g) ->
          let uu____1207 = FStar_Syntax_Syntax.fv_eq f g  in
          equal_if uu____1207
      | (FStar_Syntax_Syntax.Tm_uinst (f,us),FStar_Syntax_Syntax.Tm_uinst
         (g,vs)) ->
          let uu____1220 = eq_tm f g  in
          eq_and uu____1220
            (fun uu____1221  ->
               let uu____1222 = eq_univs_list us vs  in equal_if uu____1222)
      | (FStar_Syntax_Syntax.Tm_constant c,FStar_Syntax_Syntax.Tm_constant d)
          ->
          let uu____1225 = FStar_Const.eq_const c d  in equal_iff uu____1225
      | (FStar_Syntax_Syntax.Tm_uvar
         (u1,uu____1227),FStar_Syntax_Syntax.Tm_uvar (u2,uu____1229)) ->
          let uu____1254 = FStar_Unionfind.equivalent u1 u2  in
          equal_if uu____1254
      | (FStar_Syntax_Syntax.Tm_app (h1,args1),FStar_Syntax_Syntax.Tm_app
         (h2,args2)) ->
          let uu____1290 = eq_tm h1 h2  in
          eq_and uu____1290 (fun uu____1291  -> eq_args args1 args2)
      | (FStar_Syntax_Syntax.Tm_type u,FStar_Syntax_Syntax.Tm_type v1) ->
          let uu____1294 = eq_univs u v1  in equal_if uu____1294
      | (FStar_Syntax_Syntax.Tm_meta (t12,uu____1296),uu____1297) ->
          eq_tm t12 t21
      | (uu____1302,FStar_Syntax_Syntax.Tm_meta (t22,uu____1304)) ->
          eq_tm t11 t22
      | uu____1309 -> Unknown

and eq_args :
  FStar_Syntax_Syntax.args -> FStar_Syntax_Syntax.args -> eq_result =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | ([],[]) -> Equal
      | ((a,uu____1333)::a11,(b,uu____1336)::b1) ->
          let uu____1374 = eq_tm a b  in
          (match uu____1374 with
           | Equal  -> eq_args a11 b1
           | uu____1375 -> Unknown)
      | uu____1376 -> Unknown

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
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1390) ->
        unrefine x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1396,uu____1397) ->
        unrefine t2
    | uu____1416 -> t1
  
let rec is_unit : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1420 =
      let uu____1421 = unrefine t  in uu____1421.FStar_Syntax_Syntax.n  in
    match uu____1420 with
    | FStar_Syntax_Syntax.Tm_type uu____1424 -> true
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.unit_lid) ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.squash_lid)
    | FStar_Syntax_Syntax.Tm_uinst (t1,uu____1427) -> is_unit t1
    | uu____1432 -> false
  
let is_fun : FStar_Syntax_Syntax.term -> Prims.bool =
  fun e  ->
    let uu____1436 =
      let uu____1437 = FStar_Syntax_Subst.compress e  in
      uu____1437.FStar_Syntax_Syntax.n  in
    match uu____1436 with
    | FStar_Syntax_Syntax.Tm_abs uu____1440 -> true
    | uu____1455 -> false
  
let is_function_typ : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let uu____1459 =
      let uu____1460 = FStar_Syntax_Subst.compress t  in
      uu____1460.FStar_Syntax_Syntax.n  in
    match uu____1459 with
    | FStar_Syntax_Syntax.Tm_arrow uu____1463 -> true
    | uu____1471 -> false
  
let rec pre_typ : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_refine (x,uu____1477) ->
        pre_typ x.FStar_Syntax_Syntax.sort
    | FStar_Syntax_Syntax.Tm_ascribed (t2,uu____1483,uu____1484) ->
        pre_typ t2
    | uu____1503 -> t1
  
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
      let uu____1517 =
        let uu____1518 = un_uinst typ1  in uu____1518.FStar_Syntax_Syntax.n
         in
      match uu____1517 with
      | FStar_Syntax_Syntax.Tm_app (head1,args) ->
          let head2 = un_uinst head1  in
          (match head2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some args
           | uu____1556 -> None)
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc lid -> Some []
      | uu____1572 -> None
  
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
    match lids_of_sigelt se with | l::[] -> Some l | uu____1649 -> None
  
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
  
let range_of_lb uu___176_1832 =
  match uu___176_1832 with
  | (FStar_Util.Inl x,uu____1839,uu____1840) ->
      FStar_Syntax_Syntax.range_of_bv x
  | (FStar_Util.Inr l,uu____1844,uu____1845) -> FStar_Ident.range_of_lid l 
let range_of_arg uu____1862 =
  match uu____1862 with | (hd1,uu____1868) -> hd1.FStar_Syntax_Syntax.pos 
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
      let uu____1982 =
        let uu____1985 =
          let uu____1986 =
            let uu____1991 =
              FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
                (Some FStar_Syntax_Syntax.Data_ctor)
               in
            (uu____1991,
              (FStar_Syntax_Syntax.Meta_desugared
                 FStar_Syntax_Syntax.Data_app))
             in
          FStar_Syntax_Syntax.Tm_meta uu____1986  in
        FStar_Syntax_Syntax.mk uu____1985  in
      uu____1982 None (FStar_Ident.range_of_lid l)
  | uu____2000 ->
      let e =
        let uu____2009 =
          FStar_Syntax_Syntax.fvar l FStar_Syntax_Syntax.Delta_constant
            (Some FStar_Syntax_Syntax.Data_ctor)
           in
        mk_app uu____2009 args  in
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
      let uu____2024 =
        let uu____2027 =
          FStar_Util.substring_from x.FStar_Ident.idText
            (Prims.parse_int "7")
           in
        (uu____2027, (x.FStar_Ident.idRange))  in
      FStar_Ident.mk_ident uu____2024
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
          let uu____2060 = FStar_Syntax_Syntax.is_null_bv x  in
          if uu____2060
          then
            let uu____2061 =
              let uu____2064 =
                let uu____2065 = FStar_Util.string_of_int i  in
                Prims.strcat "_" uu____2065  in
              let uu____2066 = FStar_Syntax_Syntax.range_of_bv x  in
              (uu____2064, uu____2066)  in
            FStar_Ident.mk_ident uu____2061
          else x.FStar_Syntax_Syntax.ppname  in
        let y =
          let uu___179_2069 = x  in
          {
            FStar_Syntax_Syntax.ppname = nm;
            FStar_Syntax_Syntax.index =
              (uu___179_2069.FStar_Syntax_Syntax.index);
            FStar_Syntax_Syntax.sort =
              (uu___179_2069.FStar_Syntax_Syntax.sort)
          }  in
        let uu____2070 = mk_field_projector_name_from_ident lid nm  in
        (uu____2070, y)
  
let set_uvar uv t =
  let uu____2087 = FStar_Unionfind.find uv  in
  match uu____2087 with
  | FStar_Syntax_Syntax.Fixed uu____2090 ->
      let uu____2091 =
        let uu____2092 =
          let uu____2093 = FStar_Unionfind.uvar_id uv  in
          FStar_All.pipe_left FStar_Util.string_of_int uu____2093  in
        FStar_Util.format1 "Changing a fixed uvar! ?%s\n" uu____2092  in
      failwith uu____2091
  | uu____2095 -> FStar_Unionfind.change uv (FStar_Syntax_Syntax.Fixed t) 
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
      | uu____2142 -> q1 = q2
  
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
                 let uu____2228 =
                   let uu____2234 = FStar_Syntax_Subst.close_lcomp bs lc  in
                   FStar_Util.Inl uu____2234  in
                 Some uu____2228
              in
           match bs with
           | [] -> t
           | uu____2245 ->
               let body =
                 let uu____2250 = FStar_Syntax_Subst.close bs t  in
                 FStar_Syntax_Subst.compress uu____2250  in
               (match ((body.FStar_Syntax_Syntax.n), lopt) with
                | (FStar_Syntax_Syntax.Tm_abs (bs',t1,lopt'),None ) ->
                    let uu____2293 =
                      let uu____2296 =
                        let uu____2297 =
                          let uu____2312 =
                            let uu____2316 =
                              FStar_Syntax_Subst.close_binders bs  in
                            FStar_List.append uu____2316 bs'  in
                          let uu____2322 = close_lopt lopt'  in
                          (uu____2312, t1, uu____2322)  in
                        FStar_Syntax_Syntax.Tm_abs uu____2297  in
                      FStar_Syntax_Syntax.mk uu____2296  in
                    uu____2293 None t1.FStar_Syntax_Syntax.pos
                | uu____2348 ->
                    let uu____2357 =
                      let uu____2360 =
                        let uu____2361 =
                          let uu____2376 =
                            FStar_Syntax_Subst.close_binders bs  in
                          let uu____2377 = close_lopt lopt  in
                          (uu____2376, body, uu____2377)  in
                        FStar_Syntax_Syntax.Tm_abs uu____2361  in
                      FStar_Syntax_Syntax.mk uu____2360  in
                    uu____2357 None t.FStar_Syntax_Syntax.pos))
  
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
      | uu____2406 ->
          let uu____2407 =
            let uu____2410 =
              let uu____2411 =
                let uu____2419 = FStar_Syntax_Subst.close_binders bs  in
                let uu____2420 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____2419, uu____2420)  in
              FStar_Syntax_Syntax.Tm_arrow uu____2411  in
            FStar_Syntax_Syntax.mk uu____2410  in
          uu____2407 None c.FStar_Syntax_Syntax.pos
  
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
      | uu____2437 ->
          let c = FStar_Syntax_Syntax.mk_Total t  in
          let uu____2439 =
            let uu____2442 =
              let uu____2443 =
                let uu____2451 = FStar_Syntax_Subst.close_binders bs  in
                let uu____2452 = FStar_Syntax_Subst.close_comp bs c  in
                (uu____2451, uu____2452)  in
              FStar_Syntax_Syntax.Tm_arrow uu____2443  in
            FStar_Syntax_Syntax.mk uu____2442  in
          uu____2439 None c.FStar_Syntax_Syntax.pos
  
let flat_arrow :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.comp ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun bs  ->
    fun c  ->
      let t = arrow bs c  in
      let uu____2470 =
        let uu____2471 = FStar_Syntax_Subst.compress t  in
        uu____2471.FStar_Syntax_Syntax.n  in
      match uu____2470 with
      | FStar_Syntax_Syntax.Tm_arrow (bs1,c1) ->
          (match c1.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Total (tres,uu____2491) ->
               let uu____2498 =
                 let uu____2499 = FStar_Syntax_Subst.compress tres  in
                 uu____2499.FStar_Syntax_Syntax.n  in
               (match uu____2498 with
                | FStar_Syntax_Syntax.Tm_arrow (bs',c') ->
                    let uu____2516 = FStar_ST.read t.FStar_Syntax_Syntax.tk
                       in
                    (FStar_Syntax_Syntax.mk
                       (FStar_Syntax_Syntax.Tm_arrow
                          ((FStar_List.append bs1 bs'), c'))) uu____2516
                      t.FStar_Syntax_Syntax.pos
                | uu____2536 -> t)
           | uu____2537 -> t)
      | uu____2538 -> t
  
let refine :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun b  ->
    fun t  ->
      let uu____2547 =
        FStar_ST.read (b.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.tk  in
      let uu____2552 =
        let uu____2553 = FStar_Syntax_Syntax.range_of_bv b  in
        FStar_Range.union_ranges uu____2553 t.FStar_Syntax_Syntax.pos  in
      let uu____2554 =
        let uu____2557 =
          let uu____2558 =
            let uu____2563 =
              let uu____2564 =
                let uu____2565 = FStar_Syntax_Syntax.mk_binder b  in
                [uu____2565]  in
              FStar_Syntax_Subst.close uu____2564 t  in
            (b, uu____2563)  in
          FStar_Syntax_Syntax.Tm_refine uu____2558  in
        FStar_Syntax_Syntax.mk uu____2557  in
      uu____2554 uu____2547 uu____2552
  
let branch : FStar_Syntax_Syntax.branch -> FStar_Syntax_Syntax.branch =
  fun b  -> FStar_Syntax_Subst.close_branch b 
let tot_or_gtot_result c =
  match c.FStar_Syntax_Syntax.n with
  | FStar_Syntax_Syntax.Total (t,_)|FStar_Syntax_Syntax.GTotal (t,_) -> t
  | uu____2603 -> failwith "Expected a Tot or GTot computation" 
let rec arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list *
      FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        let uu____2632 = FStar_Syntax_Subst.open_comp bs c  in
        (match uu____2632 with
         | (bs1,c1) ->
             let uu____2642 = is_tot_or_gtot_comp c1  in
             if uu____2642
             then
               let uu____2648 =
                 let uu____2654 = tot_or_gtot_result c1  in
                 arrow_formals_comp uu____2654  in
               (match uu____2648 with
                | (bs',k2) -> ((FStar_List.append bs1 bs'), k2))
             else (bs1, c1))
    | uu____2674 ->
        let uu____2675 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____2675)
  
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
            let uu___180_2736 = l1  in
            let uu____2737 =
              FStar_List.map
                (fun uu____2747  ->
                   match uu____2747 with
                   | (t1,imp) ->
                       let uu____2754 = FStar_Syntax_Subst.subst s t1  in
                       (uu____2754, imp))
                l1.FStar_Syntax_Syntax.lcomp_indices
               in
            let uu____2755 =
              FStar_Syntax_Subst.subst s l1.FStar_Syntax_Syntax.lcomp_res_typ
               in
            {
              FStar_Syntax_Syntax.lcomp_name =
                (uu___180_2736.FStar_Syntax_Syntax.lcomp_name);
              FStar_Syntax_Syntax.lcomp_univs =
                (uu___180_2736.FStar_Syntax_Syntax.lcomp_univs);
              FStar_Syntax_Syntax.lcomp_indices = uu____2737;
              FStar_Syntax_Syntax.lcomp_res_typ = uu____2755;
              FStar_Syntax_Syntax.lcomp_cflags =
                (uu___180_2736.FStar_Syntax_Syntax.lcomp_cflags);
              FStar_Syntax_Syntax.lcomp_as_comp =
                (fun uu____2758  ->
                   let uu____2759 = l1.FStar_Syntax_Syntax.lcomp_as_comp ()
                      in
                   FStar_Syntax_Subst.subst_comp s uu____2759)
            }  in
          Some (FStar_Util.Inl l2)
      | uu____2768 -> l  in
    let rec aux t1 abs_body_lcomp =
      let uu____2806 =
        let uu____2807 =
          let uu____2810 = FStar_Syntax_Subst.compress t1  in
          FStar_All.pipe_left unascribe uu____2810  in
        uu____2807.FStar_Syntax_Syntax.n  in
      match uu____2806 with
      | FStar_Syntax_Syntax.Tm_abs (bs,t2,what) ->
          let uu____2848 = aux t2 what  in
          (match uu____2848 with
           | (bs',t3,what1) -> ((FStar_List.append bs bs'), t3, what1))
      | uu____2905 -> ([], t1, abs_body_lcomp)  in
    let uu____2917 = aux t None  in
    match uu____2917 with
    | (bs,t1,abs_body_lcomp) ->
        let uu____2965 = FStar_Syntax_Subst.open_term' bs t1  in
        (match uu____2965 with
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
                | (Some fvs,uu____3065) ->
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
            let uu____3126 = FStar_Syntax_Subst.open_univ_vars_comp uvs c  in
            (match uu____3126 with | (uvs1,c1) -> (uvs1, [], c1))
        | uu____3142 ->
            let t' = arrow binders c  in
            let uu____3147 = FStar_Syntax_Subst.open_univ_vars uvs t'  in
            (match uu____3147 with
             | (uvs1,t'1) ->
                 let uu____3158 =
                   let uu____3159 = FStar_Syntax_Subst.compress t'1  in
                   uu____3159.FStar_Syntax_Syntax.n  in
                 (match uu____3158 with
                  | FStar_Syntax_Syntax.Tm_arrow (binders1,c1) ->
                      (uvs1, binders1, c1)
                  | uu____3185 -> failwith "Impossible"))
  
let is_tuple_constructor : FStar_Syntax_Syntax.typ -> Prims.bool =
  fun t  ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_fvar fv ->
        FStar_Util.starts_with
          ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
          "Prims.tuple"
    | uu____3200 -> false
  
let mk_tuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3208 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "tuple%s" uu____3208  in
      let uu____3209 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range uu____3209 r
  
let mk_tuple_data_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3217 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "Mktuple%s" uu____3217  in
      let uu____3218 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range uu____3218 r
  
let is_tuple_data_lid : FStar_Ident.lident -> Prims.int -> Prims.bool =
  fun f  ->
    fun n1  ->
      let uu____3225 = mk_tuple_data_lid n1 FStar_Range.dummyRange  in
      FStar_Ident.lid_equals f uu____3225
  
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
    | uu____3243 -> false
  
let mk_dtuple_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3251 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "dtuple%s" uu____3251  in
      let uu____3252 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range uu____3252 r
  
let mk_dtuple_data_lid : Prims.int -> FStar_Range.range -> FStar_Ident.lident
  =
  fun n1  ->
    fun r  ->
      let t =
        let uu____3260 = FStar_Util.string_of_int n1  in
        FStar_Util.format1 "Mkdtuple%s" uu____3260  in
      let uu____3261 = FStar_Syntax_Const.pconst t  in
      FStar_Ident.set_lid_range uu____3261 r
  
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
      let uu____3299 =
        let uu____3300 = pre_typ t  in uu____3300.FStar_Syntax_Syntax.n  in
      match uu____3299 with
      | FStar_Syntax_Syntax.Tm_fvar tc ->
          FStar_Ident.lid_equals
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v lid
      | uu____3308 -> false
  
let rec is_constructed_typ :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident -> Prims.bool =
  fun t  ->
    fun lid  ->
      let uu____3315 =
        let uu____3316 = pre_typ t  in uu____3316.FStar_Syntax_Syntax.n  in
      match uu____3315 with
      | FStar_Syntax_Syntax.Tm_fvar uu____3319 -> is_constructor t lid
      | FStar_Syntax_Syntax.Tm_app (t1,uu____3321) ->
          is_constructed_typ t1 lid
      | uu____3336 -> false
  
let rec get_tycon :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term Prims.option =
  fun t  ->
    let t1 = pre_typ t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_bvar _
      |FStar_Syntax_Syntax.Tm_name _|FStar_Syntax_Syntax.Tm_fvar _ -> 
        Some t1
    | FStar_Syntax_Syntax.Tm_app (t2,uu____3347) -> get_tycon t2
    | uu____3362 -> None
  
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
  fun uu____3392  ->
    let u =
      let uu____3396 = FStar_Unionfind.fresh None  in
      FStar_All.pipe_left (fun _0_26  -> FStar_Syntax_Syntax.U_unif _0_26)
        uu____3396
       in
    let uu____3402 =
      (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)) None
        FStar_Range.dummyRange
       in
    (uu____3402, u)
  
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
          let uu____3440 =
            let uu____3443 =
              FStar_Range.union_ranges phi11.FStar_Syntax_Syntax.pos
                phi2.FStar_Syntax_Syntax.pos
               in
            let uu____3444 =
              let uu____3447 =
                let uu____3448 =
                  let uu____3458 =
                    let uu____3460 = FStar_Syntax_Syntax.as_arg phi11  in
                    let uu____3461 =
                      let uu____3463 = FStar_Syntax_Syntax.as_arg phi2  in
                      [uu____3463]  in
                    uu____3460 :: uu____3461  in
                  (tand, uu____3458)  in
                FStar_Syntax_Syntax.Tm_app uu____3448  in
              FStar_Syntax_Syntax.mk uu____3447  in
            uu____3444 None uu____3443  in
          Some uu____3440
  
let mk_binop op_t phi1 phi2 =
  let uu____3498 =
    FStar_Range.union_ranges phi1.FStar_Syntax_Syntax.pos
      phi2.FStar_Syntax_Syntax.pos
     in
  let uu____3499 =
    let uu____3502 =
      let uu____3503 =
        let uu____3513 =
          let uu____3515 = FStar_Syntax_Syntax.as_arg phi1  in
          let uu____3516 =
            let uu____3518 = FStar_Syntax_Syntax.as_arg phi2  in [uu____3518]
             in
          uu____3515 :: uu____3516  in
        (op_t, uu____3513)  in
      FStar_Syntax_Syntax.Tm_app uu____3503  in
    FStar_Syntax_Syntax.mk uu____3502  in
  uu____3499 None uu____3498 
let mk_neg phi =
  let uu____3539 =
    let uu____3542 =
      let uu____3543 =
        let uu____3553 =
          let uu____3555 = FStar_Syntax_Syntax.as_arg phi  in [uu____3555]
           in
        (t_not, uu____3553)  in
      FStar_Syntax_Syntax.Tm_app uu____3543  in
    FStar_Syntax_Syntax.mk uu____3542  in
  uu____3539 None phi.FStar_Syntax_Syntax.pos 
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
      let uu____3615 =
        let uu____3616 = FStar_Syntax_Subst.compress phi1  in
        uu____3616.FStar_Syntax_Syntax.n  in
      match uu____3615 with
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.false_lid ->
          t_true
      | FStar_Syntax_Syntax.Tm_fvar tc when
          FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid ->
          phi2
      | uu____3621 ->
          let uu____3622 =
            let uu____3623 = FStar_Syntax_Subst.compress phi2  in
            uu____3623.FStar_Syntax_Syntax.n  in
          (match uu____3622 with
           | FStar_Syntax_Syntax.Tm_fvar tc when
               (FStar_Syntax_Syntax.fv_eq_lid tc FStar_Syntax_Const.true_lid)
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid tc
                    FStar_Syntax_Const.false_lid)
               -> phi2
           | uu____3627 -> mk_binop timp phi1 phi2)
  
let mk_iff phi1 phi2 = mk_binop tiff phi1 phi2 
let b2t e =
  let uu____3651 =
    let uu____3654 =
      let uu____3655 =
        let uu____3665 =
          let uu____3667 = FStar_Syntax_Syntax.as_arg e  in [uu____3667]  in
        (b2t_v, uu____3665)  in
      FStar_Syntax_Syntax.Tm_app uu____3655  in
    FStar_Syntax_Syntax.mk uu____3654  in
  uu____3651 None e.FStar_Syntax_Syntax.pos 
let teq : FStar_Syntax_Syntax.term = fvar_const FStar_Syntax_Const.eq2_lid 
let mk_untyped_eq2 e1 e2 =
  let uu____3691 =
    FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
      e2.FStar_Syntax_Syntax.pos
     in
  let uu____3692 =
    let uu____3695 =
      let uu____3696 =
        let uu____3706 =
          let uu____3708 = FStar_Syntax_Syntax.as_arg e1  in
          let uu____3709 =
            let uu____3711 = FStar_Syntax_Syntax.as_arg e2  in [uu____3711]
             in
          uu____3708 :: uu____3709  in
        (teq, uu____3706)  in
      FStar_Syntax_Syntax.Tm_app uu____3696  in
    FStar_Syntax_Syntax.mk uu____3695  in
  uu____3692 None uu____3691 
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
          let uu____3734 =
            FStar_Range.union_ranges e1.FStar_Syntax_Syntax.pos
              e2.FStar_Syntax_Syntax.pos
             in
          let uu____3735 =
            let uu____3738 =
              let uu____3739 =
                let uu____3749 =
                  let uu____3751 = FStar_Syntax_Syntax.iarg t  in
                  let uu____3752 =
                    let uu____3754 = FStar_Syntax_Syntax.as_arg e1  in
                    let uu____3755 =
                      let uu____3757 = FStar_Syntax_Syntax.as_arg e2  in
                      [uu____3757]  in
                    uu____3754 :: uu____3755  in
                  uu____3751 :: uu____3752  in
                (eq_inst, uu____3749)  in
              FStar_Syntax_Syntax.Tm_app uu____3739  in
            FStar_Syntax_Syntax.mk uu____3738  in
          uu____3735 None uu____3734
  
let mk_has_type t x t' =
  let t_has_type = fvar_const FStar_Syntax_Const.has_type_lid  in
  let t_has_type1 =
    FStar_Syntax_Syntax.mk
      (FStar_Syntax_Syntax.Tm_uinst
         (t_has_type,
           [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero])) None
      FStar_Range.dummyRange
     in
  let uu____3795 =
    let uu____3798 =
      let uu____3799 =
        let uu____3809 =
          let uu____3811 = FStar_Syntax_Syntax.iarg t  in
          let uu____3812 =
            let uu____3814 = FStar_Syntax_Syntax.as_arg x  in
            let uu____3815 =
              let uu____3817 = FStar_Syntax_Syntax.as_arg t'  in [uu____3817]
               in
            uu____3814 :: uu____3815  in
          uu____3811 :: uu____3812  in
        (t_has_type1, uu____3809)  in
      FStar_Syntax_Syntax.Tm_app uu____3799  in
    FStar_Syntax_Syntax.mk uu____3798  in
  uu____3795 None FStar_Range.dummyRange 
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
      (fun uu____3833  -> FStar_Syntax_Syntax.mk_Total ktype0)
  } 
let mk_forall :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
        FStar_Syntax_Syntax.syntax
  =
  fun x  ->
    fun body  ->
      let uu____3840 =
        let uu____3843 =
          let uu____3844 =
            let uu____3854 =
              let uu____3856 =
                FStar_Syntax_Syntax.iarg x.FStar_Syntax_Syntax.sort  in
              let uu____3857 =
                let uu____3859 =
                  let uu____3860 =
                    let uu____3861 =
                      let uu____3865 = FStar_Syntax_Syntax.mk_binder x  in
                      [uu____3865]  in
                    abs uu____3861 body (Some (FStar_Util.Inl lc_tot_type0))
                     in
                  FStar_Syntax_Syntax.as_arg uu____3860  in
                [uu____3859]  in
              uu____3856 :: uu____3857  in
            (tforall, uu____3854)  in
          FStar_Syntax_Syntax.Tm_app uu____3844  in
        FStar_Syntax_Syntax.mk uu____3843  in
      uu____3840 None FStar_Range.dummyRange
  
let rec close_forall :
  FStar_Syntax_Syntax.binder Prims.list ->
    FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.typ
  =
  fun bs  ->
    fun f  ->
      FStar_List.fold_right
        (fun b  ->
           fun f1  ->
             let uu____3893 = FStar_Syntax_Syntax.is_null_binder b  in
             if uu____3893 then f1 else mk_forall (Prims.fst b) f1) bs f
  
let rec is_wild_pat p =
  match p.FStar_Syntax_Syntax.v with
  | FStar_Syntax_Syntax.Pat_wild uu____3906 -> true
  | uu____3907 -> false 
let if_then_else b t1 t2 =
  let then_branch =
    let uu____3950 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool true))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t1.FStar_Syntax_Syntax.pos
       in
    (uu____3950, None, t1)  in
  let else_branch =
    let uu____3973 =
      FStar_Syntax_Syntax.withinfo
        (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool false))
        FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n
        t2.FStar_Syntax_Syntax.pos
       in
    (uu____3973, None, t2)  in
  let uu____3985 =
    let uu____3986 =
      FStar_Range.union_ranges t1.FStar_Syntax_Syntax.pos
        t2.FStar_Syntax_Syntax.pos
       in
    FStar_Range.union_ranges b.FStar_Syntax_Syntax.pos uu____3986  in
  FStar_Syntax_Syntax.mk
    (FStar_Syntax_Syntax.Tm_match (b, [then_branch; else_branch])) None
    uu____3985
  
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let uu___is_QAll : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QAll _0 -> true | uu____4059 -> false
  
let __proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QAll _0 -> _0 
let uu___is_QEx : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | QEx _0 -> true | uu____4083 -> false
  
let __proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ)
  = fun projectee  -> match projectee with | QEx _0 -> _0 
let uu___is_BaseConn : connective -> Prims.bool =
  fun projectee  ->
    match projectee with | BaseConn _0 -> true | uu____4106 -> false
  
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
      | uu____4141 -> f2  in
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
      let rec aux f2 uu____4186 =
        match uu____4186 with
        | (lid,arity) ->
            let uu____4192 =
              let uu____4202 = unmeta_monadic f2  in head_and_args uu____4202
               in
            (match uu____4192 with
             | (t,args) ->
                 let t1 = un_uinst t  in
                 let uu____4221 =
                   (is_constructor t1 lid) &&
                     ((FStar_List.length args) = arity)
                    in
                 if uu____4221 then Some (BaseConn (lid, args)) else None)
         in
      FStar_Util.find_map connectives (aux f1)  in
    let patterns t =
      let t1 = FStar_Syntax_Subst.compress t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern pats) ->
          let uu____4272 = FStar_Syntax_Subst.compress t2  in
          (pats, uu____4272)
      | uu____4279 ->
          let uu____4280 = FStar_Syntax_Subst.compress t1  in
          ([], uu____4280)
       in
    let destruct_q_conn t =
      let is_q fa fv =
        if fa
        then is_forall (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
        else is_exists (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      let flat t1 =
        let uu____4322 = head_and_args t1  in
        match uu____4322 with
        | (t2,args) ->
            let uu____4353 = un_uinst t2  in
            let uu____4354 =
              FStar_All.pipe_right args
                (FStar_List.map
                   (fun uu____4370  ->
                      match uu____4370 with
                      | (t3,imp) ->
                          let uu____4377 = unascribe t3  in (uu____4377, imp)))
               in
            (uu____4353, uu____4354)
         in
      let rec aux qopt out t1 =
        let uu____4400 = let uu____4409 = flat t1  in (qopt, uu____4409)  in
        match uu____4400 with
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
        | (Some b,uu____4668) ->
            let bs = FStar_List.rev out  in
            let uu____4686 = FStar_Syntax_Subst.open_term bs t1  in
            (match uu____4686 with
             | (bs1,t2) ->
                 let uu____4692 = patterns t2  in
                 (match uu____4692 with
                  | (pats,body) ->
                      if b
                      then Some (QAll (bs1, pats, body))
                      else Some (QEx (bs1, pats, body))))
        | uu____4730 -> None  in
      aux None [] t  in
    let phi = unmeta_monadic f  in
    let uu____4742 = destruct_base_conn phi  in
    match uu____4742 with | Some b -> Some b | None  -> destruct_q_conn phi
  
let action_as_lb :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.sigelt
  =
  fun eff_lid  ->
    fun a  ->
      let lb =
        let uu____4753 =
          let uu____4756 =
            FStar_Syntax_Syntax.lid_as_fv a.FStar_Syntax_Syntax.action_name
              FStar_Syntax_Syntax.Delta_equational None
             in
          FStar_Util.Inr uu____4756  in
        close_univs_and_mk_letbinding None uu____4753
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
  let uu____4785 =
    let uu____4788 =
      let uu____4789 =
        let uu____4799 =
          let uu____4801 = FStar_Syntax_Syntax.as_arg t  in [uu____4801]  in
        (reify_, uu____4799)  in
      FStar_Syntax_Syntax.Tm_app uu____4789  in
    FStar_Syntax_Syntax.mk uu____4788  in
  uu____4785 None t.FStar_Syntax_Syntax.pos 
let rec delta_qualifier :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.delta_depth =
  fun t  ->
    let t1 = FStar_Syntax_Subst.compress t  in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_delayed uu____4817 -> failwith "Impossible"
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
    let uu____4923 =
      let uu____4924 = FStar_Syntax_Subst.compress t  in
      uu____4924.FStar_Syntax_Syntax.n  in
    match uu____4923 with
    | FStar_Syntax_Syntax.Tm_unknown  -> true
    | uu____4927 -> false
  
let rec list_elements :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term Prims.list Prims.option
  =
  fun e  ->
    let uu____4935 = let uu____4945 = unmeta e  in head_and_args uu____4945
       in
    match uu____4935 with
    | (head1,args) ->
        let uu____4964 =
          let uu____4972 =
            let uu____4973 = un_uinst head1  in
            uu____4973.FStar_Syntax_Syntax.n  in
          (uu____4972, args)  in
        (match uu____4964 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4984) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid ->
             Some []
         | (FStar_Syntax_Syntax.Tm_fvar
            fv,uu____4997::(hd1,uu____4999)::(tl1,uu____5001)::[]) when
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.cons_lid ->
             let uu____5035 =
               let uu____5039 =
                 let uu____5043 = list_elements tl1  in
                 FStar_Util.must uu____5043  in
               hd1 :: uu____5039  in
             Some uu____5035
         | uu____5052 -> None)
  