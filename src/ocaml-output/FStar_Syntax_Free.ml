open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
let no_free_vars :
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) =
  let _0_696 = FStar_Syntax_Syntax.new_fv_set ()  in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
     FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, _0_696)
  
let singleton_fvar :
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun fv  ->
    let _0_698 =
      let _0_697 = FStar_Syntax_Syntax.new_fv_set ()  in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v _0_697
       in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
       FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, _0_698)
  
let singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let _0_702 =
      let _0_700 =
        let _0_699 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Util.set_add x _0_699  in
      {
        FStar_Syntax_Syntax.free_names = _0_700;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      }  in
    let _0_701 = FStar_Syntax_Syntax.new_fv_set ()  in (_0_702, _0_701)
  
let singleton_uv :
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let _0_706 =
      let _0_704 =
        let _0_703 = FStar_Syntax_Syntax.new_uv_set ()  in
        FStar_Util.set_add x _0_703  in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = _0_704;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      }  in
    let _0_705 = FStar_Syntax_Syntax.new_fv_set ()  in (_0_706, _0_705)
  
let singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let _0_710 =
      let _0_708 =
        let _0_707 = FStar_Syntax_Syntax.new_universe_uvar_set ()  in
        FStar_Util.set_add x _0_707  in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs = _0_708;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      }  in
    let _0_709 = FStar_Syntax_Syntax.new_fv_set ()  in (_0_710, _0_709)
  
let singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let _0_714 =
      let _0_712 =
        let _0_711 = FStar_Syntax_Syntax.new_universe_names_fifo_set ()  in
        FStar_Util.fifo_set_add x _0_711  in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = _0_712
      }  in
    let _0_713 = FStar_Syntax_Syntax.new_fv_set ()  in (_0_714, _0_713)
  
let union f1 f2 =
  let _0_720 =
    let _0_718 =
      FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_names
        (Prims.fst f2).FStar_Syntax_Syntax.free_names
       in
    let _0_717 =
      FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_uvars
        (Prims.fst f2).FStar_Syntax_Syntax.free_uvars
       in
    let _0_716 =
      FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_univs
        (Prims.fst f2).FStar_Syntax_Syntax.free_univs
       in
    let _0_715 =
      FStar_Util.fifo_set_union
        (Prims.fst f1).FStar_Syntax_Syntax.free_univ_names
        (Prims.fst f2).FStar_Syntax_Syntax.free_univ_names
       in
    {
      FStar_Syntax_Syntax.free_names = _0_718;
      FStar_Syntax_Syntax.free_uvars = _0_717;
      FStar_Syntax_Syntax.free_univs = _0_716;
      FStar_Syntax_Syntax.free_univ_names = _0_715
    }  in
  let _0_719 = FStar_Util.set_union (Prims.snd f1) (Prims.snd f2)  in
  (_0_720, _0_719) 
let rec free_univs :
  FStar_Syntax_Syntax.universe ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun u  ->
    let uu____143 = FStar_Syntax_Subst.compress_univ u  in
    match uu____143 with
    | FStar_Syntax_Syntax.U_zero 
      |FStar_Syntax_Syntax.U_bvar _|FStar_Syntax_Syntax.U_unknown  ->
        no_free_vars
    | FStar_Syntax_Syntax.U_name uname -> singleton_univ_name uname
    | FStar_Syntax_Syntax.U_succ u -> free_univs u
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let _0_721 = free_univs x  in union out _0_721)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u -> singleton_univ u
  
let rec free_names_and_uvs' :
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars =
  fun tm  ->
    fun use_cache  ->
      let aux_binders bs from_body =
        let from_binders =
          let fold_fun n uu____268 =
            match uu____268 with
            | (x,uu____278) ->
                let _0_722 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache
                   in
                union n _0_722
             in
          FStar_All.pipe_right bs
            (FStar_List.fold_left fold_fun no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____291 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t) -> singleton_uv (x, t)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____334 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_unknown  ->
          no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
          let f = free_names_and_uvars t use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let _0_723 = free_univs u  in union out _0_723) f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____357) ->
          let _0_724 = free_names_and_uvars t use_cache  in
          aux_binders bs _0_724
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let _0_725 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs _0_725
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let _0_726 = free_names_and_uvars t use_cache  in
          aux_binders [(bv, None)] _0_726
      | FStar_Syntax_Syntax.Tm_app (t,args) ->
          let _0_727 = free_names_and_uvars t use_cache  in
          free_names_and_uvars_args args _0_727 use_cache
      | FStar_Syntax_Syntax.Tm_match (t,pats) ->
          let _0_732 =
            let _0_731 = free_names_and_uvars t use_cache  in
            FStar_List.fold_left
              (fun n  ->
                 fun uu____475  ->
                   match uu____475 with
                   | (p,wopt,t) ->
                       let n1 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache  in
                       let n2 = free_names_and_uvars t use_cache  in
                       let n =
                         let _0_729 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right _0_729
                           (FStar_List.fold_left
                              (fun n  ->
                                 fun x  ->
                                   let _0_728 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n _0_728) n)
                          in
                       let _0_730 = union n1 n2  in union n _0_730) _0_731
             in
          FStar_All.pipe_right pats _0_732
      | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inl t2,uu____539) ->
          let _0_734 = free_names_and_uvars t1 use_cache  in
          let _0_733 = free_names_and_uvars t2 use_cache  in
          union _0_734 _0_733
      | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inr c,uu____560) ->
          let _0_736 = free_names_and_uvars t1 use_cache  in
          let _0_735 = free_names_and_uvars_comp c use_cache  in
          union _0_736 _0_735
      | FStar_Syntax_Syntax.Tm_let (lbs,t) ->
          let _0_741 =
            let _0_740 = free_names_and_uvars t use_cache  in
            FStar_List.fold_left
              (fun n  ->
                 fun lb  ->
                   let _0_739 =
                     let _0_738 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let _0_737 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union _0_738 _0_737  in
                   union n _0_739) _0_740
             in
          FStar_All.pipe_right (Prims.snd lbs) _0_741
      | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern args)
          ->
          let _0_742 = free_names_and_uvars t use_cache  in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args _0_742
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic (uu____635,t')) ->
          let _0_744 = free_names_and_uvars t use_cache  in
          let _0_743 = free_names_and_uvars t' use_cache  in
          union _0_744 _0_743
      | FStar_Syntax_Syntax.Tm_meta (t,uu____646) ->
          free_names_and_uvars t use_cache

and free_names_and_uvars :
  (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun t  ->
    fun use_cache  ->
      let t = FStar_Syntax_Subst.compress t  in
      let uu____656 = FStar_ST.read t.FStar_Syntax_Syntax.vars  in
      match uu____656 with
      | Some n when Prims.op_Negation (should_invalidate_cache n use_cache)
          -> let _0_745 = FStar_Syntax_Syntax.new_fv_set ()  in (n, _0_745)
      | uu____666 ->
          (FStar_ST.write t.FStar_Syntax_Syntax.vars None;
           (let n = free_names_and_uvs' t use_cache  in
            FStar_ST.write t.FStar_Syntax_Syntax.vars (Some (Prims.fst n)); n))

and free_names_and_uvars_args :
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) ->
      Prims.bool ->
        (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun args  ->
    fun acc  ->
      fun use_cache  ->
        FStar_All.pipe_right args
          (FStar_List.fold_left
             (fun n  ->
                fun uu____705  ->
                  match uu____705 with
                  | (x,uu____717) ->
                      let _0_746 = free_names_and_uvars x use_cache  in
                      union n _0_746) acc)

and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n  ->
          fun uu____743  ->
            match uu____743 with
            | (x,uu____753) ->
                let _0_747 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache
                   in
                union n _0_747) acc)

and free_names_and_uvars_comp :
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____758 = FStar_ST.read c.FStar_Syntax_Syntax.vars  in
      match uu____758 with
      | Some n ->
          let uu____767 = should_invalidate_cache n use_cache  in
          if uu____767
          then
            (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
             free_names_and_uvars_comp c use_cache)
          else
            (let _0_748 = FStar_Syntax_Syntax.new_fv_set ()  in (n, _0_748))
      | uu____777 ->
          let n =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None )|FStar_Syntax_Syntax.Total
              (t,None ) -> free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u)|FStar_Syntax_Syntax.Total
              (t,Some u) ->
                let _0_750 = free_univs u  in
                let _0_749 = free_names_and_uvars t use_cache  in
                union _0_750 _0_749
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args no_free_vars use_cache
                   in
                FStar_List.fold_left
                  (fun us  ->
                     fun u  -> let _0_751 = free_univs u  in union us _0_751)
                  us ct.FStar_Syntax_Syntax.comp_univs
             in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (Prims.fst n)); n)

and should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let _0_752 =
            FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements
             in
          FStar_All.pipe_right _0_752
            (FStar_Util.for_some
               (fun uu____869  ->
                  match uu____869 with
                  | (u,uu____879) ->
                      let uu____892 = FStar_Unionfind.find u  in
                      (match uu____892 with
                       | FStar_Syntax_Syntax.Fixed uu____899 -> true
                       | uu____904 -> false))))
           ||
           (let _0_753 =
              FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements
               in
            FStar_All.pipe_right _0_753
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____916 = FStar_Unionfind.find u  in
                    match uu____916 with
                    | Some uu____919 -> true
                    | None  -> false))))

let names : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.bv FStar_Util.set
  =
  fun t  ->
    (Prims.fst (free_names_and_uvars t true)).FStar_Syntax_Syntax.free_names
  
let uvars :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
      FStar_Unionfind.uvar *
      (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax) FStar_Util.set
  =
  fun t  ->
    (Prims.fst (free_names_and_uvars t true)).FStar_Syntax_Syntax.free_uvars
  
let univs :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.universe_uvar FStar_Util.set
  =
  fun t  ->
    (Prims.fst (free_names_and_uvars t true)).FStar_Syntax_Syntax.free_univs
  
let univnames :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set
  =
  fun t  ->
    (Prims.fst (free_names_and_uvars t true)).FStar_Syntax_Syntax.free_univ_names
  
let fvars : FStar_Syntax_Syntax.term -> FStar_Ident.lident FStar_Util.set =
  fun t  -> Prims.snd (free_names_and_uvars t false) 
let names_of_binders :
  FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.bv FStar_Util.set =
  fun bs  ->
    (Prims.fst (free_names_and_uvars_binders bs no_free_vars true)).FStar_Syntax_Syntax.free_names
  