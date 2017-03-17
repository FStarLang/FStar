open Prims
type free_vars_and_fvars =
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
let no_free_vars :
  (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set) =
  let _0_672 = FStar_Syntax_Syntax.new_fv_set ()  in
  ({
     FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
     FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
     FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars;
     FStar_Syntax_Syntax.free_univ_names =
       FStar_Syntax_Syntax.no_universe_names
   }, _0_672)
  
let singleton_fvar :
  FStar_Syntax_Syntax.fv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun fv  ->
    let _0_674 =
      let _0_673 = FStar_Syntax_Syntax.new_fv_set ()  in
      FStar_Util.set_add
        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v _0_673
       in
    ({
       FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
       FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
       FStar_Syntax_Syntax.free_univs = FStar_Syntax_Syntax.no_universe_uvars;
       FStar_Syntax_Syntax.free_univ_names =
         FStar_Syntax_Syntax.no_universe_names
     }, _0_674)
  
let singleton_bv :
  FStar_Syntax_Syntax.bv ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let _0_678 =
      let _0_676 =
        let _0_675 = FStar_Syntax_Syntax.new_bv_set ()  in
        FStar_Util.set_add x _0_675  in
      {
        FStar_Syntax_Syntax.free_names = uu____36;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      }  in
    let _0_677 = FStar_Syntax_Syntax.new_fv_set ()  in (_0_678, _0_677)
  
let singleton_uv :
  ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis
    FStar_Unionfind.uvar *
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
    FStar_Syntax_Syntax.syntax) ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let _0_682 =
      let _0_680 =
        let _0_679 = FStar_Syntax_Syntax.new_uv_set ()  in
        FStar_Util.set_add x _0_679  in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = uu____68;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      }  in
    let _0_681 = FStar_Syntax_Syntax.new_fv_set ()  in (_0_682, _0_681)
  
let singleton_univ :
  FStar_Syntax_Syntax.universe_uvar ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let _0_686 =
      let _0_684 =
        let _0_683 = FStar_Syntax_Syntax.new_universe_uvar_set ()  in
        FStar_Util.set_add x _0_683  in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs = uu____108;
        FStar_Syntax_Syntax.free_univ_names =
          FStar_Syntax_Syntax.no_universe_names
      }  in
    let _0_685 = FStar_Syntax_Syntax.new_fv_set ()  in (_0_686, _0_685)
  
let singleton_univ_name :
  FStar_Syntax_Syntax.univ_name ->
    (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun x  ->
    let _0_690 =
      let _0_688 =
        let _0_687 = FStar_Syntax_Syntax.new_universe_names_fifo_set ()  in
        FStar_Util.fifo_set_add x _0_687  in
      {
        FStar_Syntax_Syntax.free_names = FStar_Syntax_Syntax.no_names;
        FStar_Syntax_Syntax.free_uvars = FStar_Syntax_Syntax.no_uvs;
        FStar_Syntax_Syntax.free_univs =
          FStar_Syntax_Syntax.no_universe_uvars;
        FStar_Syntax_Syntax.free_univ_names = _0_688
      }  in
    let _0_689 = FStar_Syntax_Syntax.new_fv_set ()  in (_0_690, _0_689)
  
let union f1 f2 =
  let uu____164 =
    let uu____165 =
      FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_names
        (Prims.fst f2).FStar_Syntax_Syntax.free_names
       in
    let _0_693 =
      FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_uvars
        (Prims.fst f2).FStar_Syntax_Syntax.free_uvars
       in
    let _0_692 =
      FStar_Util.set_union (Prims.fst f1).FStar_Syntax_Syntax.free_univs
        (Prims.fst f2).FStar_Syntax_Syntax.free_univs
       in
    let _0_691 =
      FStar_Util.fifo_set_union
        (Prims.fst f1).FStar_Syntax_Syntax.free_univ_names
        (Prims.fst f2).FStar_Syntax_Syntax.free_univ_names
       in
    {
      FStar_Syntax_Syntax.free_names = _0_694;
      FStar_Syntax_Syntax.free_uvars = _0_693;
      FStar_Syntax_Syntax.free_univs = _0_692;
      FStar_Syntax_Syntax.free_univ_names = _0_691
    }  in
  let _0_695 = FStar_Util.set_union (Prims.snd f1) (Prims.snd f2)  in
  (_0_696, _0_695) 
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
    | FStar_Syntax_Syntax.U_succ u1 -> free_univs u1
    | FStar_Syntax_Syntax.U_max us ->
        FStar_List.fold_left
          (fun out  ->
             fun x  -> let _0_697 = free_univs x  in union out _0_697)
          no_free_vars us
    | FStar_Syntax_Syntax.U_unif u -> singleton_univ u
  
let rec free_names_and_uvs' :
  FStar_Syntax_Syntax.term -> Prims.bool -> free_vars_and_fvars =
  fun tm  ->
    fun use_cache  ->
      let aux_binders bs from_body =
        let from_binders =
          FStar_All.pipe_right bs
            (FStar_List.fold_left
               (fun n1  ->
                  fun uu____342  ->
                    match uu____342 with
                    | (x,uu____352) ->
                        let uu____353 =
                          free_names_and_uvars x.FStar_Syntax_Syntax.sort
                            use_cache
                           in
                        union n _0_698) no_free_vars)
           in
        union from_binders from_body  in
      let t = FStar_Syntax_Subst.compress tm  in
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____358 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name x -> singleton_bv x
      | FStar_Syntax_Syntax.Tm_uvar (x,t1) -> singleton_uv (x, t1)
      | FStar_Syntax_Syntax.Tm_type u -> free_univs u
      | FStar_Syntax_Syntax.Tm_bvar uu____401 -> no_free_vars
      | FStar_Syntax_Syntax.Tm_fvar fv -> singleton_fvar fv
      | FStar_Syntax_Syntax.Tm_constant _|FStar_Syntax_Syntax.Tm_unknown  ->
          no_free_vars
      | FStar_Syntax_Syntax.Tm_uinst (t,us) ->
          let f = free_names_and_uvars t use_cache  in
          FStar_List.fold_left
            (fun out  ->
               fun u  -> let _0_699 = free_univs u  in union out _0_699) f us
      | FStar_Syntax_Syntax.Tm_abs (bs,t,uu____344) ->
          let _0_700 = free_names_and_uvars t use_cache  in
          aux_binders bs _0_700
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let _0_701 = free_names_and_uvars_comp c use_cache  in
          aux_binders bs _0_701
      | FStar_Syntax_Syntax.Tm_refine (bv,t) ->
          let _0_702 = free_names_and_uvars t use_cache  in
          aux_binders [(bv, None)] _0_702
      | FStar_Syntax_Syntax.Tm_app (t,args) ->
          let _0_703 = free_names_and_uvars t use_cache  in
          free_names_and_uvars_args args _0_703 use_cache
      | FStar_Syntax_Syntax.Tm_match (t,pats) ->
          let _0_708 =
            let _0_707 = free_names_and_uvars t use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun uu____569  ->
                   match uu____569 with
                   | (p,wopt,t2) ->
                       let n11 =
                         match wopt with
                         | None  -> no_free_vars
                         | Some w -> free_names_and_uvars w use_cache  in
                       let n2 = free_names_and_uvars t use_cache  in
                       let n =
                         let _0_705 = FStar_Syntax_Syntax.pat_bvs p  in
                         FStar_All.pipe_right _0_705
                           (FStar_List.fold_left
                              (fun n3  ->
                                 fun x  ->
                                   let uu____633 =
                                     free_names_and_uvars
                                       x.FStar_Syntax_Syntax.sort use_cache
                                      in
                                   union n _0_704) n)
                          in
                       let _0_706 = union n1 n2  in union n _0_706) _0_707
             in
          FStar_All.pipe_right pats _0_708
      | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inl t2,uu____526) ->
          let _0_710 = free_names_and_uvars t1 use_cache  in
          let _0_709 = free_names_and_uvars t2 use_cache  in
          union _0_710 _0_709
      | FStar_Syntax_Syntax.Tm_ascribed (t1,FStar_Util.Inr c,uu____547) ->
          let _0_712 = free_names_and_uvars t1 use_cache  in
          let _0_711 = free_names_and_uvars_comp c use_cache  in
          union _0_712 _0_711
      | FStar_Syntax_Syntax.Tm_let (lbs,t) ->
          let _0_717 =
            let _0_716 = free_names_and_uvars t use_cache  in
            FStar_List.fold_left
              (fun n1  ->
                 fun lb  ->
                   let uu____775 =
                     let uu____779 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbtyp
                         use_cache
                        in
                     let _0_713 =
                       free_names_and_uvars lb.FStar_Syntax_Syntax.lbdef
                         use_cache
                        in
                     union _0_714 _0_713  in
                   union n _0_715) _0_716
             in
          FStar_All.pipe_right (Prims.snd lbs) _0_717
      | FStar_Syntax_Syntax.Tm_meta (t,FStar_Syntax_Syntax.Meta_pattern args)
          ->
          let _0_718 = free_names_and_uvars t use_cache  in
          FStar_List.fold_right
            (fun a  -> fun acc  -> free_names_and_uvars_args a acc use_cache)
            args uu____804
      | FStar_Syntax_Syntax.Tm_meta
          (t,FStar_Syntax_Syntax.Meta_monadic (uu____622,t')) ->
          let _0_720 = free_names_and_uvars t use_cache  in
          let _0_719 = free_names_and_uvars t' use_cache  in
          union _0_720 _0_719
      | FStar_Syntax_Syntax.Tm_meta (t,uu____633) ->
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
      let uu____643 = FStar_ST.read t.FStar_Syntax_Syntax.vars  in
      match uu____643 with
      | Some n when Prims.op_Negation (should_invalidate_cache n use_cache)
          -> let _0_721 = FStar_Syntax_Syntax.new_fv_set ()  in (n, _0_721)
      | uu____653 ->
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
                fun uu____692  ->
                  match uu____692 with
                  | (x,uu____704) ->
                      let _0_722 = free_names_and_uvars x use_cache  in
                      union n _0_722) acc)

and free_names_and_uvars_binders bs acc use_cache =
  FStar_All.pipe_right bs
    (FStar_List.fold_left
       (fun n  ->
          fun uu____730  ->
            match uu____730 with
            | (x,uu____740) ->
                let _0_723 =
                  free_names_and_uvars x.FStar_Syntax_Syntax.sort use_cache
                   in
                union n _0_723) acc)

and free_names_and_uvars_comp :
  (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
    Prims.bool ->
      (FStar_Syntax_Syntax.free_vars * FStar_Ident.lident FStar_Util.set)
  =
  fun c  ->
    fun use_cache  ->
      let uu____745 = FStar_ST.read c.FStar_Syntax_Syntax.vars  in
      match uu____745 with
      | Some n ->
          let uu____754 = should_invalidate_cache n use_cache  in
          (match uu____754 with
           | true  ->
               (FStar_ST.write c.FStar_Syntax_Syntax.vars None;
                free_names_and_uvars_comp c use_cache)
           | uu____762 ->
               let _0_724 = FStar_Syntax_Syntax.new_fv_set ()  in (n, _0_724))
      | uu____764 ->
          let n =
            match c.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.GTotal (t,None )|FStar_Syntax_Syntax.Total
              (t,None ) -> free_names_and_uvars t use_cache
            | FStar_Syntax_Syntax.GTotal (t,Some u)|FStar_Syntax_Syntax.Total
              (t,Some u) ->
                let _0_726 = free_univs u  in
                let _0_725 = free_names_and_uvars t use_cache  in
                union _0_726 _0_725
            | FStar_Syntax_Syntax.Comp ct ->
                let us =
                  let uu____1032 =
                    free_names_and_uvars ct.FStar_Syntax_Syntax.result_typ
                      use_cache
                     in
                  free_names_and_uvars_args
                    ct.FStar_Syntax_Syntax.effect_args _0_727 use_cache
                   in
                FStar_List.fold_left
                  (fun us  ->
                     fun u  -> let _0_728 = free_univs u  in union us _0_728)
                  us ct.FStar_Syntax_Syntax.comp_univs
             in
          (FStar_ST.write c.FStar_Syntax_Syntax.vars (Some (Prims.fst n)); n)

and should_invalidate_cache :
  FStar_Syntax_Syntax.free_vars -> Prims.bool -> Prims.bool =
  fun n1  ->
    fun use_cache  ->
      (Prims.op_Negation use_cache) ||
        ((let _0_729 =
            FStar_All.pipe_right n.FStar_Syntax_Syntax.free_uvars
              FStar_Util.set_elements
             in
          FStar_All.pipe_right _0_729
            (FStar_Util.for_some
               (fun uu____856  ->
                  match uu____856 with
                  | (u,uu____866) ->
                      let uu____879 = FStar_Unionfind.find u  in
                      (match uu____879 with
                       | FStar_Syntax_Syntax.Fixed uu____886 -> true
                       | uu____891 -> false))))
           ||
           (let _0_730 =
              FStar_All.pipe_right n.FStar_Syntax_Syntax.free_univs
                FStar_Util.set_elements
               in
            FStar_All.pipe_right _0_730
              (FStar_Util.for_some
                 (fun u  ->
                    let uu____903 = FStar_Unionfind.find u  in
                    match uu____903 with
                    | Some uu____906 -> true
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
  