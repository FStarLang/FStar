open Prims
type inst_t = (FStar_Ident.lident* FStar_Syntax_Syntax.universes) Prims.list
let mk t s =
  let uu____26 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
  FStar_Syntax_Syntax.mk s uu____26 t.FStar_Syntax_Syntax.pos
let rec inst:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t in
      let mk1 = mk t1 in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____123 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name _
        |FStar_Syntax_Syntax.Tm_uvar _
         |FStar_Syntax_Syntax.Tm_uvar _
          |FStar_Syntax_Syntax.Tm_type _
           |FStar_Syntax_Syntax.Tm_bvar _
            |FStar_Syntax_Syntax.Tm_constant _
             |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_uinst _
          -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____179 =
            let uu____180 =
              let uu____195 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____195) in
            FStar_Syntax_Syntax.Tm_abs uu____180 in
          mk1 uu____179
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___158_233 = bv in
            let uu____234 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___158_233.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___158_233.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____234
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____254 =
            let uu____255 =
              let uu____265 = inst s t2 in
              let uu____266 = inst_args s args in (uu____265, uu____266) in
            FStar_Syntax_Syntax.Tm_app uu____255 in
          mk1 uu____254
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____343  ->
                    match uu____343 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | None  -> None
                          | Some w ->
                              let uu____369 = inst s w in Some uu____369 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____374 =
            let uu____375 = let uu____391 = inst s t2 in (uu____391, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____375 in
          mk1 uu____374
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____447 =
            match uu____447 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____488 = inst s t2 in FStar_Util.Inl uu____488
                  | FStar_Util.Inr c ->
                      let uu____496 = inst_comp s c in
                      FStar_Util.Inr uu____496 in
                (annot1, topt1) in
          let uu____506 =
            let uu____507 =
              let uu____525 = inst s t11 in
              let uu____526 = inst_asc asc in (uu____525, uu____526, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____507 in
          mk1 uu____506
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____558 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___159_564 = lb in
                      let uu____565 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____568 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___159_564.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___159_564.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____565;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___159_564.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____568
                      })) in
            ((fst lbs), uu____558) in
          let uu____573 =
            let uu____574 = let uu____582 = inst s t2 in (lbs1, uu____582) in
            FStar_Syntax_Syntax.Tm_let uu____574 in
          mk1 uu____573
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____598 =
            let uu____599 =
              let uu____604 = inst s t2 in
              let uu____605 =
                let uu____606 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____606 in
              (uu____604, uu____605) in
            FStar_Syntax_Syntax.Tm_meta uu____599 in
          mk1 uu____598
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____646 =
            let uu____647 =
              let uu____652 = inst s t2 in
              let uu____653 =
                let uu____654 = let uu____659 = inst s t' in (m, uu____659) in
                FStar_Syntax_Syntax.Meta_monadic uu____654 in
              (uu____652, uu____653) in
            FStar_Syntax_Syntax.Tm_meta uu____647 in
          mk1 uu____646
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____666 =
            let uu____667 = let uu____672 = inst s t2 in (uu____672, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____667 in
          mk1 uu____666
and inst_binders:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____686  ->
              match uu____686 with
              | (x,imp) ->
                  let uu____693 =
                    let uu___160_694 = x in
                    let uu____695 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___160_694.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___160_694.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____695
                    } in
                  (uu____693, imp)))
and inst_args:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax* FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____721  ->
              match uu____721 with
              | (a,imp) -> let uu____728 = inst s a in (uu____728, imp)))
and inst_comp:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.comp',Prims.unit) FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uopt) ->
          let uu____747 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____747 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____756 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____756 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___161_759 = ct in
            let uu____760 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____763 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____769 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___157_773  ->
                      match uu___157_773 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____777 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____777
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___161_759.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___161_759.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____760;
              FStar_Syntax_Syntax.effect_args = uu____763;
              FStar_Syntax_Syntax.flags = uu____769
            } in
          FStar_Syntax_Syntax.mk_Comp ct1
and inst_lcomp_opt:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                 FStar_Syntax_Syntax.cflags Prims.list))
      FStar_Util.either option ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident*
                                   FStar_Syntax_Syntax.cflags Prims.list))
        FStar_Util.either option
  =
  fun s  ->
    fun l  ->
      match l with
      | None |Some (FStar_Util.Inr _) -> l
      | Some (FStar_Util.Inl lc) ->
          let uu____822 =
            let uu____828 =
              let uu___162_829 = lc in
              let uu____830 = inst s lc.FStar_Syntax_Syntax.res_typ in
              {
                FStar_Syntax_Syntax.eff_name =
                  (uu___162_829.FStar_Syntax_Syntax.eff_name);
                FStar_Syntax_Syntax.res_typ = uu____830;
                FStar_Syntax_Syntax.cflags =
                  (uu___162_829.FStar_Syntax_Syntax.cflags);
                FStar_Syntax_Syntax.comp =
                  (fun uu____833  ->
                     let uu____834 = lc.FStar_Syntax_Syntax.comp () in
                     inst_comp s uu____834)
              } in
            FStar_Util.Inl uu____828 in
          Some uu____822
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____853 ->
          let inst_fv t1 fv =
            let uu____861 =
              FStar_Util.find_opt
                (fun uu____867  ->
                   match uu____867 with
                   | (x,uu____871) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____861 with
            | None  -> t1
            | Some (uu____878,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t