open Prims
type inst_t = (FStar_Ident.lident* FStar_Syntax_Syntax.universes) Prims.list
let mk t s =
  let uu____31 = FStar_ST.read t.FStar_Syntax_Syntax.tk in
  FStar_Syntax_Syntax.mk s uu____31 t.FStar_Syntax_Syntax.pos
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
      | FStar_Syntax_Syntax.Tm_delayed uu____128 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____149 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____150 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____159 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____168 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____169 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____170 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____171 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____204 =
            let uu____205 =
              let uu____220 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____220) in
            FStar_Syntax_Syntax.Tm_abs uu____205 in
          mk1 uu____204
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___157_258 = bv in
            let uu____259 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___157_258.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___157_258.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____259
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____279 =
            let uu____280 =
              let uu____290 = inst s t2 in
              let uu____291 = inst_args s args in (uu____290, uu____291) in
            FStar_Syntax_Syntax.Tm_app uu____280 in
          mk1 uu____279
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____368  ->
                    match uu____368 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | None  -> None
                          | Some w ->
                              let uu____394 = inst s w in Some uu____394 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____399 =
            let uu____400 = let uu____416 = inst s t2 in (uu____416, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____400 in
          mk1 uu____399
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____472 =
            match uu____472 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____513 = inst s t2 in FStar_Util.Inl uu____513
                  | FStar_Util.Inr c ->
                      let uu____521 = inst_comp s c in
                      FStar_Util.Inr uu____521 in
                (annot1, topt1) in
          let uu____531 =
            let uu____532 =
              let uu____550 = inst s t11 in
              let uu____551 = inst_asc asc in (uu____550, uu____551, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____532 in
          mk1 uu____531
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____583 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___158_589 = lb in
                      let uu____590 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____593 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___158_589.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___158_589.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____590;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___158_589.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____593
                      })) in
            ((fst lbs), uu____583) in
          let uu____598 =
            let uu____599 = let uu____607 = inst s t2 in (lbs1, uu____607) in
            FStar_Syntax_Syntax.Tm_let uu____599 in
          mk1 uu____598
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____623 =
            let uu____624 =
              let uu____629 = inst s t2 in
              let uu____630 =
                let uu____631 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____631 in
              (uu____629, uu____630) in
            FStar_Syntax_Syntax.Tm_meta uu____624 in
          mk1 uu____623
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____671 =
            let uu____672 =
              let uu____677 = inst s t2 in
              let uu____678 =
                let uu____679 = let uu____684 = inst s t' in (m, uu____684) in
                FStar_Syntax_Syntax.Meta_monadic uu____679 in
              (uu____677, uu____678) in
            FStar_Syntax_Syntax.Tm_meta uu____672 in
          mk1 uu____671
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____691 =
            let uu____692 = let uu____697 = inst s t2 in (uu____697, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____692 in
          mk1 uu____691
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
           (fun uu____711  ->
              match uu____711 with
              | (x,imp) ->
                  let uu____718 =
                    let uu___159_719 = x in
                    let uu____720 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___159_719.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___159_719.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____720
                    } in
                  (uu____718, imp)))
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
           (fun uu____746  ->
              match uu____746 with
              | (a,imp) -> let uu____753 = inst s a in (uu____753, imp)))
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
          let uu____772 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____772 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____781 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____781 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___160_784 = ct in
            let uu____785 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____788 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____794 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___156_798  ->
                      match uu___156_798 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____802 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____802
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___160_784.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___160_784.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____785;
              FStar_Syntax_Syntax.effect_args = uu____788;
              FStar_Syntax_Syntax.flags = uu____794
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
      | None  -> l
      | Some (FStar_Util.Inr uu____829) -> l
      | Some (FStar_Util.Inl lc) ->
          let uu____850 =
            let uu____856 =
              let uu___161_857 = lc in
              let uu____858 = inst s lc.FStar_Syntax_Syntax.res_typ in
              {
                FStar_Syntax_Syntax.eff_name =
                  (uu___161_857.FStar_Syntax_Syntax.eff_name);
                FStar_Syntax_Syntax.res_typ = uu____858;
                FStar_Syntax_Syntax.cflags =
                  (uu___161_857.FStar_Syntax_Syntax.cflags);
                FStar_Syntax_Syntax.comp =
                  (fun uu____861  ->
                     let uu____862 = lc.FStar_Syntax_Syntax.comp () in
                     inst_comp s uu____862)
              } in
            FStar_Util.Inl uu____856 in
          Some uu____850
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____883 ->
          let inst_fv t1 fv =
            let uu____891 =
              FStar_Util.find_opt
                (fun uu____897  ->
                   match uu____897 with
                   | (x,uu____901) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____891 with
            | None  -> t1
            | Some (uu____908,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t