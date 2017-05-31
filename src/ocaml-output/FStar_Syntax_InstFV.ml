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
      | FStar_Syntax_Syntax.Tm_name uu____144 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____145 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____154 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____163 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____164 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____165 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____166 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____199 =
            let uu____200 =
              let uu____215 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____215) in
            FStar_Syntax_Syntax.Tm_abs uu____200 in
          mk1 uu____199
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___146_253 = bv in
            let uu____254 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___146_253.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___146_253.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____254
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____274 =
            let uu____275 =
              let uu____285 = inst s t2 in
              let uu____286 = inst_args s args in (uu____285, uu____286) in
            FStar_Syntax_Syntax.Tm_app uu____275 in
          mk1 uu____274
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____363  ->
                    match uu____363 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | None  -> None
                          | Some w ->
                              let uu____389 = inst s w in Some uu____389 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____394 =
            let uu____395 = let uu____411 = inst s t2 in (uu____411, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____395 in
          mk1 uu____394
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____467 =
            match uu____467 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____508 = inst s t2 in FStar_Util.Inl uu____508
                  | FStar_Util.Inr c ->
                      let uu____516 = inst_comp s c in
                      FStar_Util.Inr uu____516 in
                (annot1, topt1) in
          let uu____526 =
            let uu____527 =
              let uu____545 = inst s t11 in
              let uu____546 = inst_asc asc in (uu____545, uu____546, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____527 in
          mk1 uu____526
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____578 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___147_584 = lb in
                      let uu____585 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____588 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___147_584.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___147_584.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____585;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___147_584.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____588
                      })) in
            ((fst lbs), uu____578) in
          let uu____593 =
            let uu____594 = let uu____602 = inst s t2 in (lbs1, uu____602) in
            FStar_Syntax_Syntax.Tm_let uu____594 in
          mk1 uu____593
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____618 =
            let uu____619 =
              let uu____624 = inst s t2 in
              let uu____625 =
                let uu____626 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____626 in
              (uu____624, uu____625) in
            FStar_Syntax_Syntax.Tm_meta uu____619 in
          mk1 uu____618
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____666 =
            let uu____667 =
              let uu____672 = inst s t2 in
              let uu____673 =
                let uu____674 = let uu____679 = inst s t' in (m, uu____679) in
                FStar_Syntax_Syntax.Meta_monadic uu____674 in
              (uu____672, uu____673) in
            FStar_Syntax_Syntax.Tm_meta uu____667 in
          mk1 uu____666
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____686 =
            let uu____687 = let uu____692 = inst s t2 in (uu____692, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____687 in
          mk1 uu____686
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
           (fun uu____706  ->
              match uu____706 with
              | (x,imp) ->
                  let uu____713 =
                    let uu___148_714 = x in
                    let uu____715 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___148_714.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___148_714.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____715
                    } in
                  (uu____713, imp)))
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
           (fun uu____741  ->
              match uu____741 with
              | (a,imp) -> let uu____748 = inst s a in (uu____748, imp)))
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
          let uu____767 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____767 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____776 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____776 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___149_779 = ct in
            let uu____780 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____783 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____789 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___145_793  ->
                      match uu___145_793 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____797 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____797
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___149_779.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___149_779.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____780;
              FStar_Syntax_Syntax.effect_args = uu____783;
              FStar_Syntax_Syntax.flags = uu____789
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
      | Some (FStar_Util.Inr uu____824) -> l
      | Some (FStar_Util.Inl lc) ->
          let uu____845 =
            let uu____851 =
              let uu___150_852 = lc in
              let uu____853 = inst s lc.FStar_Syntax_Syntax.res_typ in
              {
                FStar_Syntax_Syntax.eff_name =
                  (uu___150_852.FStar_Syntax_Syntax.eff_name);
                FStar_Syntax_Syntax.res_typ = uu____853;
                FStar_Syntax_Syntax.cflags =
                  (uu___150_852.FStar_Syntax_Syntax.cflags);
                FStar_Syntax_Syntax.comp =
                  (fun uu____856  ->
                     let uu____857 = lc.FStar_Syntax_Syntax.comp () in
                     inst_comp s uu____857)
              } in
            FStar_Util.Inl uu____851 in
          Some uu____845
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____876 ->
          let inst_fv t1 fv =
            let uu____884 =
              FStar_Util.find_opt
                (fun uu____890  ->
                   match uu____890 with
                   | (x,uu____894) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____884 with
            | None  -> t1
            | Some (uu____901,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t