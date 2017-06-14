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
      | FStar_Syntax_Syntax.Tm_uvar uu____156 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____167 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____168 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____169 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____170 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____203 =
            let uu____204 =
              let uu____219 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____219) in
            FStar_Syntax_Syntax.Tm_abs uu____204 in
          mk1 uu____203
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___147_257 = bv in
            let uu____258 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___147_257.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___147_257.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____258
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____278 =
            let uu____279 =
              let uu____289 = inst s t2 in
              let uu____290 = inst_args s args in (uu____289, uu____290) in
            FStar_Syntax_Syntax.Tm_app uu____279 in
          mk1 uu____278
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____360  ->
                    match uu____360 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | None  -> None
                          | Some w ->
                              let uu____382 = inst s w in Some uu____382 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____386 =
            let uu____387 = let uu____402 = inst s t2 in (uu____402, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____387 in
          mk1 uu____386
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____457 =
            match uu____457 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____498 = inst s t2 in FStar_Util.Inl uu____498
                  | FStar_Util.Inr c ->
                      let uu____506 = inst_comp s c in
                      FStar_Util.Inr uu____506 in
                (annot1, topt1) in
          let uu____516 =
            let uu____517 =
              let uu____535 = inst s t11 in
              let uu____536 = inst_asc asc in (uu____535, uu____536, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____517 in
          mk1 uu____516
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____568 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___148_574 = lb in
                      let uu____575 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____578 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___148_574.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___148_574.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____575;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___148_574.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____578
                      })) in
            ((fst lbs), uu____568) in
          let uu____583 =
            let uu____584 = let uu____592 = inst s t2 in (lbs1, uu____592) in
            FStar_Syntax_Syntax.Tm_let uu____584 in
          mk1 uu____583
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____608 =
            let uu____609 =
              let uu____614 = inst s t2 in
              let uu____615 =
                let uu____616 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____616 in
              (uu____614, uu____615) in
            FStar_Syntax_Syntax.Tm_meta uu____609 in
          mk1 uu____608
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____656 =
            let uu____657 =
              let uu____662 = inst s t2 in
              let uu____663 =
                let uu____664 = let uu____669 = inst s t' in (m, uu____669) in
                FStar_Syntax_Syntax.Meta_monadic uu____664 in
              (uu____662, uu____663) in
            FStar_Syntax_Syntax.Tm_meta uu____657 in
          mk1 uu____656
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____676 =
            let uu____677 = let uu____682 = inst s t2 in (uu____682, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____677 in
          mk1 uu____676
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
           (fun uu____696  ->
              match uu____696 with
              | (x,imp) ->
                  let uu____703 =
                    let uu___149_704 = x in
                    let uu____705 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___149_704.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___149_704.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____705
                    } in
                  (uu____703, imp)))
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
           (fun uu____731  ->
              match uu____731 with
              | (a,imp) -> let uu____738 = inst s a in (uu____738, imp)))
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
          let uu____757 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____757 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____766 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____766 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___150_769 = ct in
            let uu____770 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____773 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____779 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___146_783  ->
                      match uu___146_783 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____787 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____787
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___150_769.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___150_769.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____770;
              FStar_Syntax_Syntax.effect_args = uu____773;
              FStar_Syntax_Syntax.flags = uu____779
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
      | Some (FStar_Util.Inr uu____814) -> l
      | Some (FStar_Util.Inl lc) ->
          let uu____835 =
            let uu____841 =
              let uu___151_842 = lc in
              let uu____843 = inst s lc.FStar_Syntax_Syntax.res_typ in
              {
                FStar_Syntax_Syntax.eff_name =
                  (uu___151_842.FStar_Syntax_Syntax.eff_name);
                FStar_Syntax_Syntax.res_typ = uu____843;
                FStar_Syntax_Syntax.cflags =
                  (uu___151_842.FStar_Syntax_Syntax.cflags);
                FStar_Syntax_Syntax.comp =
                  (fun uu____846  ->
                     let uu____847 = lc.FStar_Syntax_Syntax.comp () in
                     inst_comp s uu____847)
              } in
            FStar_Util.Inl uu____841 in
          Some uu____835
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____866 ->
          let inst_fv t1 fv =
            let uu____874 =
              FStar_Util.find_opt
                (fun uu____880  ->
                   match uu____880 with
                   | (x,uu____884) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____874 with
            | None  -> t1
            | Some (uu____887,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t