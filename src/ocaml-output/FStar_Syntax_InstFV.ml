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
                 (fun uu____366  ->
                    match uu____366 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | None  -> None
                          | Some w ->
                              let uu____388 = inst s w in Some uu____388 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____392 =
            let uu____393 = let uu____408 = inst s t2 in (uu____408, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____393 in
          mk1 uu____392
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____463 =
            match uu____463 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____504 = inst s t2 in FStar_Util.Inl uu____504
                  | FStar_Util.Inr c ->
                      let uu____512 = inst_comp s c in
                      FStar_Util.Inr uu____512 in
                (annot1, topt1) in
          let uu____522 =
            let uu____523 =
              let uu____541 = inst s t11 in
              let uu____542 = inst_asc asc in (uu____541, uu____542, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____523 in
          mk1 uu____522
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____574 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___148_584 = lb in
                      let uu____585 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____588 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___148_584.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___148_584.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____585;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___148_584.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____588
                      })) in
            ((fst lbs), uu____574) in
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
           (fun uu____710  ->
              match uu____710 with
              | (x,imp) ->
                  let uu____717 =
                    let uu___149_718 = x in
                    let uu____719 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___149_718.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___149_718.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____719
                    } in
                  (uu____717, imp)))
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
           (fun uu____749  ->
              match uu____749 with
              | (a,imp) -> let uu____756 = inst s a in (uu____756, imp)))
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
          let uu____775 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____775 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____784 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____784 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___150_787 = ct in
            let uu____788 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____791 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____797 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___146_804  ->
                      match uu___146_804 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____808 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____808
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___150_787.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___150_787.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____788;
              FStar_Syntax_Syntax.effect_args = uu____791;
              FStar_Syntax_Syntax.flags = uu____797
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
      | Some (FStar_Util.Inr uu____835) -> l
      | Some (FStar_Util.Inl lc) ->
          let uu____856 =
            let uu____862 =
              let uu___151_863 = lc in
              let uu____864 = inst s lc.FStar_Syntax_Syntax.res_typ in
              {
                FStar_Syntax_Syntax.eff_name =
                  (uu___151_863.FStar_Syntax_Syntax.eff_name);
                FStar_Syntax_Syntax.res_typ = uu____864;
                FStar_Syntax_Syntax.cflags =
                  (uu___151_863.FStar_Syntax_Syntax.cflags);
                FStar_Syntax_Syntax.comp =
                  (fun uu____869  ->
                     let uu____870 = lc.FStar_Syntax_Syntax.comp () in
                     inst_comp s uu____870)
              } in
            FStar_Util.Inl uu____862 in
          Some uu____856
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____889 ->
          let inst_fv t1 fv =
            let uu____897 =
              FStar_Util.find_opt
                (fun uu____906  ->
                   match uu____906 with
                   | (x,uu____910) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____897 with
            | None  -> t1
            | Some (uu____913,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t