open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list
let mk t s =
  FStar_Syntax_Syntax.mk s FStar_Pervasives_Native.None
    t.FStar_Syntax_Syntax.pos
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
      | FStar_Syntax_Syntax.Tm_delayed uu____101 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____114 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____115 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____124 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____133 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____134 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____135 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____136 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____156 =
            let uu____157 =
              let uu____166 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____166) in
            FStar_Syntax_Syntax.Tm_abs uu____157 in
          mk1 uu____156
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___148_188 = bv in
            let uu____189 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___148_188.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___148_188.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____189
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____204 =
            let uu____205 =
              let uu____213 = inst s t2 in
              let uu____214 = inst_args s args in (uu____213, uu____214) in
            FStar_Syntax_Syntax.Tm_app uu____205 in
          mk1 uu____204
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____280  ->
                    match uu____280 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____302 = inst s w in
                              FStar_Pervasives_Native.Some uu____302 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____306 =
            let uu____307 = let uu____319 = inst s t2 in (uu____319, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____307 in
          mk1 uu____306
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____364 =
            match uu____364 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____398 = inst s t2 in FStar_Util.Inl uu____398
                  | FStar_Util.Inr c ->
                      let uu____403 = inst_comp s c in
                      FStar_Util.Inr uu____403 in
                (annot1, topt1) in
          let uu____410 =
            let uu____411 =
              let uu____425 = inst s t11 in
              let uu____426 = inst_asc asc in (uu____425, uu____426, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____411 in
          mk1 uu____410
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____454 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___149_464 = lb in
                      let uu____465 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____467 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___149_464.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___149_464.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____465;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___149_464.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____467
                      })) in
            ((FStar_Pervasives_Native.fst lbs), uu____454) in
          let uu____471 =
            let uu____472 = let uu____479 = inst s t2 in (lbs1, uu____479) in
            FStar_Syntax_Syntax.Tm_let uu____472 in
          mk1 uu____471
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____492 =
            let uu____493 =
              let uu____497 = inst s t2 in
              let uu____498 =
                let uu____499 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____499 in
              (uu____497, uu____498) in
            FStar_Syntax_Syntax.Tm_meta uu____493 in
          mk1 uu____492
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____530 =
            let uu____531 =
              let uu____535 = inst s t2 in
              let uu____536 =
                let uu____537 = let uu____541 = inst s t' in (m, uu____541) in
                FStar_Syntax_Syntax.Meta_monadic uu____537 in
              (uu____535, uu____536) in
            FStar_Syntax_Syntax.Tm_meta uu____531 in
          mk1 uu____530
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____546 =
            let uu____547 = let uu____551 = inst s t2 in (uu____551, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____547 in
          mk1 uu____546
and inst_binders:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____569  ->
              match uu____569 with
              | (x,imp) ->
                  let uu____576 =
                    let uu___150_577 = x in
                    let uu____578 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___150_577.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___150_577.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____578
                    } in
                  (uu____576, imp)))
and inst_args:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____605  ->
              match uu____605 with
              | (a,imp) -> let uu____612 = inst s a in (uu____612, imp)))
and inst_comp:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp
  =
  fun s  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uopt) ->
          let uu____627 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____627 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____634 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____634 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___151_637 = ct in
            let uu____638 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____640 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____645 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___147_652  ->
                      match uu___147_652 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____655 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____655
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___151_637.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___151_637.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____638;
              FStar_Syntax_Syntax.effect_args = uu____640;
              FStar_Syntax_Syntax.flags = uu____645
            } in
          FStar_Syntax_Syntax.mk_Comp ct1
and inst_lcomp_opt:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____667 =
            let uu___152_668 = rc in
            let uu____669 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___152_668.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____669;
              FStar_Syntax_Syntax.residual_flags =
                (uu___152_668.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____667
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____683 ->
          let inst_fv t1 fv =
            let uu____691 =
              FStar_Util.find_opt
                (fun uu____700  ->
                   match uu____700 with
                   | (x,uu____704) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____691 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____707,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t