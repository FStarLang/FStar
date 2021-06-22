open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'uuuuu 'uuuuu1 .
    'uuuuu FStar_Syntax_Syntax.syntax ->
      'uuuuu1 -> 'uuuuu1 FStar_Syntax_Syntax.syntax
  = fun t -> fun s -> FStar_Syntax_Syntax.mk s t.FStar_Syntax_Syntax.pos
let rec (inst :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun t ->
      let t1 = FStar_Syntax_Subst.compress t in
      let mk1 = mk t1 in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu___ -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu___ -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu___ -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu___ -> t1
      | FStar_Syntax_Syntax.Tm_type uu___ -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu___ -> t1
      | FStar_Syntax_Syntax.Tm_constant uu___ -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu___ -> t1
      | FStar_Syntax_Syntax.Tm_unknown -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu___ -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu___ -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu___ =
            let uu___1 =
              let uu___2 = inst_lcomp_opt s lopt in (bs1, body1, uu___2) in
            FStar_Syntax_Syntax.Tm_abs uu___1 in
          mk1 uu___
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv, t2) ->
          let bv1 =
            let uu___ = bv in
            let uu___1 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname = (uu___.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (uu___.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu___1
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2, args) ->
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t2 in
              let uu___3 = inst_args s args in (uu___2, uu___3) in
            FStar_Syntax_Syntax.Tm_app uu___1 in
          mk1 uu___
      | FStar_Syntax_Syntax.Tm_match (t2, asc_opt, pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu___ ->
                    match uu___ with
                    | (p, wopt, t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu___1 = inst s w in
                              FStar_Pervasives_Native.Some uu___1 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let asc_opt1 = FStar_Util.map_opt asc_opt (inst_ascription s) in
          let uu___ =
            let uu___1 = let uu___2 = inst s t2 in (uu___2, asc_opt1, pats1) in
            FStar_Syntax_Syntax.Tm_match uu___1 in
          mk1 uu___
      | FStar_Syntax_Syntax.Tm_ascribed (t11, asc, f) ->
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t11 in
              let uu___3 = inst_ascription s asc in (uu___2, uu___3, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu___1 in
          mk1 uu___
      | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
          let lbs1 =
            let uu___ =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb ->
                      let uu___1 = lb in
                      let uu___2 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu___3 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___1.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___1.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu___2;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___1.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu___3;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___1.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___1.FStar_Syntax_Syntax.lbpos)
                      })) in
            ((FStar_Pervasives_Native.fst lbs), uu___) in
          let uu___ =
            let uu___1 = let uu___2 = inst s t2 in (lbs1, uu___2) in
            FStar_Syntax_Syntax.Tm_let uu___1 in
          mk1 uu___
      | FStar_Syntax_Syntax.Tm_meta
          (t2, FStar_Syntax_Syntax.Meta_pattern (bvs, args)) ->
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t2 in
              let uu___3 =
                let uu___4 =
                  let uu___5 =
                    FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                  (bvs, uu___5) in
                FStar_Syntax_Syntax.Meta_pattern uu___4 in
              (uu___2, uu___3) in
            FStar_Syntax_Syntax.Tm_meta uu___1 in
          mk1 uu___
      | FStar_Syntax_Syntax.Tm_meta
          (t2, FStar_Syntax_Syntax.Meta_monadic (m, t')) ->
          let uu___ =
            let uu___1 =
              let uu___2 = inst s t2 in
              let uu___3 =
                let uu___4 = let uu___5 = inst s t' in (m, uu___5) in
                FStar_Syntax_Syntax.Meta_monadic uu___4 in
              (uu___2, uu___3) in
            FStar_Syntax_Syntax.Tm_meta uu___1 in
          mk1 uu___
      | FStar_Syntax_Syntax.Tm_meta (t2, tag) ->
          let uu___ =
            let uu___1 = let uu___2 = inst s t2 in (uu___2, tag) in
            FStar_Syntax_Syntax.Tm_meta uu___1 in
          mk1 uu___
and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s ->
    fun bs ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun b ->
              let uu___ = b in
              let uu___1 =
                let uu___2 = b.FStar_Syntax_Syntax.binder_bv in
                let uu___3 =
                  inst s
                    (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                {
                  FStar_Syntax_Syntax.ppname =
                    (uu___2.FStar_Syntax_Syntax.ppname);
                  FStar_Syntax_Syntax.index =
                    (uu___2.FStar_Syntax_Syntax.index);
                  FStar_Syntax_Syntax.sort = uu___3
                } in
              let uu___2 =
                FStar_All.pipe_right b.FStar_Syntax_Syntax.binder_attrs
                  (FStar_List.map (inst s)) in
              {
                FStar_Syntax_Syntax.binder_bv = uu___1;
                FStar_Syntax_Syntax.binder_qual =
                  (uu___.FStar_Syntax_Syntax.binder_qual);
                FStar_Syntax_Syntax.binder_attrs = uu___2
              }))
and (inst_args :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list)
  =
  fun s ->
    fun args ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu___ ->
              match uu___ with
              | (a, imp) -> let uu___1 = inst s a in (uu___1, imp)))
and (inst_comp :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s ->
    fun c ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t, uopt) ->
          let uu___ = inst s t in FStar_Syntax_Syntax.mk_Total' uu___ uopt
      | FStar_Syntax_Syntax.GTotal (t, uopt) ->
          let uu___ = inst s t in FStar_Syntax_Syntax.mk_GTotal' uu___ uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___ = ct in
            let uu___1 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu___2 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu___3 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___4 ->
                      match uu___4 with
                      | FStar_Syntax_Syntax.DECREASES dec_order ->
                          let uu___5 = inst_decreases_order s dec_order in
                          FStar_Syntax_Syntax.DECREASES uu___5
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu___1;
              FStar_Syntax_Syntax.effect_args = uu___2;
              FStar_Syntax_Syntax.flags = uu___3
            } in
          FStar_Syntax_Syntax.mk_Comp ct1
and (inst_decreases_order :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.decreases_order ->
      FStar_Syntax_Syntax.decreases_order)
  =
  fun s ->
    fun uu___ ->
      match uu___ with
      | FStar_Syntax_Syntax.Decreases_lex l ->
          let uu___1 = FStar_All.pipe_right l (FStar_List.map (inst s)) in
          FStar_Syntax_Syntax.Decreases_lex uu___1
      | FStar_Syntax_Syntax.Decreases_wf (rel, e) ->
          let uu___1 =
            let uu___2 = inst s rel in
            let uu___3 = inst s e in (uu___2, uu___3) in
          FStar_Syntax_Syntax.Decreases_wf uu___1
and (inst_lcomp_opt :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s ->
    fun l ->
      match l with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu___ =
            let uu___1 = rc in
            let uu___2 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___1.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu___2;
              FStar_Syntax_Syntax.residual_flags =
                (uu___1.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu___
and (inst_ascription :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.ascription ->
      ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,
        FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
        FStar_Pervasives.either * FStar_Syntax_Syntax.term'
        FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option))
  =
  fun s ->
    fun asc ->
      let uu___ = asc in
      match uu___ with
      | (annot, topt) ->
          let annot1 =
            match annot with
            | FStar_Pervasives.Inl t ->
                let uu___1 = inst s t in FStar_Pervasives.Inl uu___1
            | FStar_Pervasives.Inr c ->
                let uu___1 = inst_comp s c in FStar_Pervasives.Inr uu___1 in
          let topt1 = FStar_Util.map_opt topt (inst s) in (annot1, topt1)
let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i ->
    fun t ->
      match i with
      | [] -> t
      | uu___ ->
          let inst_fv t1 fv =
            let uu___1 =
              FStar_Util.find_opt
                (fun uu___2 ->
                   match uu___2 with
                   | (x, uu___3) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu___1 with
            | FStar_Pervasives_Native.None -> t1
            | FStar_Pervasives_Native.Some (uu___2, us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t