open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let mk:
  'Auu____11 'Auu____12 .
    'Auu____12 FStar_Syntax_Syntax.syntax ->
      'Auu____11 -> 'Auu____11 FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
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
      | FStar_Syntax_Syntax.Tm_delayed uu____113 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____138 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____139 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____156 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____173 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____174 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____175 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____176 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____209 =
            let uu____210 =
              let uu____227 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____227) in
            FStar_Syntax_Syntax.Tm_abs uu____210 in
          mk1 uu____209
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___198_263 = bv in
            let uu____264 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___198_263.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___198_263.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____264
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____290 =
            let uu____291 =
              let uu____306 = inst s t2 in
              let uu____307 = inst_args s args in (uu____306, uu____307) in
            FStar_Syntax_Syntax.Tm_app uu____291 in
          mk1 uu____290
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____429  ->
                    match uu____429 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____467 = inst s w in
                              FStar_Pervasives_Native.Some uu____467 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____473 =
            let uu____474 = let uu____497 = inst s t2 in (uu____497, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____474 in
          mk1 uu____473
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____580 =
            match uu____580 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____642 = inst s t2 in FStar_Util.Inl uu____642
                  | FStar_Util.Inr c ->
                      let uu____650 = inst_comp s c in
                      FStar_Util.Inr uu____650 in
                (annot1, topt1) in
          let uu____663 =
            let uu____664 =
              let uu____691 = inst s t11 in
              let uu____692 = inst_asc asc in (uu____691, uu____692, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____664 in
          mk1 uu____663
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____744 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___199_758 = lb in
                      let uu____759 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____762 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___199_758.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___199_758.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____759;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___199_758.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____762
                      })) in
            ((FStar_Pervasives_Native.fst lbs), uu____744) in
          let uu____769 =
            let uu____770 = let uu____783 = inst s t2 in (lbs1, uu____783) in
            FStar_Syntax_Syntax.Tm_let uu____770 in
          mk1 uu____769
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____806 =
            let uu____807 =
              let uu____814 = inst s t2 in
              let uu____815 =
                let uu____816 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____816 in
              (uu____814, uu____815) in
            FStar_Syntax_Syntax.Tm_meta uu____807 in
          mk1 uu____806
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____874 =
            let uu____875 =
              let uu____882 = inst s t2 in
              let uu____883 =
                let uu____884 = let uu____891 = inst s t' in (m, uu____891) in
                FStar_Syntax_Syntax.Meta_monadic uu____884 in
              (uu____882, uu____883) in
            FStar_Syntax_Syntax.Tm_meta uu____875 in
          mk1 uu____874
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____898 =
            let uu____899 = let uu____906 = inst s t2 in (uu____906, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____899 in
          mk1 uu____898
and inst_binders:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____931  ->
              match uu____931 with
              | (x,imp) ->
                  let uu____942 =
                    let uu___200_943 = x in
                    let uu____944 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___200_943.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___200_943.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____944
                    } in
                  (uu____942, imp)))
and inst_args:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____987  ->
              match uu____987 with
              | (a,imp) -> let uu____998 = inst s a in (uu____998, imp)))
and inst_comp:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax
  =
  fun s  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uopt) ->
          let uu____1019 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____1019 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1030 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____1030 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___201_1033 = ct in
            let uu____1034 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____1037 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____1046 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___197_1056  ->
                      match uu___197_1056 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1060 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____1060
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___201_1033.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___201_1033.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1034;
              FStar_Syntax_Syntax.effect_args = uu____1037;
              FStar_Syntax_Syntax.flags = uu____1046
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
          let uu____1075 =
            let uu___202_1076 = rc in
            let uu____1077 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___202_1076.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1077;
              FStar_Syntax_Syntax.residual_flags =
                (uu___202_1076.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____1075
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1094 ->
          let inst_fv t1 fv =
            let uu____1102 =
              FStar_Util.find_opt
                (fun uu____1116  ->
                   match uu____1116 with
                   | (x,uu____1122) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____1102 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1127,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t