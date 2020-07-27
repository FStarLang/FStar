open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'uuuuuu14 'uuuuuu15 .
    'uuuuuu14 FStar_Syntax_Syntax.syntax ->
      'uuuuuu15 -> 'uuuuuu15 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____144 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____159 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____160 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____173 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____186 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____187 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____188 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____189 -> t1
      | FStar_Syntax_Syntax.Tm_unknown -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____196 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____203 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____234 =
            let uu____235 =
              let uu____254 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____254) in
            FStar_Syntax_Syntax.Tm_abs uu____235 in
          mk1 uu____234
      | FStar_Syntax_Syntax.Tm_arrow (bs, c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv, t2) ->
          let bv1 =
            let uu___47_312 = bv in
            let uu____313 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___47_312.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___47_312.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____313
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2, args) ->
          let uu____345 =
            let uu____346 =
              let uu____363 = inst s t2 in
              let uu____366 = inst_args s args in (uu____363, uu____366) in
            FStar_Syntax_Syntax.Tm_app uu____346 in
          mk1 uu____345
      | FStar_Syntax_Syntax.Tm_match (t2, pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____498 ->
                    match uu____498 with
                    | (p, wopt, t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____536 = inst s w in
                              FStar_Pervasives_Native.Some uu____536 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____542 =
            let uu____543 = let uu____566 = inst s t2 in (uu____566, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____543 in
          mk1 uu____542
      | FStar_Syntax_Syntax.Tm_ascribed (t11, asc, f) ->
          let inst_asc uu____659 =
            match uu____659 with
            | (annot, topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____721 = inst s t2 in FStar_Util.Inl uu____721
                  | FStar_Util.Inr c ->
                      let uu____729 = inst_comp s c in
                      FStar_Util.Inr uu____729 in
                (annot1, topt1) in
          let uu____742 =
            let uu____743 =
              let uu____770 = inst s t11 in
              let uu____773 = inst_asc asc in (uu____770, uu____773, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____743 in
          mk1 uu____742
      | FStar_Syntax_Syntax.Tm_let (lbs, t2) ->
          let lbs1 =
            let uu____835 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb ->
                      let uu___89_849 = lb in
                      let uu____850 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____853 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___89_849.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___89_849.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____850;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___89_849.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____853;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___89_849.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___89_849.FStar_Syntax_Syntax.lbpos)
                      })) in
            ((FStar_Pervasives_Native.fst lbs), uu____835) in
          let uu____860 =
            let uu____861 = let uu____874 = inst s t2 in (lbs1, uu____874) in
            FStar_Syntax_Syntax.Tm_let uu____861 in
          mk1 uu____860
      | FStar_Syntax_Syntax.Tm_meta
          (t2, FStar_Syntax_Syntax.Meta_pattern (bvs, args)) ->
          let uu____924 =
            let uu____925 =
              let uu____932 = inst s t2 in
              let uu____935 =
                let uu____936 =
                  let uu____957 =
                    FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                  (bvs, uu____957) in
                FStar_Syntax_Syntax.Meta_pattern uu____936 in
              (uu____932, uu____935) in
            FStar_Syntax_Syntax.Tm_meta uu____925 in
          mk1 uu____924
      | FStar_Syntax_Syntax.Tm_meta
          (t2, FStar_Syntax_Syntax.Meta_monadic (m, t')) ->
          let uu____1043 =
            let uu____1044 =
              let uu____1051 = inst s t2 in
              let uu____1054 =
                let uu____1055 =
                  let uu____1062 = inst s t' in (m, uu____1062) in
                FStar_Syntax_Syntax.Meta_monadic uu____1055 in
              (uu____1051, uu____1054) in
            FStar_Syntax_Syntax.Tm_meta uu____1044 in
          mk1 uu____1043
      | FStar_Syntax_Syntax.Tm_meta (t2, tag) ->
          let uu____1075 =
            let uu____1076 = let uu____1083 = inst s t2 in (uu____1083, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____1076 in
          mk1 uu____1075
and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s ->
    fun bs ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____1118 ->
              match uu____1118 with
              | (x, imp) ->
                  let uu____1137 =
                    let uu___115_1138 = x in
                    let uu____1139 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___115_1138.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___115_1138.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1139
                    } in
                  (uu____1137, imp)))
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
           (fun uu____1194 ->
              match uu____1194 with
              | (a, imp) -> let uu____1213 = inst s a in (uu____1213, imp)))
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
          let uu____1236 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____1236 uopt
      | FStar_Syntax_Syntax.GTotal (t, uopt) ->
          let uu____1247 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____1247 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___134_1250 = ct in
            let uu____1251 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____1254 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____1265 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___0_1275 ->
                      match uu___0_1275 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1279 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____1279
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___134_1250.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___134_1250.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1251;
              FStar_Syntax_Syntax.effect_args = uu____1254;
              FStar_Syntax_Syntax.flags = uu____1265
            } in
          FStar_Syntax_Syntax.mk_Comp ct1
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
          let uu____1294 =
            let uu___146_1295 = rc in
            let uu____1296 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___146_1295.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1296;
              FStar_Syntax_Syntax.residual_flags =
                (uu___146_1295.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____1294
let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i ->
    fun t ->
      match i with
      | [] -> t
      | uu____1319 ->
          let inst_fv t1 fv =
            let uu____1331 =
              FStar_Util.find_opt
                (fun uu____1345 ->
                   match uu____1345 with
                   | (x, uu____1351) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____1331 with
            | FStar_Pervasives_Native.None -> t1
            | FStar_Pervasives_Native.Some (uu____1356, us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t