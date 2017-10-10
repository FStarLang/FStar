open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let mk:
  'Auu____15 'Auu____16 .
    'Auu____16 FStar_Syntax_Syntax.syntax ->
      'Auu____15 -> 'Auu____15 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____117 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____142 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____143 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____160 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____177 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____178 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____179 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____180 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs in
          let body1 = inst s body in
          let uu____213 =
            let uu____214 =
              let uu____231 = inst_lcomp_opt s lopt in
              (bs1, body1, uu____231) in
            FStar_Syntax_Syntax.Tm_abs uu____214 in
          mk1 uu____213
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs in
          let c1 = inst_comp s c in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___152_267 = bv in
            let uu____268 = inst s bv.FStar_Syntax_Syntax.sort in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___152_267.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___152_267.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____268
            } in
          let t3 = inst s t2 in mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____294 =
            let uu____295 =
              let uu____310 = inst s t2 in
              let uu____311 = inst_args s args in (uu____310, uu____311) in
            FStar_Syntax_Syntax.Tm_app uu____295 in
          mk1 uu____294
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____433  ->
                    match uu____433 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____471 = inst s w in
                              FStar_Pervasives_Native.Some uu____471 in
                        let t4 = inst s t3 in (p, wopt1, t4))) in
          let uu____477 =
            let uu____478 = let uu____501 = inst s t2 in (uu____501, pats1) in
            FStar_Syntax_Syntax.Tm_match uu____478 in
          mk1 uu____477
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____584 =
            match uu____584 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s) in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____646 = inst s t2 in FStar_Util.Inl uu____646
                  | FStar_Util.Inr c ->
                      let uu____654 = inst_comp s c in
                      FStar_Util.Inr uu____654 in
                (annot1, topt1) in
          let uu____667 =
            let uu____668 =
              let uu____695 = inst s t11 in
              let uu____696 = inst_asc asc in (uu____695, uu____696, f) in
            FStar_Syntax_Syntax.Tm_ascribed uu____668 in
          mk1 uu____667
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____748 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___153_762 = lb in
                      let uu____763 = inst s lb.FStar_Syntax_Syntax.lbtyp in
                      let uu____766 = inst s lb.FStar_Syntax_Syntax.lbdef in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___153_762.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___153_762.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____763;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___153_762.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____766
                      })) in
            ((FStar_Pervasives_Native.fst lbs), uu____748) in
          let uu____773 =
            let uu____774 = let uu____787 = inst s t2 in (lbs1, uu____787) in
            FStar_Syntax_Syntax.Tm_let uu____774 in
          mk1 uu____773
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____810 =
            let uu____811 =
              let uu____818 = inst s t2 in
              let uu____819 =
                let uu____820 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s)) in
                FStar_Syntax_Syntax.Meta_pattern uu____820 in
              (uu____818, uu____819) in
            FStar_Syntax_Syntax.Tm_meta uu____811 in
          mk1 uu____810
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____878 =
            let uu____879 =
              let uu____886 = inst s t2 in
              let uu____887 =
                let uu____888 = let uu____895 = inst s t' in (m, uu____895) in
                FStar_Syntax_Syntax.Meta_monadic uu____888 in
              (uu____886, uu____887) in
            FStar_Syntax_Syntax.Tm_meta uu____879 in
          mk1 uu____878
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____902 =
            let uu____903 = let uu____910 = inst s t2 in (uu____910, tag) in
            FStar_Syntax_Syntax.Tm_meta uu____903 in
          mk1 uu____902
and inst_binders:
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____935  ->
              match uu____935 with
              | (x,imp) ->
                  let uu____946 =
                    let uu___154_947 = x in
                    let uu____948 = inst s x.FStar_Syntax_Syntax.sort in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___154_947.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___154_947.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____948
                    } in
                  (uu____946, imp)))
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
           (fun uu____991  ->
              match uu____991 with
              | (a,imp) -> let uu____1002 = inst s a in (uu____1002, imp)))
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
          let uu____1023 = inst s t in
          FStar_Syntax_Syntax.mk_Total' uu____1023 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1034 = inst s t in
          FStar_Syntax_Syntax.mk_GTotal' uu____1034 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___155_1037 = ct in
            let uu____1038 = inst s ct.FStar_Syntax_Syntax.result_typ in
            let uu____1041 = inst_args s ct.FStar_Syntax_Syntax.effect_args in
            let uu____1050 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___151_1060  ->
                      match uu___151_1060 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1064 = inst s t in
                          FStar_Syntax_Syntax.DECREASES uu____1064
                      | f -> f)) in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___155_1037.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___155_1037.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1038;
              FStar_Syntax_Syntax.effect_args = uu____1041;
              FStar_Syntax_Syntax.flags = uu____1050
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
          let uu____1079 =
            let uu___156_1080 = rc in
            let uu____1081 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s) in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___156_1080.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1081;
              FStar_Syntax_Syntax.residual_flags =
                (uu___156_1080.FStar_Syntax_Syntax.residual_flags)
            } in
          FStar_Pervasives_Native.Some uu____1079
let instantiate:
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1100 ->
          let inst_fv t1 fv =
            let uu____1108 =
              FStar_Util.find_opt
                (fun uu____1122  ->
                   match uu____1122 with
                   | (x,uu____1128) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i in
            match uu____1108 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1133,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us)) in
          inst inst_fv t