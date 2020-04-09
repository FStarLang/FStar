open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____14 'Auu____15 .
    'Auu____14 FStar_Syntax_Syntax.syntax ->
      'Auu____15 -> 'Auu____15 FStar_Syntax_Syntax.syntax
  =
  fun t  ->
    fun s  ->
      FStar_Syntax_Syntax.mk s FStar_Pervasives_Native.None
        t.FStar_Syntax_Syntax.pos
  
let rec (inst :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let mk1 = mk t1  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____145 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____161 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____162 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____175 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____188 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____189 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____190 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____191 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____198 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____205 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____236 =
            let uu____237 =
              let uu____256 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____256)  in
            FStar_Syntax_Syntax.Tm_abs uu____237  in
          mk1 uu____236
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___47_314 = bv  in
            let uu____315 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___47_314.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___47_314.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____315
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____347 =
            let uu____348 =
              let uu____365 = inst s t2  in
              let uu____368 = inst_args s args  in (uu____365, uu____368)  in
            FStar_Syntax_Syntax.Tm_app uu____348  in
          mk1 uu____347
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____500  ->
                    match uu____500 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____538 = inst s w  in
                              FStar_Pervasives_Native.Some uu____538
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____544 =
            let uu____545 = let uu____568 = inst s t2  in (uu____568, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____545  in
          mk1 uu____544
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____661 =
            match uu____661 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____723 = inst s t2  in FStar_Util.Inl uu____723
                  | FStar_Util.Inr c ->
                      let uu____731 = inst_comp s c  in
                      FStar_Util.Inr uu____731
                   in
                (annot1, topt1)
             in
          let uu____744 =
            let uu____745 =
              let uu____772 = inst s t11  in
              let uu____775 = inst_asc asc  in (uu____772, uu____775, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____745  in
          mk1 uu____744
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____840 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___89_855 = lb  in
                      let uu____856 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____859 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___89_855.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___89_855.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____856;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___89_855.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____859;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___89_855.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___89_855.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____840)  in
          let uu____868 =
            let uu____869 = let uu____883 = inst s t2  in (lbs1, uu____883)
               in
            FStar_Syntax_Syntax.Tm_let uu____869  in
          mk1 uu____868
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern (bvs,args)) ->
          let uu____934 =
            let uu____935 =
              let uu____942 = inst s t2  in
              let uu____945 =
                let uu____946 =
                  let uu____967 =
                    FStar_All.pipe_right args (FStar_List.map (inst_args s))
                     in
                  (bvs, uu____967)  in
                FStar_Syntax_Syntax.Meta_pattern uu____946  in
              (uu____942, uu____945)  in
            FStar_Syntax_Syntax.Tm_meta uu____935  in
          mk1 uu____934
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____1053 =
            let uu____1054 =
              let uu____1061 = inst s t2  in
              let uu____1064 =
                let uu____1065 =
                  let uu____1072 = inst s t'  in (m, uu____1072)  in
                FStar_Syntax_Syntax.Meta_monadic uu____1065  in
              (uu____1061, uu____1064)  in
            FStar_Syntax_Syntax.Tm_meta uu____1054  in
          mk1 uu____1053
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____1085 =
            let uu____1086 = let uu____1093 = inst s t2  in (uu____1093, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____1086  in
          mk1 uu____1085

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____1128  ->
              match uu____1128 with
              | (x,imp) ->
                  let uu____1147 =
                    let uu___115_1148 = x  in
                    let uu____1149 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___115_1148.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___115_1148.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1149
                    }  in
                  (uu____1147, imp)))

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
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1204  ->
              match uu____1204 with
              | (a,imp) -> let uu____1223 = inst s a  in (uu____1223, imp)))

and (inst_comp :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun s  ->
    fun c  ->
      match c.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Total (t,uopt) ->
          let uu____1246 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1246 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1257 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1257 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___134_1260 = ct  in
            let uu____1261 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1264 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1275 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___0_1285  ->
                      match uu___0_1285 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1289 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1289
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___134_1260.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___134_1260.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1261;
              FStar_Syntax_Syntax.effect_args = uu____1264;
              FStar_Syntax_Syntax.flags = uu____1275
            }  in
          FStar_Syntax_Syntax.mk_Comp ct1

and (inst_lcomp_opt :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some rc ->
          let uu____1304 =
            let uu___146_1305 = rc  in
            let uu____1306 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___146_1305.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1306;
              FStar_Syntax_Syntax.residual_flags =
                (uu___146_1305.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1304

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1330 ->
          let inst_fv t1 fv =
            let uu____1342 =
              FStar_Util.find_opt
                (fun uu____1356  ->
                   match uu____1356 with
                   | (x,uu____1363) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1342 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1368,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  