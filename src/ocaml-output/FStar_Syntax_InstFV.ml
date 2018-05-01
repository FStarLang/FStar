open Prims
type inst_t =
  (FStar_Ident.lident,FStar_Syntax_Syntax.universes)
    FStar_Pervasives_Native.tuple2 Prims.list[@@deriving show]
let mk :
  'Auu____15 'Auu____16 .
    'Auu____15 FStar_Syntax_Syntax.syntax ->
      'Auu____16 -> 'Auu____16 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____141 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____166 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____167 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____168 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____169 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____170 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____171 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____172 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____179 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____186 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____213 =
            let uu____214 =
              let uu____231 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____231)  in
            FStar_Syntax_Syntax.Tm_abs uu____214  in
          mk1 uu____213
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___53_281 = bv  in
            let uu____282 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___53_281.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___53_281.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____282
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____310 =
            let uu____311 =
              let uu____326 = inst s t2  in
              let uu____329 = inst_args s args  in (uu____326, uu____329)  in
            FStar_Syntax_Syntax.Tm_app uu____311  in
          mk1 uu____310
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____457  ->
                    match uu____457 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____495 = inst s w  in
                              FStar_Pervasives_Native.Some uu____495
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____501 =
            let uu____502 = let uu____525 = inst s t2  in (uu____525, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____502  in
          mk1 uu____501
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____618 =
            match uu____618 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____680 = inst s t2  in FStar_Util.Inl uu____680
                  | FStar_Util.Inr c ->
                      let uu____688 = inst_comp s c  in
                      FStar_Util.Inr uu____688
                   in
                (annot1, topt1)
             in
          let uu____701 =
            let uu____702 =
              let uu____729 = inst s t11  in
              let uu____732 = inst_asc asc  in (uu____729, uu____732, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____702  in
          mk1 uu____701
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____794 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___54_808 = lb  in
                      let uu____809 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____812 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___54_808.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___54_808.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____809;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___54_808.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____812;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___54_808.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___54_808.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____794)  in
          let uu____819 =
            let uu____820 = let uu____833 = inst s t2  in (lbs1, uu____833)
               in
            FStar_Syntax_Syntax.Tm_let uu____820  in
          mk1 uu____819
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____860 =
            let uu____861 =
              let uu____868 = inst s t2  in
              let uu____871 =
                let uu____872 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____872  in
              (uu____868, uu____871)  in
            FStar_Syntax_Syntax.Tm_meta uu____861  in
          mk1 uu____860
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____932 =
            let uu____933 =
              let uu____940 = inst s t2  in
              let uu____943 =
                let uu____944 = let uu____951 = inst s t'  in (m, uu____951)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____944  in
              (uu____940, uu____943)  in
            FStar_Syntax_Syntax.Tm_meta uu____933  in
          mk1 uu____932
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____964 =
            let uu____965 = let uu____972 = inst s t2  in (uu____972, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____965  in
          mk1 uu____964

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____1001  ->
              match uu____1001 with
              | (x,imp) ->
                  let uu____1012 =
                    let uu___55_1013 = x  in
                    let uu____1014 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___55_1013.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___55_1013.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____1014
                    }  in
                  (uu____1012, imp)))

and (inst_args :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,FStar_Syntax_Syntax.aqual)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____1057  ->
              match uu____1057 with
              | (a,imp) -> let uu____1068 = inst s a  in (uu____1068, imp)))

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
          let uu____1089 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____1089 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____1100 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____1100 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___56_1103 = ct  in
            let uu____1104 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____1107 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____1116 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___52_1126  ->
                      match uu___52_1126 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____1130 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____1130
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___56_1103.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___56_1103.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____1104;
              FStar_Syntax_Syntax.effect_args = uu____1107;
              FStar_Syntax_Syntax.flags = uu____1116
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
          let uu____1145 =
            let uu___57_1146 = rc  in
            let uu____1147 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___57_1146.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____1147;
              FStar_Syntax_Syntax.residual_flags =
                (uu___57_1146.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____1145

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____1170 ->
          let inst_fv t1 fv =
            let uu____1182 =
              FStar_Util.find_opt
                (fun uu____1196  ->
                   match uu____1196 with
                   | (x,uu____1202) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____1182 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____1207,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  