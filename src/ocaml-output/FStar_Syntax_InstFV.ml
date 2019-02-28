open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____42435 'Auu____42436 .
    'Auu____42435 FStar_Syntax_Syntax.syntax ->
      'Auu____42436 -> 'Auu____42436 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____42566 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____42590 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42591 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42604 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____42617 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____42618 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____42619 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____42620 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____42627 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____42634 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____42665 =
            let uu____42666 =
              let uu____42685 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____42685)  in
            FStar_Syntax_Syntax.Tm_abs uu____42666  in
          mk1 uu____42665
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___438_42743 = bv  in
            let uu____42744 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___438_42743.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___438_42743.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42744
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____42776 =
            let uu____42777 =
              let uu____42794 = inst s t2  in
              let uu____42797 = inst_args s args  in
              (uu____42794, uu____42797)  in
            FStar_Syntax_Syntax.Tm_app uu____42777  in
          mk1 uu____42776
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____42929  ->
                    match uu____42929 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____42967 = inst s w  in
                              FStar_Pervasives_Native.Some uu____42967
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____42973 =
            let uu____42974 =
              let uu____42997 = inst s t2  in (uu____42997, pats1)  in
            FStar_Syntax_Syntax.Tm_match uu____42974  in
          mk1 uu____42973
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____43090 =
            match uu____43090 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____43152 = inst s t2  in
                      FStar_Util.Inl uu____43152
                  | FStar_Util.Inr c ->
                      let uu____43160 = inst_comp s c  in
                      FStar_Util.Inr uu____43160
                   in
                (annot1, topt1)
             in
          let uu____43173 =
            let uu____43174 =
              let uu____43201 = inst s t11  in
              let uu____43204 = inst_asc asc  in
              (uu____43201, uu____43204, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____43174  in
          mk1 uu____43173
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____43269 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___480_43284 = lb  in
                      let uu____43285 = inst s lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let uu____43288 = inst s lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___480_43284.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___480_43284.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____43285;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___480_43284.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____43288;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___480_43284.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___480_43284.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____43269)  in
          let uu____43297 =
            let uu____43298 =
              let uu____43312 = inst s t2  in (lbs1, uu____43312)  in
            FStar_Syntax_Syntax.Tm_let uu____43298  in
          mk1 uu____43297
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____43342 =
            let uu____43343 =
              let uu____43350 = inst s t2  in
              let uu____43353 =
                let uu____43354 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____43354  in
              (uu____43350, uu____43353)  in
            FStar_Syntax_Syntax.Tm_meta uu____43343  in
          mk1 uu____43342
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____43424 =
            let uu____43425 =
              let uu____43432 = inst s t2  in
              let uu____43435 =
                let uu____43436 =
                  let uu____43443 = inst s t'  in (m, uu____43443)  in
                FStar_Syntax_Syntax.Meta_monadic uu____43436  in
              (uu____43432, uu____43435)  in
            FStar_Syntax_Syntax.Tm_meta uu____43425  in
          mk1 uu____43424
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____43456 =
            let uu____43457 =
              let uu____43464 = inst s t2  in (uu____43464, tag)  in
            FStar_Syntax_Syntax.Tm_meta uu____43457  in
          mk1 uu____43456

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____43499  ->
              match uu____43499 with
              | (x,imp) ->
                  let uu____43518 =
                    let uu___504_43519 = x  in
                    let uu____43520 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___504_43519.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___504_43519.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____43520
                    }  in
                  (uu____43518, imp)))

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
           (fun uu____43575  ->
              match uu____43575 with
              | (a,imp) -> let uu____43594 = inst s a  in (uu____43594, imp)))

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
          let uu____43617 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____43617 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____43628 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____43628 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___523_43631 = ct  in
            let uu____43632 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____43635 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____43646 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___391_43656  ->
                      match uu___391_43656 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____43660 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____43660
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___523_43631.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___523_43631.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____43632;
              FStar_Syntax_Syntax.effect_args = uu____43635;
              FStar_Syntax_Syntax.flags = uu____43646
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
          let uu____43675 =
            let uu___535_43676 = rc  in
            let uu____43677 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___535_43676.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____43677;
              FStar_Syntax_Syntax.residual_flags =
                (uu___535_43676.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____43675

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____43701 ->
          let inst_fv t1 fv =
            let uu____43713 =
              FStar_Util.find_opt
                (fun uu____43727  ->
                   match uu____43727 with
                   | (x,uu____43734) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____43713 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____43739,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  