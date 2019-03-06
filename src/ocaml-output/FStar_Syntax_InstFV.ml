open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk :
  'Auu____42436 'Auu____42437 .
    'Auu____42436 FStar_Syntax_Syntax.syntax ->
      'Auu____42437 -> 'Auu____42437 FStar_Syntax_Syntax.syntax
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
      | FStar_Syntax_Syntax.Tm_delayed uu____42567 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____42591 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42592 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____42605 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____42618 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____42619 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____42620 -> t1
      | FStar_Syntax_Syntax.Tm_quoted uu____42621 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____42628 -> t1
      | FStar_Syntax_Syntax.Tm_lazy uu____42635 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____42666 =
            let uu____42667 =
              let uu____42686 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____42686)  in
            FStar_Syntax_Syntax.Tm_abs uu____42667  in
          mk1 uu____42666
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___438_42744 = bv  in
            let uu____42745 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___438_42744.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___438_42744.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____42745
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____42777 =
            let uu____42778 =
              let uu____42795 = inst s t2  in
              let uu____42798 = inst_args s args  in
              (uu____42795, uu____42798)  in
            FStar_Syntax_Syntax.Tm_app uu____42778  in
          mk1 uu____42777
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____42930  ->
                    match uu____42930 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | FStar_Pervasives_Native.None  ->
                              FStar_Pervasives_Native.None
                          | FStar_Pervasives_Native.Some w ->
                              let uu____42968 = inst s w  in
                              FStar_Pervasives_Native.Some uu____42968
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____42974 =
            let uu____42975 =
              let uu____42998 = inst s t2  in (uu____42998, pats1)  in
            FStar_Syntax_Syntax.Tm_match uu____42975  in
          mk1 uu____42974
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____43091 =
            match uu____43091 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____43153 = inst s t2  in
                      FStar_Util.Inl uu____43153
                  | FStar_Util.Inr c ->
                      let uu____43161 = inst_comp s c  in
                      FStar_Util.Inr uu____43161
                   in
                (annot1, topt1)
             in
          let uu____43174 =
            let uu____43175 =
              let uu____43202 = inst s t11  in
              let uu____43205 = inst_asc asc  in
              (uu____43202, uu____43205, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____43175  in
          mk1 uu____43174
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____43270 =
              FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___480_43285 = lb  in
                      let uu____43286 = inst s lb.FStar_Syntax_Syntax.lbtyp
                         in
                      let uu____43289 = inst s lb.FStar_Syntax_Syntax.lbdef
                         in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___480_43285.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___480_43285.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____43286;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___480_43285.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____43289;
                        FStar_Syntax_Syntax.lbattrs =
                          (uu___480_43285.FStar_Syntax_Syntax.lbattrs);
                        FStar_Syntax_Syntax.lbpos =
                          (uu___480_43285.FStar_Syntax_Syntax.lbpos)
                      }))
               in
            ((FStar_Pervasives_Native.fst lbs), uu____43270)  in
          let uu____43298 =
            let uu____43299 =
              let uu____43313 = inst s t2  in (lbs1, uu____43313)  in
            FStar_Syntax_Syntax.Tm_let uu____43299  in
          mk1 uu____43298
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____43343 =
            let uu____43344 =
              let uu____43351 = inst s t2  in
              let uu____43354 =
                let uu____43355 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____43355  in
              (uu____43351, uu____43354)  in
            FStar_Syntax_Syntax.Tm_meta uu____43344  in
          mk1 uu____43343
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____43425 =
            let uu____43426 =
              let uu____43433 = inst s t2  in
              let uu____43436 =
                let uu____43437 =
                  let uu____43444 = inst s t'  in (m, uu____43444)  in
                FStar_Syntax_Syntax.Meta_monadic uu____43437  in
              (uu____43433, uu____43436)  in
            FStar_Syntax_Syntax.Tm_meta uu____43426  in
          mk1 uu____43425
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____43457 =
            let uu____43458 =
              let uu____43465 = inst s t2  in (uu____43465, tag)  in
            FStar_Syntax_Syntax.Tm_meta uu____43458  in
          mk1 uu____43457

and (inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.binders -> FStar_Syntax_Syntax.binders)
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____43500  ->
              match uu____43500 with
              | (x,imp) ->
                  let uu____43519 =
                    let uu___504_43520 = x  in
                    let uu____43521 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___504_43520.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___504_43520.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____43521
                    }  in
                  (uu____43519, imp)))

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
           (fun uu____43576  ->
              match uu____43576 with
              | (a,imp) -> let uu____43595 = inst s a  in (uu____43595, imp)))

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
          let uu____43618 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____43618 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____43629 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____43629 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___523_43632 = ct  in
            let uu____43633 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____43636 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____43647 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___391_43657  ->
                      match uu___391_43657 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____43661 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____43661
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___523_43632.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___523_43632.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____43633;
              FStar_Syntax_Syntax.effect_args = uu____43636;
              FStar_Syntax_Syntax.flags = uu____43647
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
          let uu____43676 =
            let uu___535_43677 = rc  in
            let uu____43678 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___535_43677.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____43678;
              FStar_Syntax_Syntax.residual_flags =
                (uu___535_43677.FStar_Syntax_Syntax.residual_flags)
            }  in
          FStar_Pervasives_Native.Some uu____43676

let (instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____43702 ->
          let inst_fv t1 fv =
            let uu____43714 =
              FStar_Util.find_opt
                (fun uu____43728  ->
                   match uu____43728 with
                   | (x,uu____43735) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____43714 with
            | FStar_Pervasives_Native.None  -> t1
            | FStar_Pervasives_Native.Some (uu____43740,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  