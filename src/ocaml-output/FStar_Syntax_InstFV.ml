open Prims
type inst_t = (FStar_Ident.lident * FStar_Syntax_Syntax.universes) Prims.list
let mk t s =
  let uu____26 = FStar_ST.read t.FStar_Syntax_Syntax.tk  in
  FStar_Syntax_Syntax.mk s uu____26 t.FStar_Syntax_Syntax.pos 
let rec inst :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun s  ->
    fun t  ->
      let t1 = FStar_Syntax_Subst.compress t  in
      let mk1 = mk t1  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu____123 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name _
        |FStar_Syntax_Syntax.Tm_uvar _
         |FStar_Syntax_Syntax.Tm_uvar _
          |FStar_Syntax_Syntax.Tm_type _
           |FStar_Syntax_Syntax.Tm_bvar _
            |FStar_Syntax_Syntax.Tm_constant _
             |FStar_Syntax_Syntax.Tm_unknown |FStar_Syntax_Syntax.Tm_uinst _
          -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____179 =
            let uu____180 =
              let uu____195 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____195)  in
            FStar_Syntax_Syntax.Tm_abs uu____180  in
          mk1 uu____179
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___160_233 = bv  in
            let uu____234 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___160_233.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___160_233.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____234
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____254 =
            let uu____255 =
              let uu____265 = inst s t2  in
              let uu____266 = inst_args s args  in (uu____265, uu____266)  in
            FStar_Syntax_Syntax.Tm_app uu____255  in
          mk1 uu____254
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____343  ->
                    match uu____343 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | None  -> None
                          | Some w ->
                              let uu____369 = inst s w  in Some uu____369
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____374 =
            let uu____375 = let uu____391 = inst s t2  in (uu____391, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____375  in
          mk1 uu____374
      | FStar_Syntax_Syntax.Tm_ascribed (t11,FStar_Util.Inl t2,f) ->
          let uu____420 =
            let uu____421 =
              let uu____434 = inst s t11  in
              let uu____435 =
                let uu____440 = inst s t2  in FStar_Util.Inl uu____440  in
              (uu____434, uu____435, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____421  in
          mk1 uu____420
      | FStar_Syntax_Syntax.Tm_ascribed (t11,FStar_Util.Inr c,f) ->
          let uu____469 =
            let uu____470 =
              let uu____483 = inst s t11  in
              let uu____484 =
                let uu____491 = inst_comp s c  in FStar_Util.Inr uu____491
                 in
              (uu____483, uu____484, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____470  in
          mk1 uu____469
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____521 =
              FStar_All.pipe_right (Prims.snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___161_527 = lb  in
                      let uu____528 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____531 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___161_527.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___161_527.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____528;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___161_527.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____531
                      }))
               in
            ((Prims.fst lbs), uu____521)  in
          let uu____536 =
            let uu____537 = let uu____545 = inst s t2  in (lbs1, uu____545)
               in
            FStar_Syntax_Syntax.Tm_let uu____537  in
          mk1 uu____536
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____561 =
            let uu____562 =
              let uu____567 = inst s t2  in
              let uu____568 =
                let uu____569 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____569  in
              (uu____567, uu____568)  in
            FStar_Syntax_Syntax.Tm_meta uu____562  in
          mk1 uu____561
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____609 =
            let uu____610 =
              let uu____615 = inst s t2  in
              let uu____616 =
                let uu____617 = let uu____622 = inst s t'  in (m, uu____622)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____617  in
              (uu____615, uu____616)  in
            FStar_Syntax_Syntax.Tm_meta uu____610  in
          mk1 uu____609
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____629 =
            let uu____630 = let uu____635 = inst s t2  in (uu____635, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____630  in
          mk1 uu____629

and inst_binders :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.binders ->
      (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun s  ->
    fun bs  ->
      FStar_All.pipe_right bs
        (FStar_List.map
           (fun uu____649  ->
              match uu____649 with
              | (x,imp) ->
                  let uu____656 =
                    let uu___162_657 = x  in
                    let uu____658 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___162_657.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___162_657.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____658
                    }  in
                  (uu____656, imp)))

and inst_args :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    ((FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.aqual) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual) Prims.list
  =
  fun s  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____684  ->
              match uu____684 with
              | (a,imp) -> let uu____691 = inst s a  in (uu____691, imp)))

and inst_comp :
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
          let uu____710 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____710 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____719 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____719 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___163_722 = ct  in
            let uu____723 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____729 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___159_733  ->
                      match uu___159_733 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____737 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____737
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_typ_name =
                (uu___163_722.FStar_Syntax_Syntax.comp_typ_name);
              FStar_Syntax_Syntax.comp_univs =
                (uu___163_722.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_args = uu____723;
              FStar_Syntax_Syntax.flags = uu____729
            }  in
          FStar_Syntax_Syntax.mk_Comp ct1

and inst_lcomp_opt :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident *
                                 FStar_Syntax_Syntax.cflags Prims.list))
      FStar_Util.either Prims.option ->
      (FStar_Syntax_Syntax.lcomp,(FStar_Ident.lident *
                                   FStar_Syntax_Syntax.cflags Prims.list))
        FStar_Util.either Prims.option
  =
  fun s  ->
    fun l  ->
      match l with
      | None |Some (FStar_Util.Inr _) -> l
      | Some (FStar_Util.Inl lc) ->
          let uu____782 =
            let uu____788 =
              let uu___164_789 = lc  in
              let uu____790 =
                inst_args s lc.FStar_Syntax_Syntax.lcomp_indices  in
              let uu____796 = inst s lc.FStar_Syntax_Syntax.lcomp_res_typ  in
              {
                FStar_Syntax_Syntax.lcomp_name =
                  (uu___164_789.FStar_Syntax_Syntax.lcomp_name);
                FStar_Syntax_Syntax.lcomp_univs =
                  (uu___164_789.FStar_Syntax_Syntax.lcomp_univs);
                FStar_Syntax_Syntax.lcomp_indices = uu____790;
                FStar_Syntax_Syntax.lcomp_res_typ = uu____796;
                FStar_Syntax_Syntax.lcomp_cflags =
                  (uu___164_789.FStar_Syntax_Syntax.lcomp_cflags);
                FStar_Syntax_Syntax.lcomp_as_comp =
                  (fun uu____799  ->
                     let uu____800 = lc.FStar_Syntax_Syntax.lcomp_as_comp ()
                        in
                     inst_comp s uu____800)
              }  in
            FStar_Util.Inl uu____788  in
          Some uu____782

let instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____819 ->
          let inst_fv t1 fv =
            let uu____827 =
              FStar_Util.find_opt
                (fun uu____833  ->
                   match uu____833 with
                   | (x,uu____837) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____827 with
            | None  -> t1
            | Some (uu____844,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  