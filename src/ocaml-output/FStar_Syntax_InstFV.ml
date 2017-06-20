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
      | FStar_Syntax_Syntax.Tm_delayed uu____113 -> failwith "Impossible"
      | FStar_Syntax_Syntax.Tm_name uu____128 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____129 -> t1
      | FStar_Syntax_Syntax.Tm_uvar uu____138 -> t1
      | FStar_Syntax_Syntax.Tm_type uu____147 -> t1
      | FStar_Syntax_Syntax.Tm_bvar uu____148 -> t1
      | FStar_Syntax_Syntax.Tm_constant uu____149 -> t1
      | FStar_Syntax_Syntax.Tm_unknown  -> t1
      | FStar_Syntax_Syntax.Tm_uinst uu____150 -> t1
      | FStar_Syntax_Syntax.Tm_fvar fv -> s t1 fv
      | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
          let bs1 = inst_binders s bs  in
          let body1 = inst s body  in
          let uu____173 =
            let uu____174 =
              let uu____184 = inst_lcomp_opt s lopt  in
              (bs1, body1, uu____184)  in
            FStar_Syntax_Syntax.Tm_abs uu____174  in
          mk1 uu____173
      | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
          let bs1 = inst_binders s bs  in
          let c1 = inst_comp s c  in
          mk1 (FStar_Syntax_Syntax.Tm_arrow (bs1, c1))
      | FStar_Syntax_Syntax.Tm_refine (bv,t2) ->
          let bv1 =
            let uu___157_212 = bv  in
            let uu____213 = inst s bv.FStar_Syntax_Syntax.sort  in
            {
              FStar_Syntax_Syntax.ppname =
                (uu___157_212.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index =
                (uu___157_212.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = uu____213
            }  in
          let t3 = inst s t2  in
          mk1 (FStar_Syntax_Syntax.Tm_refine (bv1, t3))
      | FStar_Syntax_Syntax.Tm_app (t2,args) ->
          let uu____233 =
            let uu____234 =
              let uu____244 = inst s t2  in
              let uu____245 = inst_args s args  in (uu____244, uu____245)  in
            FStar_Syntax_Syntax.Tm_app uu____234  in
          mk1 uu____233
      | FStar_Syntax_Syntax.Tm_match (t2,pats) ->
          let pats1 =
            FStar_All.pipe_right pats
              (FStar_List.map
                 (fun uu____322  ->
                    match uu____322 with
                    | (p,wopt,t3) ->
                        let wopt1 =
                          match wopt with
                          | None  -> None
                          | Some w ->
                              let uu____348 = inst s w  in Some uu____348
                           in
                        let t4 = inst s t3  in (p, wopt1, t4)))
             in
          let uu____353 =
            let uu____354 = let uu____370 = inst s t2  in (uu____370, pats1)
               in
            FStar_Syntax_Syntax.Tm_match uu____354  in
          mk1 uu____353
      | FStar_Syntax_Syntax.Tm_ascribed (t11,asc,f) ->
          let inst_asc uu____426 =
            match uu____426 with
            | (annot,topt) ->
                let topt1 = FStar_Util.map_opt topt (inst s)  in
                let annot1 =
                  match annot with
                  | FStar_Util.Inl t2 ->
                      let uu____467 = inst s t2  in FStar_Util.Inl uu____467
                  | FStar_Util.Inr c ->
                      let uu____475 = inst_comp s c  in
                      FStar_Util.Inr uu____475
                   in
                (annot1, topt1)
             in
          let uu____485 =
            let uu____486 =
              let uu____504 = inst s t11  in
              let uu____505 = inst_asc asc  in (uu____504, uu____505, f)  in
            FStar_Syntax_Syntax.Tm_ascribed uu____486  in
          mk1 uu____485
      | FStar_Syntax_Syntax.Tm_let (lbs,t2) ->
          let lbs1 =
            let uu____537 =
              FStar_All.pipe_right (snd lbs)
                (FStar_List.map
                   (fun lb  ->
                      let uu___158_543 = lb  in
                      let uu____544 = inst s lb.FStar_Syntax_Syntax.lbtyp  in
                      let uu____547 = inst s lb.FStar_Syntax_Syntax.lbdef  in
                      {
                        FStar_Syntax_Syntax.lbname =
                          (uu___158_543.FStar_Syntax_Syntax.lbname);
                        FStar_Syntax_Syntax.lbunivs =
                          (uu___158_543.FStar_Syntax_Syntax.lbunivs);
                        FStar_Syntax_Syntax.lbtyp = uu____544;
                        FStar_Syntax_Syntax.lbeff =
                          (uu___158_543.FStar_Syntax_Syntax.lbeff);
                        FStar_Syntax_Syntax.lbdef = uu____547
                      }))
               in
            ((fst lbs), uu____537)  in
          let uu____552 =
            let uu____553 = let uu____561 = inst s t2  in (lbs1, uu____561)
               in
            FStar_Syntax_Syntax.Tm_let uu____553  in
          mk1 uu____552
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_pattern args) ->
          let uu____577 =
            let uu____578 =
              let uu____583 = inst s t2  in
              let uu____584 =
                let uu____585 =
                  FStar_All.pipe_right args (FStar_List.map (inst_args s))
                   in
                FStar_Syntax_Syntax.Meta_pattern uu____585  in
              (uu____583, uu____584)  in
            FStar_Syntax_Syntax.Tm_meta uu____578  in
          mk1 uu____577
      | FStar_Syntax_Syntax.Tm_meta
          (t2,FStar_Syntax_Syntax.Meta_monadic (m,t')) ->
          let uu____625 =
            let uu____626 =
              let uu____631 = inst s t2  in
              let uu____632 =
                let uu____633 = let uu____638 = inst s t'  in (m, uu____638)
                   in
                FStar_Syntax_Syntax.Meta_monadic uu____633  in
              (uu____631, uu____632)  in
            FStar_Syntax_Syntax.Tm_meta uu____626  in
          mk1 uu____625
      | FStar_Syntax_Syntax.Tm_meta (t2,tag) ->
          let uu____645 =
            let uu____646 = let uu____651 = inst s t2  in (uu____651, tag)
               in
            FStar_Syntax_Syntax.Tm_meta uu____646  in
          mk1 uu____645

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
           (fun uu____665  ->
              match uu____665 with
              | (x,imp) ->
                  let uu____672 =
                    let uu___159_673 = x  in
                    let uu____674 = inst s x.FStar_Syntax_Syntax.sort  in
                    {
                      FStar_Syntax_Syntax.ppname =
                        (uu___159_673.FStar_Syntax_Syntax.ppname);
                      FStar_Syntax_Syntax.index =
                        (uu___159_673.FStar_Syntax_Syntax.index);
                      FStar_Syntax_Syntax.sort = uu____674
                    }  in
                  (uu____672, imp)))

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
           (fun uu____700  ->
              match uu____700 with
              | (a,imp) -> let uu____707 = inst s a  in (uu____707, imp)))

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
          let uu____726 = inst s t  in
          FStar_Syntax_Syntax.mk_Total' uu____726 uopt
      | FStar_Syntax_Syntax.GTotal (t,uopt) ->
          let uu____735 = inst s t  in
          FStar_Syntax_Syntax.mk_GTotal' uu____735 uopt
      | FStar_Syntax_Syntax.Comp ct ->
          let ct1 =
            let uu___160_738 = ct  in
            let uu____739 = inst s ct.FStar_Syntax_Syntax.result_typ  in
            let uu____742 = inst_args s ct.FStar_Syntax_Syntax.effect_args
               in
            let uu____748 =
              FStar_All.pipe_right ct.FStar_Syntax_Syntax.flags
                (FStar_List.map
                   (fun uu___156_752  ->
                      match uu___156_752 with
                      | FStar_Syntax_Syntax.DECREASES t ->
                          let uu____756 = inst s t  in
                          FStar_Syntax_Syntax.DECREASES uu____756
                      | f -> f))
               in
            {
              FStar_Syntax_Syntax.comp_univs =
                (uu___160_738.FStar_Syntax_Syntax.comp_univs);
              FStar_Syntax_Syntax.effect_name =
                (uu___160_738.FStar_Syntax_Syntax.effect_name);
              FStar_Syntax_Syntax.result_typ = uu____739;
              FStar_Syntax_Syntax.effect_args = uu____742;
              FStar_Syntax_Syntax.flags = uu____748
            }  in
          FStar_Syntax_Syntax.mk_Comp ct1

and inst_lcomp_opt :
  (FStar_Syntax_Syntax.term ->
     FStar_Syntax_Syntax.fv -> FStar_Syntax_Syntax.term)
    ->
    FStar_Syntax_Syntax.residual_comp option ->
      FStar_Syntax_Syntax.residual_comp option
  =
  fun s  ->
    fun l  ->
      match l with
      | None  -> None
      | Some rc ->
          let uu____769 =
            let uu___161_770 = rc  in
            let uu____771 =
              FStar_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ (inst s)
               in
            {
              FStar_Syntax_Syntax.residual_effect =
                (uu___161_770.FStar_Syntax_Syntax.residual_effect);
              FStar_Syntax_Syntax.residual_typ = uu____771;
              FStar_Syntax_Syntax.residual_flags =
                (uu___161_770.FStar_Syntax_Syntax.residual_flags)
            }  in
          Some uu____769

let instantiate :
  inst_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun i  ->
    fun t  ->
      match i with
      | [] -> t
      | uu____785 ->
          let inst_fv t1 fv =
            let uu____793 =
              FStar_Util.find_opt
                (fun uu____799  ->
                   match uu____799 with
                   | (x,uu____803) ->
                       FStar_Ident.lid_equals x
                         (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                i
               in
            match uu____793 with
            | None  -> t1
            | Some (uu____810,us) ->
                mk t1 (FStar_Syntax_Syntax.Tm_uinst (t1, us))
             in
          inst inst_fv t
  