open Prims
type 'a endo = 'a -> 'a
let id : 'a . 'a -> 'a = fun x -> x
type vfs_t =
  {
  f_term: FStar_Syntax_Syntax.term endo ;
  f_binder: FStar_Syntax_Syntax.binder endo ;
  f_binding_bv: FStar_Syntax_Syntax.bv endo ;
  f_br: FStar_Syntax_Syntax.branch endo ;
  f_comp: FStar_Syntax_Syntax.comp endo ;
  f_residual_comp: FStar_Syntax_Syntax.residual_comp endo ;
  f_univ: FStar_Syntax_Syntax.universe endo }
let (__proj__Mkvfs_t__item__f_term : vfs_t -> FStar_Syntax_Syntax.term endo)
  =
  fun projectee ->
    match projectee with
    | { f_term; f_binder; f_binding_bv; f_br; f_comp; f_residual_comp;
        f_univ;_} -> f_term
let (__proj__Mkvfs_t__item__f_binder :
  vfs_t -> FStar_Syntax_Syntax.binder endo) =
  fun projectee ->
    match projectee with
    | { f_term; f_binder; f_binding_bv; f_br; f_comp; f_residual_comp;
        f_univ;_} -> f_binder
let (__proj__Mkvfs_t__item__f_binding_bv :
  vfs_t -> FStar_Syntax_Syntax.bv endo) =
  fun projectee ->
    match projectee with
    | { f_term; f_binder; f_binding_bv; f_br; f_comp; f_residual_comp;
        f_univ;_} -> f_binding_bv
let (__proj__Mkvfs_t__item__f_br : vfs_t -> FStar_Syntax_Syntax.branch endo)
  =
  fun projectee ->
    match projectee with
    | { f_term; f_binder; f_binding_bv; f_br; f_comp; f_residual_comp;
        f_univ;_} -> f_br
let (__proj__Mkvfs_t__item__f_comp : vfs_t -> FStar_Syntax_Syntax.comp endo)
  =
  fun projectee ->
    match projectee with
    | { f_term; f_binder; f_binding_bv; f_br; f_comp; f_residual_comp;
        f_univ;_} -> f_comp
let (__proj__Mkvfs_t__item__f_residual_comp :
  vfs_t -> FStar_Syntax_Syntax.residual_comp endo) =
  fun projectee ->
    match projectee with
    | { f_term; f_binder; f_binding_bv; f_br; f_comp; f_residual_comp;
        f_univ;_} -> f_residual_comp
let (__proj__Mkvfs_t__item__f_univ :
  vfs_t -> FStar_Syntax_Syntax.universe endo) =
  fun projectee ->
    match projectee with
    | { f_term; f_binder; f_binding_bv; f_br; f_comp; f_residual_comp;
        f_univ;_} -> f_univ
let on_tuple2 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 .
    ('uuuuu -> 'uuuuu1) ->
      ('uuuuu2 -> 'uuuuu3) -> ('uuuuu * 'uuuuu2) -> ('uuuuu1 * 'uuuuu3)
  =
  fun f ->
    fun g ->
      fun uu___ ->
        match uu___ with
        | (x, y) -> let uu___1 = f x in let uu___2 = g y in (uu___1, uu___2)
let on_tuple3 :
  'uuuuu 'uuuuu1 'uuuuu2 'uuuuu3 'uuuuu4 'uuuuu5 .
    ('uuuuu -> 'uuuuu1) ->
      ('uuuuu2 -> 'uuuuu3) ->
        ('uuuuu4 -> 'uuuuu5) ->
          ('uuuuu * 'uuuuu2 * 'uuuuu4) -> ('uuuuu1 * 'uuuuu3 * 'uuuuu5)
  =
  fun f ->
    fun g ->
      fun h ->
        fun uu___ ->
          match uu___ with
          | (x, y, z) ->
              let uu___1 = f x in
              let uu___2 = g y in
              let uu___3 = h z in (uu___1, uu___2, uu___3)
let (novfs : vfs_t) =
  {
    f_term = id;
    f_binder = id;
    f_binding_bv = id;
    f_br = id;
    f_comp = id;
    f_residual_comp = id;
    f_univ = id
  }
let (f_term : vfs_t -> FStar_Syntax_Syntax.term endo) = fun vfs -> vfs.f_term
let (f_univ : vfs_t -> FStar_Syntax_Syntax.universe endo) =
  fun vfs -> vfs.f_univ
let (on_sub_arg :
  vfs_t -> FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.arg) =
  fun vfs ->
    fun a ->
      let uu___ = a in
      match uu___ with
      | (t, q) ->
          let t1 = f_term vfs t in
          let q1 =
            FStar_Compiler_Util.map_opt q
              (fun uu___1 ->
                 match uu___1 with
                 | { FStar_Syntax_Syntax.aqual_implicit = i;
                     FStar_Syntax_Syntax.aqual_attributes = attrs;_} ->
                     let uu___2 = FStar_Compiler_List.map (f_term vfs) attrs in
                     {
                       FStar_Syntax_Syntax.aqual_implicit = i;
                       FStar_Syntax_Syntax.aqual_attributes = uu___2
                     }) in
          (t1, q1)
let (on_sub_tscheme :
  vfs_t -> FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) =
  fun vfs ->
    fun ts ->
      let uu___ = ts in
      match uu___ with | (us, t) -> let t1 = f_term vfs t in (us, t1)
let (f_arg : vfs_t -> FStar_Syntax_Syntax.arg -> FStar_Syntax_Syntax.arg) =
  fun vfs -> on_sub_arg vfs
let (f_binding_bv : vfs_t -> FStar_Syntax_Syntax.bv endo) =
  fun vfs -> vfs.f_binding_bv
let (f_binder : vfs_t -> FStar_Syntax_Syntax.binder endo) =
  fun vfs -> vfs.f_binder
let (f_br : vfs_t -> FStar_Syntax_Syntax.branch endo) = fun vfs -> vfs.f_br
let (f_comp : vfs_t -> FStar_Syntax_Syntax.comp endo) = fun vfs -> vfs.f_comp
let (f_residual_comp : vfs_t -> FStar_Syntax_Syntax.residual_comp endo) =
  fun vfs -> vfs.f_residual_comp
let (f_tscheme :
  vfs_t -> FStar_Syntax_Syntax.tscheme -> FStar_Syntax_Syntax.tscheme) =
  fun vfs -> on_sub_tscheme vfs
let (on_sub_meta :
  vfs_t -> FStar_Syntax_Syntax.metadata -> FStar_Syntax_Syntax.metadata) =
  fun vfs ->
    fun md ->
      match md with
      | FStar_Syntax_Syntax.Meta_pattern (pats, args) ->
          let pats1 = FStar_Compiler_List.map (f_term vfs) pats in
          let args1 =
            FStar_Compiler_List.map (FStar_Compiler_List.map (f_arg vfs))
              args in
          FStar_Syntax_Syntax.Meta_pattern (pats1, args1)
      | FStar_Syntax_Syntax.Meta_monadic (m, typ) ->
          let uu___ = let uu___1 = f_term vfs typ in (m, uu___1) in
          FStar_Syntax_Syntax.Meta_monadic uu___
      | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, typ) ->
          let uu___ = let uu___1 = f_term vfs typ in (m1, m2, uu___1) in
          FStar_Syntax_Syntax.Meta_monadic_lift uu___
      | FStar_Syntax_Syntax.Meta_named lid ->
          FStar_Syntax_Syntax.Meta_named lid
      | FStar_Syntax_Syntax.Meta_labeled (s, r, b) ->
          FStar_Syntax_Syntax.Meta_labeled (s, r, b)
      | FStar_Syntax_Syntax.Meta_desugared i ->
          FStar_Syntax_Syntax.Meta_desugared i
let (on_sub_letbinding :
  vfs_t -> FStar_Syntax_Syntax.letbinding -> FStar_Syntax_Syntax.letbinding)
  =
  fun vfs ->
    fun lb ->
      let uu___ =
        match lb.FStar_Syntax_Syntax.lbname with
        | FStar_Pervasives.Inl bv ->
            let uu___1 = f_binding_bv vfs bv in FStar_Pervasives.Inl uu___1
        | FStar_Pervasives.Inr fv -> FStar_Pervasives.Inr fv in
      let uu___1 = f_term vfs lb.FStar_Syntax_Syntax.lbtyp in
      let uu___2 = f_term vfs lb.FStar_Syntax_Syntax.lbdef in
      let uu___3 =
        FStar_Compiler_List.map (f_term vfs) lb.FStar_Syntax_Syntax.lbattrs in
      {
        FStar_Syntax_Syntax.lbname = uu___;
        FStar_Syntax_Syntax.lbunivs = (lb.FStar_Syntax_Syntax.lbunivs);
        FStar_Syntax_Syntax.lbtyp = uu___1;
        FStar_Syntax_Syntax.lbeff = (lb.FStar_Syntax_Syntax.lbeff);
        FStar_Syntax_Syntax.lbdef = uu___2;
        FStar_Syntax_Syntax.lbattrs = uu___3;
        FStar_Syntax_Syntax.lbpos = (lb.FStar_Syntax_Syntax.lbpos)
      }
let (on_sub_ascription :
  vfs_t -> FStar_Syntax_Syntax.ascription -> FStar_Syntax_Syntax.ascription)
  =
  fun vfs ->
    fun a ->
      let uu___ = a in
      match uu___ with
      | (tc, tacopt, b) ->
          let tc1 =
            match tc with
            | FStar_Pervasives.Inl t ->
                let uu___1 = f_term vfs t in FStar_Pervasives.Inl uu___1
            | FStar_Pervasives.Inr c ->
                let uu___1 = f_comp vfs c in FStar_Pervasives.Inr uu___1 in
          let tacopt1 = FStar_Compiler_Util.map_opt tacopt (f_term vfs) in
          (tc1, tacopt1, b)
let rec (compress : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun tm ->
    let tm1 = FStar_Syntax_Subst.compress tm in
    match tm1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_lazy li ->
        let tm' =
          let uu___ =
            let uu___1 =
              FStar_Compiler_Effect.op_Bang FStar_Syntax_Syntax.lazy_chooser in
            FStar_Compiler_Util.must uu___1 in
          uu___ li.FStar_Syntax_Syntax.lkind li in
        compress tm'
    | uu___ -> tm1
let (on_sub_term :
  vfs_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun vfs ->
    fun tm ->
      let mk t = FStar_Syntax_Syntax.mk t tm.FStar_Syntax_Syntax.pos in
      let tm1 = compress tm in
      match tm1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_lazy uu___ -> failwith "impos"
      | FStar_Syntax_Syntax.Tm_delayed uu___ -> failwith "impos"
      | FStar_Syntax_Syntax.Tm_fvar uu___ -> tm1
      | FStar_Syntax_Syntax.Tm_constant uu___ -> tm1
      | FStar_Syntax_Syntax.Tm_unknown -> tm1
      | FStar_Syntax_Syntax.Tm_bvar uu___ -> tm1
      | FStar_Syntax_Syntax.Tm_name uu___ -> tm1
      | FStar_Syntax_Syntax.Tm_uvar uu___ -> tm1
      | FStar_Syntax_Syntax.Tm_uinst (f, us) ->
          let f1 = f_term vfs f in
          let us1 = FStar_Compiler_List.map (f_univ vfs) us in
          mk (FStar_Syntax_Syntax.Tm_uinst (f1, us1))
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu___ =
            let uu___1 = f_univ vfs u in FStar_Syntax_Syntax.Tm_type uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Tm_app
          { FStar_Syntax_Syntax.hd = hd; FStar_Syntax_Syntax.args = args;_}
          ->
          let hd1 = f_term vfs hd in
          let args1 = FStar_Compiler_List.map (f_arg vfs) args in
          mk
            (FStar_Syntax_Syntax.Tm_app
               {
                 FStar_Syntax_Syntax.hd = hd1;
                 FStar_Syntax_Syntax.args = args1
               })
      | FStar_Syntax_Syntax.Tm_abs
          { FStar_Syntax_Syntax.bs = bs; FStar_Syntax_Syntax.body = t;
            FStar_Syntax_Syntax.rc_opt = rc_opt;_}
          ->
          let bs1 = FStar_Compiler_List.map (f_binder vfs) bs in
          let t1 = f_term vfs t in
          let rc_opt1 =
            FStar_Compiler_Util.map_opt rc_opt (f_residual_comp vfs) in
          mk
            (FStar_Syntax_Syntax.Tm_abs
               {
                 FStar_Syntax_Syntax.bs = bs1;
                 FStar_Syntax_Syntax.body = t1;
                 FStar_Syntax_Syntax.rc_opt = rc_opt1
               })
      | FStar_Syntax_Syntax.Tm_arrow
          { FStar_Syntax_Syntax.bs1 = bs; FStar_Syntax_Syntax.comp = c;_} ->
          let bs1 = FStar_Compiler_List.map (f_binder vfs) bs in
          let c1 = f_comp vfs c in
          mk
            (FStar_Syntax_Syntax.Tm_arrow
               { FStar_Syntax_Syntax.bs1 = bs1; FStar_Syntax_Syntax.comp = c1
               })
      | FStar_Syntax_Syntax.Tm_refine
          { FStar_Syntax_Syntax.b = bv; FStar_Syntax_Syntax.phi = phi;_} ->
          let bv1 = f_binding_bv vfs bv in
          let phi1 = f_term vfs phi in
          mk
            (FStar_Syntax_Syntax.Tm_refine
               { FStar_Syntax_Syntax.b = bv1; FStar_Syntax_Syntax.phi = phi1
               })
      | FStar_Syntax_Syntax.Tm_match
          { FStar_Syntax_Syntax.scrutinee = sc;
            FStar_Syntax_Syntax.ret_opt = asc_opt;
            FStar_Syntax_Syntax.brs = brs;
            FStar_Syntax_Syntax.rc_opt1 = rc_opt;_}
          ->
          let sc1 = f_term vfs sc in
          let asc_opt1 =
            FStar_Compiler_Util.map_opt asc_opt
              (fun uu___ ->
                 match uu___ with
                 | (b, asc) ->
                     let uu___1 = f_binder vfs b in
                     let uu___2 = on_sub_ascription vfs asc in
                     (uu___1, uu___2)) in
          let brs1 = FStar_Compiler_List.map (f_br vfs) brs in
          let rc_opt1 =
            FStar_Compiler_Util.map_opt rc_opt (f_residual_comp vfs) in
          mk
            (FStar_Syntax_Syntax.Tm_match
               {
                 FStar_Syntax_Syntax.scrutinee = sc1;
                 FStar_Syntax_Syntax.ret_opt = asc_opt1;
                 FStar_Syntax_Syntax.brs = brs1;
                 FStar_Syntax_Syntax.rc_opt1 = rc_opt1
               })
      | FStar_Syntax_Syntax.Tm_ascribed
          { FStar_Syntax_Syntax.tm = e; FStar_Syntax_Syntax.asc = a;
            FStar_Syntax_Syntax.eff_opt = lopt;_}
          ->
          let e1 = f_term vfs e in
          let a1 = on_sub_ascription vfs a in
          mk
            (FStar_Syntax_Syntax.Tm_ascribed
               {
                 FStar_Syntax_Syntax.tm = e1;
                 FStar_Syntax_Syntax.asc = a1;
                 FStar_Syntax_Syntax.eff_opt = lopt
               })
      | FStar_Syntax_Syntax.Tm_let
          { FStar_Syntax_Syntax.lbs = (is_rec, lbs);
            FStar_Syntax_Syntax.body1 = t;_}
          ->
          let lbs1 = FStar_Compiler_List.map (on_sub_letbinding vfs) lbs in
          let t1 = f_term vfs t in
          mk
            (FStar_Syntax_Syntax.Tm_let
               {
                 FStar_Syntax_Syntax.lbs = (is_rec, lbs1);
                 FStar_Syntax_Syntax.body1 = t1
               })
      | FStar_Syntax_Syntax.Tm_quoted (tm2, qi) ->
          let tm3 = f_term vfs tm2 in
          let qi1 = FStar_Syntax_Syntax.on_antiquoted (f_term vfs) qi in
          mk (FStar_Syntax_Syntax.Tm_quoted (tm3, qi1))
      | FStar_Syntax_Syntax.Tm_meta
          { FStar_Syntax_Syntax.tm2 = t; FStar_Syntax_Syntax.meta = md;_} ->
          let t1 = f_term vfs t in
          let md1 = on_sub_meta vfs md in
          mk
            (FStar_Syntax_Syntax.Tm_meta
               { FStar_Syntax_Syntax.tm2 = t1; FStar_Syntax_Syntax.meta = md1
               })
let (on_sub_binding_bv :
  vfs_t -> FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv) =
  fun vfs ->
    fun x ->
      let uu___ = f_term vfs x.FStar_Syntax_Syntax.sort in
      {
        FStar_Syntax_Syntax.ppname = (x.FStar_Syntax_Syntax.ppname);
        FStar_Syntax_Syntax.index = (x.FStar_Syntax_Syntax.index);
        FStar_Syntax_Syntax.sort = uu___
      }
let (on_sub_binder :
  vfs_t -> FStar_Syntax_Syntax.binder -> FStar_Syntax_Syntax.binder) =
  fun vfs ->
    fun b ->
      let uu___ = f_binding_bv vfs b.FStar_Syntax_Syntax.binder_bv in
      let uu___1 =
        FStar_Compiler_Util.map_opt b.FStar_Syntax_Syntax.binder_qual
          (fun uu___2 ->
             match uu___2 with
             | FStar_Syntax_Syntax.Meta t ->
                 let uu___3 = f_term vfs t in FStar_Syntax_Syntax.Meta uu___3
             | q -> q) in
      let uu___2 =
        FStar_Compiler_List.map (f_term vfs)
          b.FStar_Syntax_Syntax.binder_attrs in
      {
        FStar_Syntax_Syntax.binder_bv = uu___;
        FStar_Syntax_Syntax.binder_qual = uu___1;
        FStar_Syntax_Syntax.binder_positivity =
          (b.FStar_Syntax_Syntax.binder_positivity);
        FStar_Syntax_Syntax.binder_attrs = uu___2
      }
let rec (on_sub_pat :
  vfs_t -> FStar_Syntax_Syntax.pat -> FStar_Syntax_Syntax.pat) =
  fun vfs ->
    fun p0 ->
      let mk p =
        {
          FStar_Syntax_Syntax.v = p;
          FStar_Syntax_Syntax.p = (p0.FStar_Syntax_Syntax.p)
        } in
      match p0.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu___ -> p0
      | FStar_Syntax_Syntax.Pat_cons (fv, us, subpats) ->
          let us1 =
            FStar_Compiler_Util.map_opt us
              (FStar_Compiler_List.map (f_univ vfs)) in
          let subpats1 =
            FStar_Compiler_List.map
              (fun uu___ ->
                 match uu___ with
                 | (p, b) -> let uu___1 = on_sub_pat vfs p in (uu___1, b))
              subpats in
          mk (FStar_Syntax_Syntax.Pat_cons (fv, us1, subpats1))
      | FStar_Syntax_Syntax.Pat_var bv ->
          let uu___ =
            let uu___1 = f_binding_bv vfs bv in
            FStar_Syntax_Syntax.Pat_var uu___1 in
          mk uu___
      | FStar_Syntax_Syntax.Pat_dot_term t ->
          let uu___ =
            let uu___1 = FStar_Compiler_Util.map_opt t (f_term vfs) in
            FStar_Syntax_Syntax.Pat_dot_term uu___1 in
          mk uu___
let (on_sub_br :
  vfs_t ->
    (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
      FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) ->
      (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term))
  =
  fun vfs ->
    fun br ->
      let uu___ = br in
      match uu___ with
      | (pat, wopt, body) ->
          let uu___1 = on_sub_pat vfs pat in
          let uu___2 = FStar_Compiler_Util.map_opt wopt (f_term vfs) in
          let uu___3 = f_term vfs body in (uu___1, uu___2, uu___3)
let (on_sub_comp_typ :
  vfs_t -> FStar_Syntax_Syntax.comp_typ -> FStar_Syntax_Syntax.comp_typ) =
  fun vfs ->
    fun ct ->
      let uu___ =
        FStar_Compiler_List.map (f_univ vfs)
          ct.FStar_Syntax_Syntax.comp_univs in
      let uu___1 = f_term vfs ct.FStar_Syntax_Syntax.result_typ in
      let uu___2 =
        FStar_Compiler_List.map (f_arg vfs)
          ct.FStar_Syntax_Syntax.effect_args in
      {
        FStar_Syntax_Syntax.comp_univs = uu___;
        FStar_Syntax_Syntax.effect_name =
          (ct.FStar_Syntax_Syntax.effect_name);
        FStar_Syntax_Syntax.result_typ = uu___1;
        FStar_Syntax_Syntax.effect_args = uu___2;
        FStar_Syntax_Syntax.flags = (ct.FStar_Syntax_Syntax.flags)
      }
let (on_sub_comp :
  vfs_t ->
    FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun vfs ->
    fun c ->
      let cn =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total typ ->
            let uu___ = f_term vfs typ in FStar_Syntax_Syntax.Total uu___
        | FStar_Syntax_Syntax.GTotal typ ->
            let uu___ = f_term vfs typ in FStar_Syntax_Syntax.GTotal uu___
        | FStar_Syntax_Syntax.Comp ct ->
            let uu___ = on_sub_comp_typ vfs ct in
            FStar_Syntax_Syntax.Comp uu___ in
      FStar_Syntax_Syntax.mk cn c.FStar_Syntax_Syntax.pos
let (__on_decreases :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
     FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
    -> FStar_Syntax_Syntax.cflag -> FStar_Syntax_Syntax.cflag)
  =
  fun f ->
    fun uu___ ->
      match uu___ with
      | FStar_Syntax_Syntax.DECREASES (FStar_Syntax_Syntax.Decreases_lex l)
          ->
          let uu___1 =
            let uu___2 = FStar_Compiler_List.map f l in
            FStar_Syntax_Syntax.Decreases_lex uu___2 in
          FStar_Syntax_Syntax.DECREASES uu___1
      | FStar_Syntax_Syntax.DECREASES (FStar_Syntax_Syntax.Decreases_wf
          (r, t)) ->
          let uu___1 =
            let uu___2 =
              let uu___3 = f r in let uu___4 = f t in (uu___3, uu___4) in
            FStar_Syntax_Syntax.Decreases_wf uu___2 in
          FStar_Syntax_Syntax.DECREASES uu___1
      | f1 -> f1
let (on_sub_residual_comp :
  vfs_t ->
    FStar_Syntax_Syntax.residual_comp -> FStar_Syntax_Syntax.residual_comp)
  =
  fun vfs ->
    fun rc ->
      let uu___ =
        FStar_Compiler_Util.map_opt rc.FStar_Syntax_Syntax.residual_typ
          (f_term vfs) in
      let uu___1 =
        let uu___2 = __on_decreases (f_term vfs) in
        FStar_Compiler_List.map uu___2 rc.FStar_Syntax_Syntax.residual_flags in
      {
        FStar_Syntax_Syntax.residual_effect =
          (rc.FStar_Syntax_Syntax.residual_effect);
        FStar_Syntax_Syntax.residual_typ = uu___;
        FStar_Syntax_Syntax.residual_flags = uu___1
      }
let (on_sub_univ :
  vfs_t -> FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) =
  fun vfs ->
    fun u ->
      let u1 = FStar_Syntax_Subst.compress_univ u in
      match u1 with
      | FStar_Syntax_Syntax.U_max us ->
          let uu___ = FStar_Compiler_List.map (f_univ vfs) us in
          FStar_Syntax_Syntax.U_max uu___
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu___ = f_univ vfs u2 in FStar_Syntax_Syntax.U_succ uu___
      | FStar_Syntax_Syntax.U_zero -> u1
      | FStar_Syntax_Syntax.U_bvar uu___ -> u1
      | FStar_Syntax_Syntax.U_name uu___ -> u1
      | FStar_Syntax_Syntax.U_unknown -> u1
      | FStar_Syntax_Syntax.U_unif uu___ -> u1
let (on_sub_wp_eff_combinators :
  vfs_t ->
    FStar_Syntax_Syntax.wp_eff_combinators ->
      FStar_Syntax_Syntax.wp_eff_combinators)
  =
  fun vfs ->
    fun wpcs ->
      let uu___ = f_tscheme vfs wpcs.FStar_Syntax_Syntax.ret_wp in
      let uu___1 = f_tscheme vfs wpcs.FStar_Syntax_Syntax.bind_wp in
      let uu___2 = f_tscheme vfs wpcs.FStar_Syntax_Syntax.stronger in
      let uu___3 = f_tscheme vfs wpcs.FStar_Syntax_Syntax.if_then_else in
      let uu___4 = f_tscheme vfs wpcs.FStar_Syntax_Syntax.ite_wp in
      let uu___5 = f_tscheme vfs wpcs.FStar_Syntax_Syntax.close_wp in
      let uu___6 = f_tscheme vfs wpcs.FStar_Syntax_Syntax.trivial in
      let uu___7 =
        FStar_Compiler_Util.map_opt wpcs.FStar_Syntax_Syntax.repr
          (f_tscheme vfs) in
      let uu___8 =
        FStar_Compiler_Util.map_opt wpcs.FStar_Syntax_Syntax.return_repr
          (f_tscheme vfs) in
      let uu___9 =
        FStar_Compiler_Util.map_opt wpcs.FStar_Syntax_Syntax.bind_repr
          (f_tscheme vfs) in
      {
        FStar_Syntax_Syntax.ret_wp = uu___;
        FStar_Syntax_Syntax.bind_wp = uu___1;
        FStar_Syntax_Syntax.stronger = uu___2;
        FStar_Syntax_Syntax.if_then_else = uu___3;
        FStar_Syntax_Syntax.ite_wp = uu___4;
        FStar_Syntax_Syntax.close_wp = uu___5;
        FStar_Syntax_Syntax.trivial = uu___6;
        FStar_Syntax_Syntax.repr = uu___7;
        FStar_Syntax_Syntax.return_repr = uu___8;
        FStar_Syntax_Syntax.bind_repr = uu___9
      }
let (on_sub_layered_eff_combinators :
  vfs_t ->
    FStar_Syntax_Syntax.layered_eff_combinators ->
      FStar_Syntax_Syntax.layered_eff_combinators)
  =
  fun vfs ->
    fun lecs ->
      let f_tscheme1 = f_tscheme vfs in
      let uu___ =
        on_tuple2 f_tscheme1 f_tscheme1 lecs.FStar_Syntax_Syntax.l_repr in
      let uu___1 =
        on_tuple2 f_tscheme1 f_tscheme1 lecs.FStar_Syntax_Syntax.l_return in
      let uu___2 =
        on_tuple3 f_tscheme1 f_tscheme1 id lecs.FStar_Syntax_Syntax.l_bind in
      let uu___3 =
        on_tuple3 f_tscheme1 f_tscheme1 id lecs.FStar_Syntax_Syntax.l_subcomp in
      let uu___4 =
        on_tuple3 f_tscheme1 f_tscheme1 id
          lecs.FStar_Syntax_Syntax.l_if_then_else in
      let uu___5 =
        FStar_Compiler_Util.map_option (on_tuple2 f_tscheme1 f_tscheme1)
          lecs.FStar_Syntax_Syntax.l_close in
      {
        FStar_Syntax_Syntax.l_repr = uu___;
        FStar_Syntax_Syntax.l_return = uu___1;
        FStar_Syntax_Syntax.l_bind = uu___2;
        FStar_Syntax_Syntax.l_subcomp = uu___3;
        FStar_Syntax_Syntax.l_if_then_else = uu___4;
        FStar_Syntax_Syntax.l_close = uu___5
      }
let (on_sub_combinators :
  vfs_t ->
    FStar_Syntax_Syntax.eff_combinators ->
      FStar_Syntax_Syntax.eff_combinators)
  =
  fun vfs ->
    fun cbs ->
      match cbs with
      | FStar_Syntax_Syntax.Primitive_eff wpcs ->
          let wpcs1 = on_sub_wp_eff_combinators vfs wpcs in
          FStar_Syntax_Syntax.Primitive_eff wpcs1
      | FStar_Syntax_Syntax.DM4F_eff wpcs ->
          let wpcs1 = on_sub_wp_eff_combinators vfs wpcs in
          FStar_Syntax_Syntax.DM4F_eff wpcs1
      | FStar_Syntax_Syntax.Layered_eff lecs ->
          let lecs1 = on_sub_layered_eff_combinators vfs lecs in
          FStar_Syntax_Syntax.Layered_eff lecs1
let (on_sub_effect_signature :
  vfs_t ->
    FStar_Syntax_Syntax.effect_signature ->
      FStar_Syntax_Syntax.effect_signature)
  =
  fun vfs ->
    fun es ->
      match es with
      | FStar_Syntax_Syntax.Layered_eff_sig (n, (us, t)) ->
          let t1 = f_term vfs t in
          FStar_Syntax_Syntax.Layered_eff_sig (n, (us, t1))
      | FStar_Syntax_Syntax.WP_eff_sig (us, t) ->
          let t1 = f_term vfs t in FStar_Syntax_Syntax.WP_eff_sig (us, t1)
let (on_sub_action :
  vfs_t -> FStar_Syntax_Syntax.action -> FStar_Syntax_Syntax.action) =
  fun vfs ->
    fun a ->
      let uu___ =
        FStar_Compiler_List.map (f_binder vfs)
          a.FStar_Syntax_Syntax.action_params in
      let uu___1 = f_term vfs a.FStar_Syntax_Syntax.action_defn in
      let uu___2 = f_term vfs a.FStar_Syntax_Syntax.action_typ in
      {
        FStar_Syntax_Syntax.action_name = (a.FStar_Syntax_Syntax.action_name);
        FStar_Syntax_Syntax.action_unqualified_name =
          (a.FStar_Syntax_Syntax.action_unqualified_name);
        FStar_Syntax_Syntax.action_univs =
          (a.FStar_Syntax_Syntax.action_univs);
        FStar_Syntax_Syntax.action_params = uu___;
        FStar_Syntax_Syntax.action_defn = uu___1;
        FStar_Syntax_Syntax.action_typ = uu___2
      }
let rec (on_sub_sigelt' :
  vfs_t -> FStar_Syntax_Syntax.sigelt' -> FStar_Syntax_Syntax.sigelt') =
  fun vfs ->
    fun se ->
      match se with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          { FStar_Syntax_Syntax.lid = lid; FStar_Syntax_Syntax.us = unames;
            FStar_Syntax_Syntax.params = bs;
            FStar_Syntax_Syntax.num_uniform_params = num_uniform;
            FStar_Syntax_Syntax.t = typ;
            FStar_Syntax_Syntax.mutuals = mutuals;
            FStar_Syntax_Syntax.ds = ctors;_}
          ->
          let uu___ =
            let uu___1 = FStar_Compiler_List.map (f_binder vfs) bs in
            let uu___2 = f_term vfs typ in
            {
              FStar_Syntax_Syntax.lid = lid;
              FStar_Syntax_Syntax.us = unames;
              FStar_Syntax_Syntax.params = uu___1;
              FStar_Syntax_Syntax.num_uniform_params = num_uniform;
              FStar_Syntax_Syntax.t = uu___2;
              FStar_Syntax_Syntax.mutuals = mutuals;
              FStar_Syntax_Syntax.ds = ctors
            } in
          FStar_Syntax_Syntax.Sig_inductive_typ uu___
      | FStar_Syntax_Syntax.Sig_bundle
          { FStar_Syntax_Syntax.ses = ses; FStar_Syntax_Syntax.lids = lids;_}
          ->
          let uu___ =
            let uu___1 = FStar_Compiler_List.map (on_sub_sigelt vfs) ses in
            {
              FStar_Syntax_Syntax.ses = uu___1;
              FStar_Syntax_Syntax.lids = lids
            } in
          FStar_Syntax_Syntax.Sig_bundle uu___
      | FStar_Syntax_Syntax.Sig_datacon
          { FStar_Syntax_Syntax.lid1 = dlid;
            FStar_Syntax_Syntax.us1 = unames; FStar_Syntax_Syntax.t1 = typ;
            FStar_Syntax_Syntax.ty_lid = tlid;
            FStar_Syntax_Syntax.num_ty_params = nparams;
            FStar_Syntax_Syntax.mutuals1 = mutuals;_}
          ->
          let uu___ =
            let uu___1 = f_term vfs typ in
            {
              FStar_Syntax_Syntax.lid1 = dlid;
              FStar_Syntax_Syntax.us1 = unames;
              FStar_Syntax_Syntax.t1 = uu___1;
              FStar_Syntax_Syntax.ty_lid = tlid;
              FStar_Syntax_Syntax.num_ty_params = nparams;
              FStar_Syntax_Syntax.mutuals1 = mutuals
            } in
          FStar_Syntax_Syntax.Sig_datacon uu___
      | FStar_Syntax_Syntax.Sig_declare_typ
          { FStar_Syntax_Syntax.lid2 = lid; FStar_Syntax_Syntax.us2 = unames;
            FStar_Syntax_Syntax.t2 = typ;_}
          ->
          let uu___ =
            let uu___1 = f_term vfs typ in
            {
              FStar_Syntax_Syntax.lid2 = lid;
              FStar_Syntax_Syntax.us2 = unames;
              FStar_Syntax_Syntax.t2 = uu___1
            } in
          FStar_Syntax_Syntax.Sig_declare_typ uu___
      | FStar_Syntax_Syntax.Sig_let
          { FStar_Syntax_Syntax.lbs1 = (is_rec, lbs);
            FStar_Syntax_Syntax.lids1 = mutuals;_}
          ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                FStar_Compiler_List.map (on_sub_letbinding vfs) lbs in
              (is_rec, uu___2) in
            {
              FStar_Syntax_Syntax.lbs1 = uu___1;
              FStar_Syntax_Syntax.lids1 = mutuals
            } in
          FStar_Syntax_Syntax.Sig_let uu___
      | FStar_Syntax_Syntax.Sig_assume
          { FStar_Syntax_Syntax.lid3 = lid; FStar_Syntax_Syntax.us3 = unames;
            FStar_Syntax_Syntax.phi1 = phi;_}
          ->
          let uu___ =
            let uu___1 = f_term vfs phi in
            {
              FStar_Syntax_Syntax.lid3 = lid;
              FStar_Syntax_Syntax.us3 = unames;
              FStar_Syntax_Syntax.phi1 = uu___1
            } in
          FStar_Syntax_Syntax.Sig_assume uu___
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let ed1 =
            let uu___ =
              FStar_Compiler_List.map (f_binder vfs)
                ed.FStar_Syntax_Syntax.binders in
            let uu___1 =
              on_sub_effect_signature vfs ed.FStar_Syntax_Syntax.signature in
            let uu___2 =
              on_sub_combinators vfs ed.FStar_Syntax_Syntax.combinators in
            let uu___3 =
              FStar_Compiler_List.map (on_sub_action vfs)
                ed.FStar_Syntax_Syntax.actions in
            let uu___4 =
              FStar_Compiler_List.map (f_term vfs)
                ed.FStar_Syntax_Syntax.eff_attrs in
            {
              FStar_Syntax_Syntax.mname = (ed.FStar_Syntax_Syntax.mname);
              FStar_Syntax_Syntax.cattributes =
                (ed.FStar_Syntax_Syntax.cattributes);
              FStar_Syntax_Syntax.univs = (ed.FStar_Syntax_Syntax.univs);
              FStar_Syntax_Syntax.binders = uu___;
              FStar_Syntax_Syntax.signature = uu___1;
              FStar_Syntax_Syntax.combinators = uu___2;
              FStar_Syntax_Syntax.actions = uu___3;
              FStar_Syntax_Syntax.eff_attrs = uu___4;
              FStar_Syntax_Syntax.extraction_mode =
                (ed.FStar_Syntax_Syntax.extraction_mode)
            } in
          FStar_Syntax_Syntax.Sig_new_effect ed1
      | FStar_Syntax_Syntax.Sig_sub_effect se1 ->
          let se2 =
            let uu___ =
              FStar_Compiler_Util.map_opt se1.FStar_Syntax_Syntax.lift_wp
                (f_tscheme vfs) in
            let uu___1 =
              FStar_Compiler_Util.map_opt se1.FStar_Syntax_Syntax.lift
                (f_tscheme vfs) in
            {
              FStar_Syntax_Syntax.source = (se1.FStar_Syntax_Syntax.source);
              FStar_Syntax_Syntax.target = (se1.FStar_Syntax_Syntax.target);
              FStar_Syntax_Syntax.lift_wp = uu___;
              FStar_Syntax_Syntax.lift = uu___1;
              FStar_Syntax_Syntax.kind = (se1.FStar_Syntax_Syntax.kind)
            } in
          FStar_Syntax_Syntax.Sig_sub_effect se2
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          { FStar_Syntax_Syntax.lid4 = lid;
            FStar_Syntax_Syntax.us4 = univ_names;
            FStar_Syntax_Syntax.bs2 = binders;
            FStar_Syntax_Syntax.comp1 = comp;
            FStar_Syntax_Syntax.cflags = flags;_}
          ->
          let binders1 = FStar_Compiler_List.map (f_binder vfs) binders in
          let comp1 = f_comp vfs comp in
          let flags1 =
            let uu___ = __on_decreases (f_term vfs) in
            FStar_Compiler_List.map uu___ flags in
          FStar_Syntax_Syntax.Sig_effect_abbrev
            {
              FStar_Syntax_Syntax.lid4 = lid;
              FStar_Syntax_Syntax.us4 = univ_names;
              FStar_Syntax_Syntax.bs2 = binders1;
              FStar_Syntax_Syntax.comp1 = comp1;
              FStar_Syntax_Syntax.cflags = flags1
            }
      | FStar_Syntax_Syntax.Sig_pragma uu___ -> se
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          { FStar_Syntax_Syntax.m_lid = m; FStar_Syntax_Syntax.n_lid = n;
            FStar_Syntax_Syntax.p_lid = p;
            FStar_Syntax_Syntax.tm3 = (us_t, t);
            FStar_Syntax_Syntax.typ = (us_ty, ty);
            FStar_Syntax_Syntax.kind1 = k;_}
          ->
          let t1 = f_term vfs t in
          let ty1 = f_term vfs ty in
          FStar_Syntax_Syntax.Sig_polymonadic_bind
            {
              FStar_Syntax_Syntax.m_lid = m;
              FStar_Syntax_Syntax.n_lid = n;
              FStar_Syntax_Syntax.p_lid = p;
              FStar_Syntax_Syntax.tm3 = (us_t, t1);
              FStar_Syntax_Syntax.typ = (us_ty, ty1);
              FStar_Syntax_Syntax.kind1 = k
            }
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
          { FStar_Syntax_Syntax.m_lid1 = m; FStar_Syntax_Syntax.n_lid1 = n;
            FStar_Syntax_Syntax.tm4 = (us_t, t);
            FStar_Syntax_Syntax.typ1 = (us_ty, ty);
            FStar_Syntax_Syntax.kind2 = k;_}
          ->
          let t1 = f_term vfs t in
          let ty1 = f_term vfs ty in
          FStar_Syntax_Syntax.Sig_polymonadic_subcomp
            {
              FStar_Syntax_Syntax.m_lid1 = m;
              FStar_Syntax_Syntax.n_lid1 = n;
              FStar_Syntax_Syntax.tm4 = (us_t, t1);
              FStar_Syntax_Syntax.typ1 = (us_ty, ty1);
              FStar_Syntax_Syntax.kind2 = k
            }
      | FStar_Syntax_Syntax.Sig_fail
          { FStar_Syntax_Syntax.errs = errs;
            FStar_Syntax_Syntax.fail_in_lax = fail_in_lax;
            FStar_Syntax_Syntax.ses1 = ses;_}
          ->
          let uu___ =
            let uu___1 = FStar_Compiler_List.map (on_sub_sigelt vfs) ses in
            {
              FStar_Syntax_Syntax.errs = errs;
              FStar_Syntax_Syntax.fail_in_lax = fail_in_lax;
              FStar_Syntax_Syntax.ses1 = uu___1
            } in
          FStar_Syntax_Syntax.Sig_fail uu___
      | FStar_Syntax_Syntax.Sig_splice
          { FStar_Syntax_Syntax.is_typed = is_typed;
            FStar_Syntax_Syntax.lids2 = lids;
            FStar_Syntax_Syntax.tac = tac;_}
          ->
          let uu___ =
            let uu___1 = f_term vfs tac in
            {
              FStar_Syntax_Syntax.is_typed = is_typed;
              FStar_Syntax_Syntax.lids2 = lids;
              FStar_Syntax_Syntax.tac = uu___1
            } in
          FStar_Syntax_Syntax.Sig_splice uu___
      | uu___ -> failwith "on_sub_sigelt: missing case"
and (on_sub_sigelt :
  vfs_t -> FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun vfs ->
    fun se ->
      let uu___ = on_sub_sigelt' vfs se.FStar_Syntax_Syntax.sigel in
      let uu___1 =
        FStar_Compiler_List.map (f_term vfs) se.FStar_Syntax_Syntax.sigattrs in
      {
        FStar_Syntax_Syntax.sigel = uu___;
        FStar_Syntax_Syntax.sigrng = (se.FStar_Syntax_Syntax.sigrng);
        FStar_Syntax_Syntax.sigquals = (se.FStar_Syntax_Syntax.sigquals);
        FStar_Syntax_Syntax.sigmeta = (se.FStar_Syntax_Syntax.sigmeta);
        FStar_Syntax_Syntax.sigattrs = uu___1;
        FStar_Syntax_Syntax.sigopens_and_abbrevs =
          (se.FStar_Syntax_Syntax.sigopens_and_abbrevs);
        FStar_Syntax_Syntax.sigopts = (se.FStar_Syntax_Syntax.sigopts)
      }
let (tie_bu : vfs_t -> vfs_t FStar_Compiler_Effect.ref) =
  fun vfs ->
    let r = FStar_Compiler_Util.mk_ref novfs in
    FStar_Compiler_Effect.op_Colon_Equals r
      {
        f_term =
          (fun x ->
             let uu___1 =
               let uu___2 = FStar_Compiler_Effect.op_Bang r in
               on_sub_term uu___2 x in
             f_term vfs uu___1);
        f_binder =
          (fun x ->
             let uu___1 =
               let uu___2 = FStar_Compiler_Effect.op_Bang r in
               on_sub_binder uu___2 x in
             f_binder vfs uu___1);
        f_binding_bv =
          (fun x ->
             let uu___1 =
               let uu___2 = FStar_Compiler_Effect.op_Bang r in
               on_sub_binding_bv uu___2 x in
             f_binding_bv vfs uu___1);
        f_br =
          (fun x ->
             let uu___1 =
               let uu___2 = FStar_Compiler_Effect.op_Bang r in
               on_sub_br uu___2 x in
             f_br vfs uu___1);
        f_comp =
          (fun x ->
             let uu___1 =
               let uu___2 = FStar_Compiler_Effect.op_Bang r in
               on_sub_comp uu___2 x in
             f_comp vfs uu___1);
        f_residual_comp =
          (fun x ->
             let uu___1 =
               let uu___2 = FStar_Compiler_Effect.op_Bang r in
               on_sub_residual_comp uu___2 x in
             f_residual_comp vfs uu___1);
        f_univ =
          (fun x ->
             let uu___1 =
               let uu___2 = FStar_Compiler_Effect.op_Bang r in
               on_sub_univ uu___2 x in
             f_univ vfs uu___1)
      };
    r
let (visit_term :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun f ->
    fun tm ->
      let r =
        let uu___ =
          tie_bu
            {
              f_term = f;
              f_binder = (novfs.f_binder);
              f_binding_bv = (novfs.f_binding_bv);
              f_br = (novfs.f_br);
              f_comp = (novfs.f_comp);
              f_residual_comp = (novfs.f_residual_comp);
              f_univ = (novfs.f_univ)
            } in
        FStar_Compiler_Effect.op_Bang uu___ in
      r.f_term tm
let (visit_term_univs :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun f ->
    fun g ->
      fun tm ->
        let r =
          let uu___ =
            tie_bu
              {
                f_term = f;
                f_binder = (novfs.f_binder);
                f_binding_bv = (novfs.f_binding_bv);
                f_br = (novfs.f_br);
                f_comp = (novfs.f_comp);
                f_residual_comp = (novfs.f_residual_comp);
                f_univ = g
              } in
          FStar_Compiler_Effect.op_Bang uu___ in
        r.f_term tm
let (visit_sigelt :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    (FStar_Syntax_Syntax.universe -> FStar_Syntax_Syntax.universe) ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt)
  =
  fun f ->
    fun g ->
      fun se ->
        let r =
          let uu___ =
            tie_bu
              {
                f_term = f;
                f_binder = (novfs.f_binder);
                f_binding_bv = (novfs.f_binding_bv);
                f_br = (novfs.f_br);
                f_comp = (novfs.f_comp);
                f_residual_comp = (novfs.f_residual_comp);
                f_univ = g
              } in
          FStar_Compiler_Effect.op_Bang uu___ in
        on_sub_sigelt r se