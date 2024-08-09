open Prims
type ('m, 'a) endo = 'a -> 'm
type 'm lvm =
  {
  lvm_monad: 'm FStar_Class_Monad.monad ;
  f_term: ('m, FStar_Syntax_Syntax.term) endo ;
  f_binder: ('m, FStar_Syntax_Syntax.binder) endo ;
  f_binding_bv: ('m, FStar_Syntax_Syntax.bv) endo ;
  f_br: ('m, FStar_Syntax_Syntax.branch) endo ;
  f_comp: ('m, FStar_Syntax_Syntax.comp) endo ;
  f_residual_comp: ('m, FStar_Syntax_Syntax.residual_comp) endo ;
  f_univ: ('m, FStar_Syntax_Syntax.universe) endo }
let __proj__Mklvm__item__lvm_monad :
  'm . 'm lvm -> 'm FStar_Class_Monad.monad =
  fun projectee ->
    match projectee with
    | { lvm_monad; f_term; f_binder; f_binding_bv; f_br; f_comp;
        f_residual_comp; f_univ;_} -> lvm_monad
let __proj__Mklvm__item__f_term :
  'm . 'm lvm -> ('m, FStar_Syntax_Syntax.term) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad; f_term; f_binder; f_binding_bv; f_br; f_comp;
        f_residual_comp; f_univ;_} -> f_term
let __proj__Mklvm__item__f_binder :
  'm . 'm lvm -> ('m, FStar_Syntax_Syntax.binder) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad; f_term; f_binder; f_binding_bv; f_br; f_comp;
        f_residual_comp; f_univ;_} -> f_binder
let __proj__Mklvm__item__f_binding_bv :
  'm . 'm lvm -> ('m, FStar_Syntax_Syntax.bv) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad; f_term; f_binder; f_binding_bv; f_br; f_comp;
        f_residual_comp; f_univ;_} -> f_binding_bv
let __proj__Mklvm__item__f_br :
  'm . 'm lvm -> ('m, FStar_Syntax_Syntax.branch) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad; f_term; f_binder; f_binding_bv; f_br; f_comp;
        f_residual_comp; f_univ;_} -> f_br
let __proj__Mklvm__item__f_comp :
  'm . 'm lvm -> ('m, FStar_Syntax_Syntax.comp) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad; f_term; f_binder; f_binding_bv; f_br; f_comp;
        f_residual_comp; f_univ;_} -> f_comp
let __proj__Mklvm__item__f_residual_comp :
  'm . 'm lvm -> ('m, FStar_Syntax_Syntax.residual_comp) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad; f_term; f_binder; f_binding_bv; f_br; f_comp;
        f_residual_comp; f_univ;_} -> f_residual_comp
let __proj__Mklvm__item__f_univ :
  'm . 'm lvm -> ('m, FStar_Syntax_Syntax.universe) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad; f_term; f_binder; f_binding_bv; f_br; f_comp;
        f_residual_comp; f_univ;_} -> f_univ
let lvm_monad : 'm . 'm lvm -> 'm FStar_Class_Monad.monad =
  fun projectee ->
    match projectee with
    | { lvm_monad = lvm_monad1; f_term; f_binder; f_binding_bv; f_br; 
        f_comp; f_residual_comp; f_univ;_} -> lvm_monad1
let f_term : 'm . 'm lvm -> ('m, FStar_Syntax_Syntax.term) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad = lvm_monad1; f_term = f_term1; f_binder; f_binding_bv;
        f_br; f_comp; f_residual_comp; f_univ;_} -> f_term1
let f_binder : 'm . 'm lvm -> ('m, FStar_Syntax_Syntax.binder) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad = lvm_monad1; f_term = f_term1; f_binder = f_binder1;
        f_binding_bv; f_br; f_comp; f_residual_comp; f_univ;_} -> f_binder1
let f_binding_bv : 'm . 'm lvm -> ('m, FStar_Syntax_Syntax.bv) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad = lvm_monad1; f_term = f_term1; f_binder = f_binder1;
        f_binding_bv = f_binding_bv1; f_br; f_comp; f_residual_comp;
        f_univ;_} -> f_binding_bv1
let f_br : 'm . 'm lvm -> ('m, FStar_Syntax_Syntax.branch) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad = lvm_monad1; f_term = f_term1; f_binder = f_binder1;
        f_binding_bv = f_binding_bv1; f_br = f_br1; f_comp; f_residual_comp;
        f_univ;_} -> f_br1
let f_comp : 'm . 'm lvm -> ('m, FStar_Syntax_Syntax.comp) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad = lvm_monad1; f_term = f_term1; f_binder = f_binder1;
        f_binding_bv = f_binding_bv1; f_br = f_br1; f_comp = f_comp1;
        f_residual_comp; f_univ;_} -> f_comp1
let f_residual_comp :
  'm . 'm lvm -> ('m, FStar_Syntax_Syntax.residual_comp) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad = lvm_monad1; f_term = f_term1; f_binder = f_binder1;
        f_binding_bv = f_binding_bv1; f_br = f_br1; f_comp = f_comp1;
        f_residual_comp = f_residual_comp1; f_univ;_} -> f_residual_comp1
let f_univ : 'm . 'm lvm -> ('m, FStar_Syntax_Syntax.universe) endo =
  fun projectee ->
    match projectee with
    | { lvm_monad = lvm_monad1; f_term = f_term1; f_binder = f_binder1;
        f_binding_bv = f_binding_bv1; f_br = f_br1; f_comp = f_comp1;
        f_residual_comp = f_residual_comp1; f_univ = f_univ1;_} -> f_univ1
let _lvm_monad : 'm . 'm lvm -> 'm FStar_Class_Monad.monad =
  fun uu___ -> lvm_monad uu___
let novfs : 'm . 'm FStar_Class_Monad.monad -> 'm lvm =
  fun uu___ ->
    {
      lvm_monad = uu___;
      f_term = (Obj.magic (FStar_Class_Monad.return uu___ ()));
      f_binder = (Obj.magic (FStar_Class_Monad.return uu___ ()));
      f_binding_bv = (Obj.magic (FStar_Class_Monad.return uu___ ()));
      f_br = (Obj.magic (FStar_Class_Monad.return uu___ ()));
      f_comp = (Obj.magic (FStar_Class_Monad.return uu___ ()));
      f_residual_comp = (Obj.magic (FStar_Class_Monad.return uu___ ()));
      f_univ = (Obj.magic (FStar_Class_Monad.return uu___ ()))
    }
let f_aqual : 'm . 'm lvm -> FStar_Syntax_Syntax.arg_qualifier -> 'm =
  fun uu___ ->
    fun aq ->
      let uu___1 = aq in
      match uu___1 with
      | { FStar_Syntax_Syntax.aqual_implicit = i;
          FStar_Syntax_Syntax.aqual_attributes = attrs;_} ->
          let uu___2 =
            FStar_Class_Monad.mapM (_lvm_monad uu___) () ()
              (fun uu___3 -> (Obj.magic (f_term uu___)) uu___3)
              (Obj.magic attrs) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad uu___) () () uu___2
            (fun uu___3 ->
               (fun attrs1 ->
                  let attrs1 = Obj.magic attrs1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad uu___) ()
                       (Obj.magic
                          {
                            FStar_Syntax_Syntax.aqual_implicit = i;
                            FStar_Syntax_Syntax.aqual_attributes = attrs1
                          }))) uu___3)
let on_sub_arg : 'm . 'm lvm -> FStar_Syntax_Syntax.arg -> 'm =
  fun uu___ ->
    fun a ->
      let uu___1 = a in
      match uu___1 with
      | (t, q) ->
          let uu___2 = f_term uu___ t in
          FStar_Class_Monad.op_let_Bang (_lvm_monad uu___) () () uu___2
            (fun uu___3 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  let uu___3 =
                    FStar_Class_Monad.map_optM (_lvm_monad uu___) () ()
                      (fun uu___4 -> (Obj.magic (f_aqual uu___)) uu___4)
                      (Obj.magic q) in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad uu___) () ()
                       uu___3
                       (fun uu___4 ->
                          (fun q1 ->
                             let q1 = Obj.magic q1 in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad uu___)
                                  () (Obj.magic (t1, q1)))) uu___4))) uu___3)
let on_sub_tscheme :
  'm .
    'm FStar_Class_Monad.monad -> 'm lvm -> FStar_Syntax_Syntax.tscheme -> 'm
  =
  fun uu___ ->
    fun uu___1 ->
      fun ts ->
        let uu___2 = ts in
        match uu___2 with
        | (us, t) ->
            let uu___3 = f_term uu___1 t in
            FStar_Class_Monad.op_let_Bang uu___ () () uu___3
              (fun uu___4 ->
                 (fun t1 ->
                    let t1 = Obj.magic t1 in
                    Obj.magic
                      (FStar_Class_Monad.return uu___ () (Obj.magic (us, t1))))
                   uu___4)
let f_arg : 'm . 'm lvm -> FStar_Syntax_Syntax.arg -> 'm =
  fun uu___ -> on_sub_arg uu___
let f_args : 'm . 'm lvm -> FStar_Syntax_Syntax.arg Prims.list -> 'm =
  fun uu___1 ->
    fun uu___ ->
      (fun d ->
         let uu___ = f_arg d in
         Obj.magic
           (FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic uu___) uu___1))) uu___1 uu___
let f_tscheme : 'm . 'm lvm -> FStar_Syntax_Syntax.tscheme -> 'm =
  fun uu___ -> on_sub_tscheme (_lvm_monad uu___) uu___
let on_sub_meta : 'm . 'm lvm -> FStar_Syntax_Syntax.metadata -> 'm =
  fun d ->
    fun md ->
      match md with
      | FStar_Syntax_Syntax.Meta_pattern (pats, args) ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (f_term d)) uu___1) (Obj.magic pats) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun pats1 ->
                  let pats1 = Obj.magic pats1 in
                  let uu___1 =
                    let uu___2 = f_args d in
                    FStar_Class_Monad.mapM (_lvm_monad d) () ()
                      (fun uu___3 -> (Obj.magic uu___2) uu___3)
                      (Obj.magic args) in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun args1 ->
                             let args1 = Obj.magic args1 in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic
                                     (FStar_Syntax_Syntax.Meta_pattern
                                        (pats1, args1))))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Meta_monadic (m1, typ) ->
          let uu___ = f_term d typ in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun typ1 ->
                  let typ1 = Obj.magic typ1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Meta_monadic (m1, typ1)))))
                 uu___1)
      | FStar_Syntax_Syntax.Meta_monadic_lift (m1, m2, typ) ->
          let uu___ = f_term d typ in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun typ1 ->
                  let typ1 = Obj.magic typ1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Meta_monadic_lift
                             (m1, m2, typ1))))) uu___1)
      | FStar_Syntax_Syntax.Meta_named lid ->
          FStar_Class_Monad.return (_lvm_monad d) ()
            (Obj.magic (FStar_Syntax_Syntax.Meta_named lid))
      | FStar_Syntax_Syntax.Meta_labeled (s, r, b) ->
          FStar_Class_Monad.return (_lvm_monad d) ()
            (Obj.magic (FStar_Syntax_Syntax.Meta_labeled (s, r, b)))
      | FStar_Syntax_Syntax.Meta_desugared i ->
          FStar_Class_Monad.return (_lvm_monad d) ()
            (Obj.magic (FStar_Syntax_Syntax.Meta_desugared i))
let on_sub_letbinding : 'm . 'm lvm -> FStar_Syntax_Syntax.letbinding -> 'm =
  fun uu___ ->
    fun lb ->
      let uu___1 =
        match lb.FStar_Syntax_Syntax.lbname with
        | FStar_Pervasives.Inl bv ->
            let uu___2 = f_binding_bv uu___ bv in
            FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad uu___) () ()
              (fun uu___3 ->
                 (fun uu___3 ->
                    let uu___3 = Obj.magic uu___3 in
                    Obj.magic (FStar_Pervasives.Inl uu___3)) uu___3) uu___2
        | FStar_Pervasives.Inr fv ->
            FStar_Class_Monad.return (_lvm_monad uu___) ()
              (Obj.magic (FStar_Pervasives.Inr fv)) in
      FStar_Class_Monad.op_let_Bang (_lvm_monad uu___) () () uu___1
        (fun uu___2 ->
           (fun lbname ->
              let lbname = Obj.magic lbname in
              let lbunivs = lb.FStar_Syntax_Syntax.lbunivs in
              let uu___2 = f_term uu___ lb.FStar_Syntax_Syntax.lbtyp in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang (_lvm_monad uu___) () ()
                   uu___2
                   (fun uu___3 ->
                      (fun lbtyp ->
                         let lbtyp = Obj.magic lbtyp in
                         let lbeff = lb.FStar_Syntax_Syntax.lbeff in
                         let uu___3 =
                           FStar_Class_Monad.mapM (_lvm_monad uu___) () ()
                             (fun uu___4 -> (Obj.magic (f_term uu___)) uu___4)
                             (Obj.magic lb.FStar_Syntax_Syntax.lbattrs) in
                         Obj.magic
                           (FStar_Class_Monad.op_let_Bang (_lvm_monad uu___)
                              () () uu___3
                              (fun uu___4 ->
                                 (fun lbattrs ->
                                    let lbattrs = Obj.magic lbattrs in
                                    let lbpos = lb.FStar_Syntax_Syntax.lbpos in
                                    let uu___4 =
                                      f_term uu___
                                        lb.FStar_Syntax_Syntax.lbdef in
                                    Obj.magic
                                      (FStar_Class_Monad.op_let_Bang
                                         (_lvm_monad uu___) () () uu___4
                                         (fun uu___5 ->
                                            (fun lbdef ->
                                               let lbdef = Obj.magic lbdef in
                                               Obj.magic
                                                 (FStar_Class_Monad.return
                                                    (_lvm_monad uu___) ()
                                                    (Obj.magic
                                                       {
                                                         FStar_Syntax_Syntax.lbname
                                                           = lbname;
                                                         FStar_Syntax_Syntax.lbunivs
                                                           = lbunivs;
                                                         FStar_Syntax_Syntax.lbtyp
                                                           = lbtyp;
                                                         FStar_Syntax_Syntax.lbeff
                                                           = lbeff;
                                                         FStar_Syntax_Syntax.lbdef
                                                           = lbdef;
                                                         FStar_Syntax_Syntax.lbattrs
                                                           = lbattrs;
                                                         FStar_Syntax_Syntax.lbpos
                                                           = lbpos
                                                       }))) uu___5))) uu___4)))
                        uu___3))) uu___2)
let on_sub_ascription : 'm . 'm lvm -> FStar_Syntax_Syntax.ascription -> 'm =
  fun uu___ ->
    fun a ->
      let uu___1 = a in
      match uu___1 with
      | (tc, tacopt, b) ->
          let uu___2 =
            match tc with
            | FStar_Pervasives.Inl t ->
                let uu___3 = f_term uu___ t in
                FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad uu___)
                  () ()
                  (fun uu___4 ->
                     (fun uu___4 ->
                        let uu___4 = Obj.magic uu___4 in
                        Obj.magic (FStar_Pervasives.Inl uu___4)) uu___4)
                  uu___3
            | FStar_Pervasives.Inr c ->
                let uu___3 = f_comp uu___ c in
                FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad uu___)
                  () ()
                  (fun uu___4 ->
                     (fun uu___4 ->
                        let uu___4 = Obj.magic uu___4 in
                        Obj.magic (FStar_Pervasives.Inr uu___4)) uu___4)
                  uu___3 in
          FStar_Class_Monad.op_let_Bang (_lvm_monad uu___) () () uu___2
            (fun uu___3 ->
               (fun tc1 ->
                  let tc1 = Obj.magic tc1 in
                  let uu___3 =
                    FStar_Class_Monad.map_optM (_lvm_monad uu___) () ()
                      (fun uu___4 -> (Obj.magic (f_term uu___)) uu___4)
                      (Obj.magic tacopt) in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad uu___) () ()
                       uu___3
                       (fun uu___4 ->
                          (fun tacopt1 ->
                             let tacopt1 = Obj.magic tacopt1 in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad uu___)
                                  () (Obj.magic (tc1, tacopt1, b)))) uu___4)))
                 uu___3)
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
let on_sub_term : 'm . 'm lvm -> FStar_Syntax_Syntax.term -> 'm =
  fun d ->
    fun tm ->
      let mk t = FStar_Syntax_Syntax.mk t tm.FStar_Syntax_Syntax.pos in
      let tm1 = compress tm in
      match tm1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_lazy uu___ ->
          FStar_Compiler_Effect.failwith "impos"
      | FStar_Syntax_Syntax.Tm_delayed uu___ ->
          FStar_Compiler_Effect.failwith "impos"
      | FStar_Syntax_Syntax.Tm_fvar uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic tm1)
      | FStar_Syntax_Syntax.Tm_constant uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic tm1)
      | FStar_Syntax_Syntax.Tm_unknown ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic tm1)
      | FStar_Syntax_Syntax.Tm_bvar uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic tm1)
      | FStar_Syntax_Syntax.Tm_name uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic tm1)
      | FStar_Syntax_Syntax.Tm_uvar uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic tm1)
      | FStar_Syntax_Syntax.Tm_uinst (f, us) ->
          let uu___ = f_term d f in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun f1 ->
                  let f1 = Obj.magic f1 in
                  let uu___1 =
                    FStar_Class_Monad.mapM (_lvm_monad d) () ()
                      (fun uu___2 -> (Obj.magic (f_univ d)) uu___2)
                      (Obj.magic us) in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun us1 ->
                             let us1 = Obj.magic us1 in
                             let uu___2 =
                               mk (FStar_Syntax_Syntax.Tm_uinst (f1, us1)) in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic uu___2))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Tm_type u ->
          let uu___ = f_univ d u in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun u1 ->
                  let u1 = Obj.magic u1 in
                  let uu___1 = mk (FStar_Syntax_Syntax.Tm_type u1) in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic uu___1))) uu___1)
      | FStar_Syntax_Syntax.Tm_app
          { FStar_Syntax_Syntax.hd = hd; FStar_Syntax_Syntax.args = args;_}
          ->
          let uu___ = f_term d hd in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun hd1 ->
                  let hd1 = Obj.magic hd1 in
                  let uu___1 =
                    let uu___2 = f_arg d in
                    FStar_Class_Monad.mapM (_lvm_monad d) () ()
                      (fun uu___3 -> (Obj.magic uu___2) uu___3)
                      (Obj.magic args) in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun args1 ->
                             let args1 = Obj.magic args1 in
                             let uu___2 =
                               mk
                                 (FStar_Syntax_Syntax.Tm_app
                                    {
                                      FStar_Syntax_Syntax.hd = hd1;
                                      FStar_Syntax_Syntax.args = args1
                                    }) in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic uu___2))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Tm_abs
          { FStar_Syntax_Syntax.bs = bs; FStar_Syntax_Syntax.body = t;
            FStar_Syntax_Syntax.rc_opt = rc_opt;_}
          ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (f_binder d)) uu___1) (Obj.magic bs) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun bs1 ->
                  let bs1 = Obj.magic bs1 in
                  let uu___1 = f_term d t in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun t1 ->
                             let t1 = Obj.magic t1 in
                             let uu___2 =
                               FStar_Class_Monad.map_optM (_lvm_monad d) ()
                                 ()
                                 (fun uu___3 ->
                                    (Obj.magic (f_residual_comp d)) uu___3)
                                 (Obj.magic rc_opt) in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang (_lvm_monad d)
                                  () () uu___2
                                  (fun uu___3 ->
                                     (fun rc_opt1 ->
                                        let rc_opt1 = Obj.magic rc_opt1 in
                                        let uu___3 =
                                          mk
                                            (FStar_Syntax_Syntax.Tm_abs
                                               {
                                                 FStar_Syntax_Syntax.bs = bs1;
                                                 FStar_Syntax_Syntax.body =
                                                   t1;
                                                 FStar_Syntax_Syntax.rc_opt =
                                                   rc_opt1
                                               }) in
                                        Obj.magic
                                          (FStar_Class_Monad.return
                                             (_lvm_monad d) ()
                                             (Obj.magic uu___3))) uu___3)))
                            uu___2))) uu___1)
      | FStar_Syntax_Syntax.Tm_arrow
          { FStar_Syntax_Syntax.bs1 = bs; FStar_Syntax_Syntax.comp = c;_} ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (f_binder d)) uu___1) (Obj.magic bs) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun bs1 ->
                  let bs1 = Obj.magic bs1 in
                  let uu___1 = f_comp d c in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun c1 ->
                             let c1 = Obj.magic c1 in
                             let uu___2 =
                               mk
                                 (FStar_Syntax_Syntax.Tm_arrow
                                    {
                                      FStar_Syntax_Syntax.bs1 = bs1;
                                      FStar_Syntax_Syntax.comp = c1
                                    }) in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic uu___2))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Tm_refine
          { FStar_Syntax_Syntax.b = bv; FStar_Syntax_Syntax.phi = phi;_} ->
          let uu___ = f_binding_bv d bv in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun bv1 ->
                  let bv1 = Obj.magic bv1 in
                  let uu___1 = f_term d phi in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun phi1 ->
                             let phi1 = Obj.magic phi1 in
                             let uu___2 =
                               mk
                                 (FStar_Syntax_Syntax.Tm_refine
                                    {
                                      FStar_Syntax_Syntax.b = bv1;
                                      FStar_Syntax_Syntax.phi = phi1
                                    }) in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic uu___2))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Tm_match
          { FStar_Syntax_Syntax.scrutinee = sc;
            FStar_Syntax_Syntax.ret_opt = asc_opt;
            FStar_Syntax_Syntax.brs = brs;
            FStar_Syntax_Syntax.rc_opt1 = rc_opt;_}
          ->
          let uu___ = f_term d sc in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun sc1 ->
                  let sc1 = Obj.magic sc1 in
                  let uu___1 =
                    FStar_Class_Monad.map_optM (_lvm_monad d) () ()
                      (fun uu___2 ->
                         (fun uu___2 ->
                            let uu___2 = Obj.magic uu___2 in
                            match uu___2 with
                            | (b, asc) ->
                                let uu___3 =
                                  let uu___4 = f_binder d b in
                                  FStar_Class_Monad.op_Less_Dollar_Greater
                                    (_lvm_monad d) () ()
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          let uu___5 = Obj.magic uu___5 in
                                          Obj.magic
                                            (fun uu___6 -> (uu___5, uu___6)))
                                         uu___5) uu___4 in
                                let uu___4 = on_sub_ascription d asc in
                                Obj.magic
                                  (FStar_Class_Monad.op_Less_Star_Greater
                                     (_lvm_monad d) () () uu___3 uu___4))
                           uu___2) (Obj.magic asc_opt) in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun asc_opt1 ->
                             let asc_opt1 = Obj.magic asc_opt1 in
                             let uu___2 =
                               FStar_Class_Monad.mapM (_lvm_monad d) () ()
                                 (fun uu___3 -> (Obj.magic (f_br d)) uu___3)
                                 (Obj.magic brs) in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang (_lvm_monad d)
                                  () () uu___2
                                  (fun uu___3 ->
                                     (fun brs1 ->
                                        let brs1 = Obj.magic brs1 in
                                        let uu___3 =
                                          FStar_Class_Monad.map_optM
                                            (_lvm_monad d) () ()
                                            (fun uu___4 ->
                                               (Obj.magic (f_residual_comp d))
                                                 uu___4) (Obj.magic rc_opt) in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             (_lvm_monad d) () () uu___3
                                             (fun uu___4 ->
                                                (fun rc_opt1 ->
                                                   let rc_opt1 =
                                                     Obj.magic rc_opt1 in
                                                   let uu___4 =
                                                     mk
                                                       (FStar_Syntax_Syntax.Tm_match
                                                          {
                                                            FStar_Syntax_Syntax.scrutinee
                                                              = sc1;
                                                            FStar_Syntax_Syntax.ret_opt
                                                              = asc_opt1;
                                                            FStar_Syntax_Syntax.brs
                                                              = brs1;
                                                            FStar_Syntax_Syntax.rc_opt1
                                                              = rc_opt1
                                                          }) in
                                                   Obj.magic
                                                     (FStar_Class_Monad.return
                                                        (_lvm_monad d) ()
                                                        (Obj.magic uu___4)))
                                                  uu___4))) uu___3))) uu___2)))
                 uu___1)
      | FStar_Syntax_Syntax.Tm_ascribed
          { FStar_Syntax_Syntax.tm = e; FStar_Syntax_Syntax.asc = a;
            FStar_Syntax_Syntax.eff_opt = lopt;_}
          ->
          let uu___ = f_term d e in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun e1 ->
                  let e1 = Obj.magic e1 in
                  let uu___1 = on_sub_ascription d a in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun a1 ->
                             let a1 = Obj.magic a1 in
                             let uu___2 =
                               mk
                                 (FStar_Syntax_Syntax.Tm_ascribed
                                    {
                                      FStar_Syntax_Syntax.tm = e1;
                                      FStar_Syntax_Syntax.asc = a1;
                                      FStar_Syntax_Syntax.eff_opt = lopt
                                    }) in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic uu___2))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Tm_let
          { FStar_Syntax_Syntax.lbs = (is_rec, lbs);
            FStar_Syntax_Syntax.body1 = t;_}
          ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (on_sub_letbinding d)) uu___1)
              (Obj.magic lbs) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun lbs1 ->
                  let lbs1 = Obj.magic lbs1 in
                  let uu___1 = f_term d t in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun t1 ->
                             let t1 = Obj.magic t1 in
                             let uu___2 =
                               mk
                                 (FStar_Syntax_Syntax.Tm_let
                                    {
                                      FStar_Syntax_Syntax.lbs =
                                        (is_rec, lbs1);
                                      FStar_Syntax_Syntax.body1 = t1
                                    }) in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic uu___2))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Tm_quoted (tm2, qi) ->
          let uu___ = f_term d tm2 in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun tm3 ->
                  let tm3 = Obj.magic tm3 in
                  let uu___1 = mk (FStar_Syntax_Syntax.Tm_quoted (tm3, qi)) in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic uu___1))) uu___1)
      | FStar_Syntax_Syntax.Tm_meta
          { FStar_Syntax_Syntax.tm2 = t; FStar_Syntax_Syntax.meta = md;_} ->
          let uu___ = f_term d t in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  let uu___1 = on_sub_meta d md in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun md1 ->
                             let md1 = Obj.magic md1 in
                             let uu___2 =
                               mk
                                 (FStar_Syntax_Syntax.Tm_meta
                                    {
                                      FStar_Syntax_Syntax.tm2 = t1;
                                      FStar_Syntax_Syntax.meta = md1
                                    }) in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic uu___2))) uu___2))) uu___1)
let on_sub_binding_bv : 'm . 'm lvm -> FStar_Syntax_Syntax.bv -> 'm =
  fun d ->
    fun x ->
      let uu___ = f_term d x.FStar_Syntax_Syntax.sort in
      FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
        (fun uu___1 ->
           (fun sort ->
              let sort = Obj.magic sort in
              Obj.magic
                (FStar_Class_Monad.return (_lvm_monad d) ()
                   (Obj.magic
                      {
                        FStar_Syntax_Syntax.ppname =
                          (x.FStar_Syntax_Syntax.ppname);
                        FStar_Syntax_Syntax.index =
                          (x.FStar_Syntax_Syntax.index);
                        FStar_Syntax_Syntax.sort = sort
                      }))) uu___1)
let on_sub_binder : 'm . 'm lvm -> FStar_Syntax_Syntax.binder -> 'm =
  fun d ->
    fun b ->
      let uu___ = f_binding_bv d b.FStar_Syntax_Syntax.binder_bv in
      FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
        (fun uu___1 ->
           (fun binder_bv ->
              let binder_bv = Obj.magic binder_bv in
              let uu___1 =
                FStar_Class_Monad.map_optM (_lvm_monad d) () ()
                  (fun uu___2 ->
                     (fun uu___2 ->
                        let uu___2 = Obj.magic uu___2 in
                        match uu___2 with
                        | FStar_Syntax_Syntax.Meta t ->
                            let uu___3 = f_term d t in
                            Obj.magic
                              (FStar_Class_Monad.op_Less_Dollar_Greater
                                 (_lvm_monad d) () ()
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       let uu___4 = Obj.magic uu___4 in
                                       Obj.magic
                                         (FStar_Syntax_Syntax.Meta uu___4))
                                      uu___4) uu___3)
                        | q ->
                            Obj.magic
                              (FStar_Class_Monad.return (_lvm_monad d) ()
                                 (Obj.magic q))) uu___2)
                  (Obj.magic b.FStar_Syntax_Syntax.binder_qual) in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___1
                   (fun uu___2 ->
                      (fun binder_qual ->
                         let binder_qual = Obj.magic binder_qual in
                         let binder_positivity =
                           b.FStar_Syntax_Syntax.binder_positivity in
                         let uu___2 =
                           FStar_Class_Monad.mapM (_lvm_monad d) () ()
                             (fun uu___3 -> (Obj.magic (f_term d)) uu___3)
                             (Obj.magic b.FStar_Syntax_Syntax.binder_attrs) in
                         Obj.magic
                           (FStar_Class_Monad.op_let_Bang (_lvm_monad d) ()
                              () uu___2
                              (fun uu___3 ->
                                 (fun binder_attrs ->
                                    let binder_attrs = Obj.magic binder_attrs in
                                    Obj.magic
                                      (FStar_Class_Monad.return
                                         (_lvm_monad d) ()
                                         (Obj.magic
                                            {
                                              FStar_Syntax_Syntax.binder_bv =
                                                binder_bv;
                                              FStar_Syntax_Syntax.binder_qual
                                                = binder_qual;
                                              FStar_Syntax_Syntax.binder_positivity
                                                = binder_positivity;
                                              FStar_Syntax_Syntax.binder_attrs
                                                = binder_attrs
                                            }))) uu___3))) uu___2))) uu___1)
let rec on_sub_pat : 'm . 'm lvm -> FStar_Syntax_Syntax.pat -> 'm =
  fun d ->
    fun p0 ->
      let mk p =
        {
          FStar_Syntax_Syntax.v = p;
          FStar_Syntax_Syntax.p = (p0.FStar_Syntax_Syntax.p)
        } in
      match p0.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_constant uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic p0)
      | FStar_Syntax_Syntax.Pat_cons (fv, us, subpats) ->
          let uu___ =
            FStar_Class_Monad.map_optM (_lvm_monad d) () ()
              (fun uu___1 ->
                 (Obj.magic
                    (FStar_Class_Monad.mapM (_lvm_monad d) () ()
                       (fun uu___1 -> (Obj.magic (f_univ d)) uu___1))) uu___1)
              (Obj.magic us) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun us1 ->
                  let us1 = Obj.magic us1 in
                  let uu___1 =
                    FStar_Class_Monad.mapM (_lvm_monad d) () ()
                      (fun uu___2 ->
                         (fun uu___2 ->
                            let uu___2 = Obj.magic uu___2 in
                            match uu___2 with
                            | (p, b) ->
                                let uu___3 =
                                  let uu___4 = on_sub_pat d p in
                                  FStar_Class_Monad.op_Less_Dollar_Greater
                                    (_lvm_monad d) () ()
                                    (fun uu___5 ->
                                       (fun uu___5 ->
                                          let uu___5 = Obj.magic uu___5 in
                                          Obj.magic
                                            (fun uu___6 -> (uu___5, uu___6)))
                                         uu___5) uu___4 in
                                let uu___4 =
                                  FStar_Class_Monad.return (_lvm_monad d) ()
                                    (Obj.magic b) in
                                Obj.magic
                                  (FStar_Class_Monad.op_Less_Star_Greater
                                     (_lvm_monad d) () () uu___3 uu___4))
                           uu___2) (Obj.magic subpats) in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun subpats1 ->
                             let subpats1 = Obj.magic subpats1 in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic
                                     (mk
                                        (FStar_Syntax_Syntax.Pat_cons
                                           (fv, us1, subpats1)))))) uu___2)))
                 uu___1)
      | FStar_Syntax_Syntax.Pat_var bv ->
          let uu___ = f_binding_bv d bv in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun bv1 ->
                  let bv1 = Obj.magic bv1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic (mk (FStar_Syntax_Syntax.Pat_var bv1)))))
                 uu___1)
      | FStar_Syntax_Syntax.Pat_dot_term t ->
          let uu___ =
            FStar_Class_Monad.map_optM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (f_term d)) uu___1) (Obj.magic t) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic (mk (FStar_Syntax_Syntax.Pat_dot_term t1)))))
                 uu___1)
let on_sub_br :
  'm .
    'm lvm ->
      (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
        FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) -> 
        'm
  =
  fun d ->
    fun br ->
      let uu___ = br in
      match uu___ with
      | (pat, wopt, body) ->
          let uu___1 = on_sub_pat d pat in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___1
            (fun uu___2 ->
               (fun pat1 ->
                  let pat1 = Obj.magic pat1 in
                  let uu___2 =
                    FStar_Class_Monad.map_optM (_lvm_monad d) () ()
                      (fun uu___3 -> (Obj.magic (f_term d)) uu___3)
                      (Obj.magic wopt) in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___2
                       (fun uu___3 ->
                          (fun wopt1 ->
                             let wopt1 = Obj.magic wopt1 in
                             let uu___3 = f_term d body in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang (_lvm_monad d)
                                  () () uu___3
                                  (fun uu___4 ->
                                     (fun body1 ->
                                        let body1 = Obj.magic body1 in
                                        Obj.magic
                                          (FStar_Class_Monad.return
                                             (_lvm_monad d) ()
                                             (Obj.magic (pat1, wopt1, body1))))
                                       uu___4))) uu___3))) uu___2)
let on_sub_comp_typ : 'm . 'm lvm -> FStar_Syntax_Syntax.comp_typ -> 'm =
  fun d ->
    fun ct ->
      let uu___ =
        FStar_Class_Monad.mapM (_lvm_monad d) () ()
          (fun uu___1 -> (Obj.magic (f_univ d)) uu___1)
          (Obj.magic ct.FStar_Syntax_Syntax.comp_univs) in
      FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
        (fun uu___1 ->
           (fun comp_univs ->
              let comp_univs = Obj.magic comp_univs in
              let effect_name = ct.FStar_Syntax_Syntax.effect_name in
              let uu___1 = f_term d ct.FStar_Syntax_Syntax.result_typ in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___1
                   (fun uu___2 ->
                      (fun result_typ ->
                         let result_typ = Obj.magic result_typ in
                         let uu___2 =
                           let uu___3 = f_arg d in
                           FStar_Class_Monad.mapM (_lvm_monad d) () ()
                             (fun uu___4 -> (Obj.magic uu___3) uu___4)
                             (Obj.magic ct.FStar_Syntax_Syntax.effect_args) in
                         Obj.magic
                           (FStar_Class_Monad.op_let_Bang (_lvm_monad d) ()
                              () uu___2
                              (fun uu___3 ->
                                 (fun effect_args ->
                                    let effect_args = Obj.magic effect_args in
                                    let flags = ct.FStar_Syntax_Syntax.flags in
                                    Obj.magic
                                      (FStar_Class_Monad.return
                                         (_lvm_monad d) ()
                                         (Obj.magic
                                            {
                                              FStar_Syntax_Syntax.comp_univs
                                                = comp_univs;
                                              FStar_Syntax_Syntax.effect_name
                                                = effect_name;
                                              FStar_Syntax_Syntax.result_typ
                                                = result_typ;
                                              FStar_Syntax_Syntax.effect_args
                                                = effect_args;
                                              FStar_Syntax_Syntax.flags =
                                                flags
                                            }))) uu___3))) uu___2))) uu___1)
let on_sub_comp :
  'm . 'm lvm -> FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax -> 'm =
  fun d ->
    fun c ->
      let uu___ =
        match c.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Total typ ->
            let uu___1 = f_term d typ in
            FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) () ()
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___2 = Obj.magic uu___2 in
                    Obj.magic (FStar_Syntax_Syntax.Total uu___2)) uu___2)
              uu___1
        | FStar_Syntax_Syntax.GTotal typ ->
            let uu___1 = f_term d typ in
            FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) () ()
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___2 = Obj.magic uu___2 in
                    Obj.magic (FStar_Syntax_Syntax.GTotal uu___2)) uu___2)
              uu___1
        | FStar_Syntax_Syntax.Comp ct ->
            let uu___1 = on_sub_comp_typ d ct in
            FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) () ()
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___2 = Obj.magic uu___2 in
                    Obj.magic (FStar_Syntax_Syntax.Comp uu___2)) uu___2)
              uu___1 in
      FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
        (fun uu___1 ->
           (fun cn ->
              let cn = Obj.magic cn in
              let uu___1 =
                FStar_Syntax_Syntax.mk cn c.FStar_Syntax_Syntax.pos in
              Obj.magic
                (FStar_Class_Monad.return (_lvm_monad d) ()
                   (Obj.magic uu___1))) uu___1)
let __on_decreases :
  'm .
    'm lvm ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'm) ->
        FStar_Syntax_Syntax.cflag -> 'm
  =
  fun d ->
    fun f ->
      fun uu___ ->
        match uu___ with
        | FStar_Syntax_Syntax.DECREASES (FStar_Syntax_Syntax.Decreases_lex l)
            ->
            let uu___1 =
              let uu___2 =
                FStar_Class_Monad.mapM (_lvm_monad d) () ()
                  (fun uu___3 -> (Obj.magic f) uu___3) (Obj.magic l) in
              FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) () ()
                (fun uu___3 ->
                   (fun uu___3 ->
                      let uu___3 = Obj.magic uu___3 in
                      Obj.magic (FStar_Syntax_Syntax.Decreases_lex uu___3))
                     uu___3) uu___2 in
            FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) () ()
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___2 = Obj.magic uu___2 in
                    Obj.magic (FStar_Syntax_Syntax.DECREASES uu___2)) uu___2)
              uu___1
        | FStar_Syntax_Syntax.DECREASES (FStar_Syntax_Syntax.Decreases_wf
            (r, t)) ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = f r in
                  FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) ()
                    ()
                    (fun uu___5 ->
                       (fun uu___5 ->
                          let uu___5 = Obj.magic uu___5 in
                          Obj.magic (fun uu___6 -> (uu___5, uu___6))) uu___5)
                    uu___4 in
                let uu___4 = f t in
                FStar_Class_Monad.op_Less_Star_Greater (_lvm_monad d) () ()
                  uu___3 uu___4 in
              FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) () ()
                (fun uu___3 ->
                   (fun uu___3 ->
                      let uu___3 = Obj.magic uu___3 in
                      Obj.magic (FStar_Syntax_Syntax.Decreases_wf uu___3))
                     uu___3) uu___2 in
            FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) () ()
              (fun uu___2 ->
                 (fun uu___2 ->
                    let uu___2 = Obj.magic uu___2 in
                    Obj.magic (FStar_Syntax_Syntax.DECREASES uu___2)) uu___2)
              uu___1
        | f1 -> FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic f1)
let on_sub_residual_comp :
  'm . 'm lvm -> FStar_Syntax_Syntax.residual_comp -> 'm =
  fun d ->
    fun rc ->
      let residual_effect = rc.FStar_Syntax_Syntax.residual_effect in
      let uu___ =
        FStar_Class_Monad.map_optM (_lvm_monad d) () ()
          (fun uu___1 -> (Obj.magic (f_term d)) uu___1)
          (Obj.magic rc.FStar_Syntax_Syntax.residual_typ) in
      FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
        (fun uu___1 ->
           (fun residual_typ ->
              let residual_typ = Obj.magic residual_typ in
              let uu___1 =
                let uu___2 = __on_decreases d (f_term d) in
                FStar_Class_Monad.mapM (_lvm_monad d) () ()
                  (fun uu___3 -> (Obj.magic uu___2) uu___3)
                  (Obj.magic rc.FStar_Syntax_Syntax.residual_flags) in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___1
                   (fun uu___2 ->
                      (fun residual_flags ->
                         let residual_flags = Obj.magic residual_flags in
                         Obj.magic
                           (FStar_Class_Monad.return (_lvm_monad d) ()
                              (Obj.magic
                                 {
                                   FStar_Syntax_Syntax.residual_effect =
                                     residual_effect;
                                   FStar_Syntax_Syntax.residual_typ =
                                     residual_typ;
                                   FStar_Syntax_Syntax.residual_flags =
                                     residual_flags
                                 }))) uu___2))) uu___1)
let on_sub_univ : 'm . 'm lvm -> FStar_Syntax_Syntax.universe -> 'm =
  fun d ->
    fun u ->
      let u1 = FStar_Syntax_Subst.compress_univ u in
      match u1 with
      | FStar_Syntax_Syntax.U_max us ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (f_univ d)) uu___1) (Obj.magic us) in
          FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) () ()
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  Obj.magic (FStar_Syntax_Syntax.U_max uu___1)) uu___1) uu___
      | FStar_Syntax_Syntax.U_succ u2 ->
          let uu___ = f_univ d u2 in
          FStar_Class_Monad.op_Less_Dollar_Greater (_lvm_monad d) () ()
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___1 = Obj.magic uu___1 in
                  Obj.magic (FStar_Syntax_Syntax.U_succ uu___1)) uu___1)
            uu___
      | FStar_Syntax_Syntax.U_zero ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic u1)
      | FStar_Syntax_Syntax.U_bvar uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic u1)
      | FStar_Syntax_Syntax.U_name uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic u1)
      | FStar_Syntax_Syntax.U_unknown ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic u1)
      | FStar_Syntax_Syntax.U_unif uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic u1)
let on_sub_wp_eff_combinators :
  'm . 'm lvm -> FStar_Syntax_Syntax.wp_eff_combinators -> 'm =
  fun d ->
    fun wpcs ->
      let uu___ =
        let uu___1 = f_tscheme d in uu___1 wpcs.FStar_Syntax_Syntax.ret_wp in
      FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
        (fun uu___1 ->
           (fun ret_wp ->
              let ret_wp = Obj.magic ret_wp in
              let uu___1 =
                let uu___2 = f_tscheme d in
                uu___2 wpcs.FStar_Syntax_Syntax.bind_wp in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___1
                   (fun uu___2 ->
                      (fun bind_wp ->
                         let bind_wp = Obj.magic bind_wp in
                         let uu___2 =
                           let uu___3 = f_tscheme d in
                           uu___3 wpcs.FStar_Syntax_Syntax.stronger in
                         Obj.magic
                           (FStar_Class_Monad.op_let_Bang (_lvm_monad d) ()
                              () uu___2
                              (fun uu___3 ->
                                 (fun stronger ->
                                    let stronger = Obj.magic stronger in
                                    let uu___3 =
                                      let uu___4 = f_tscheme d in
                                      uu___4
                                        wpcs.FStar_Syntax_Syntax.if_then_else in
                                    Obj.magic
                                      (FStar_Class_Monad.op_let_Bang
                                         (_lvm_monad d) () () uu___3
                                         (fun uu___4 ->
                                            (fun if_then_else ->
                                               let if_then_else =
                                                 Obj.magic if_then_else in
                                               let uu___4 =
                                                 let uu___5 = f_tscheme d in
                                                 uu___5
                                                   wpcs.FStar_Syntax_Syntax.ite_wp in
                                               Obj.magic
                                                 (FStar_Class_Monad.op_let_Bang
                                                    (_lvm_monad d) () ()
                                                    uu___4
                                                    (fun uu___5 ->
                                                       (fun ite_wp ->
                                                          let ite_wp =
                                                            Obj.magic ite_wp in
                                                          let uu___5 =
                                                            let uu___6 =
                                                              f_tscheme d in
                                                            uu___6
                                                              wpcs.FStar_Syntax_Syntax.close_wp in
                                                          Obj.magic
                                                            (FStar_Class_Monad.op_let_Bang
                                                               (_lvm_monad d)
                                                               () () uu___5
                                                               (fun uu___6 ->
                                                                  (fun
                                                                    close_wp
                                                                    ->
                                                                    let close_wp
                                                                    =
                                                                    Obj.magic
                                                                    close_wp in
                                                                    let uu___6
                                                                    =
                                                                    let uu___7
                                                                    =
                                                                    f_tscheme
                                                                    d in
                                                                    uu___7
                                                                    wpcs.FStar_Syntax_Syntax.trivial in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    (_lvm_monad
                                                                    d) () ()
                                                                    uu___6
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    trivial
                                                                    ->
                                                                    let trivial
                                                                    =
                                                                    Obj.magic
                                                                    trivial in
                                                                    let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    f_tscheme
                                                                    d in
                                                                    FStar_Class_Monad.map_optM
                                                                    (_lvm_monad
                                                                    d) () ()
                                                                    (fun
                                                                    uu___9 ->
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    uu___9)
                                                                    (Obj.magic
                                                                    wpcs.FStar_Syntax_Syntax.repr) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    (_lvm_monad
                                                                    d) () ()
                                                                    uu___7
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun repr
                                                                    ->
                                                                    let repr
                                                                    =
                                                                    Obj.magic
                                                                    repr in
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    f_tscheme
                                                                    d in
                                                                    FStar_Class_Monad.map_optM
                                                                    (_lvm_monad
                                                                    d) () ()
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    uu___10)
                                                                    (Obj.magic
                                                                    wpcs.FStar_Syntax_Syntax.return_repr) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    (_lvm_monad
                                                                    d) () ()
                                                                    uu___8
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    return_repr
                                                                    ->
                                                                    let return_repr
                                                                    =
                                                                    Obj.magic
                                                                    return_repr in
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    f_tscheme
                                                                    d in
                                                                    FStar_Class_Monad.map_optM
                                                                    (_lvm_monad
                                                                    d) () ()
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    uu___11)
                                                                    (Obj.magic
                                                                    wpcs.FStar_Syntax_Syntax.bind_repr) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    (_lvm_monad
                                                                    d) () ()
                                                                    uu___9
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    bind_repr
                                                                    ->
                                                                    let bind_repr
                                                                    =
                                                                    Obj.magic
                                                                    bind_repr in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    (_lvm_monad
                                                                    d) ()
                                                                    (Obj.magic
                                                                    {
                                                                    FStar_Syntax_Syntax.ret_wp
                                                                    = ret_wp;
                                                                    FStar_Syntax_Syntax.bind_wp
                                                                    = bind_wp;
                                                                    FStar_Syntax_Syntax.stronger
                                                                    =
                                                                    stronger;
                                                                    FStar_Syntax_Syntax.if_then_else
                                                                    =
                                                                    if_then_else;
                                                                    FStar_Syntax_Syntax.ite_wp
                                                                    = ite_wp;
                                                                    FStar_Syntax_Syntax.close_wp
                                                                    =
                                                                    close_wp;
                                                                    FStar_Syntax_Syntax.trivial
                                                                    = trivial;
                                                                    FStar_Syntax_Syntax.repr
                                                                    = repr;
                                                                    FStar_Syntax_Syntax.return_repr
                                                                    =
                                                                    return_repr;
                                                                    FStar_Syntax_Syntax.bind_repr
                                                                    =
                                                                    bind_repr
                                                                    })))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                         uu___5))) uu___4)))
                                   uu___3))) uu___2))) uu___1)
let mapTuple2 :
  'a 'b 'c 'd 'm .
    'm FStar_Class_Monad.monad -> ('a -> 'm) -> ('c -> 'm) -> ('a * 'c) -> 'm
  =
  fun uu___ ->
    fun f ->
      fun g ->
        fun t ->
          let uu___1 =
            let uu___2 =
              f (FStar_Pervasives_Native.__proj__Mktuple2__item___1 t) in
            FStar_Class_Monad.op_Less_Dollar_Greater uu___ () ()
              (fun uu___3 ->
                 (fun uu___3 ->
                    let uu___3 = Obj.magic uu___3 in
                    Obj.magic (fun uu___4 -> (uu___3, uu___4))) uu___3)
              uu___2 in
          let uu___2 =
            g (FStar_Pervasives_Native.__proj__Mktuple2__item___2 t) in
          FStar_Class_Monad.op_Less_Star_Greater uu___ () () uu___1 uu___2
let mapTuple3 :
  'a 'b 'c 'd 'e 'f 'm .
    'm FStar_Class_Monad.monad ->
      ('a -> 'm) -> ('c -> 'm) -> ('e -> 'm) -> ('a * 'c * 'e) -> 'm
  =
  fun uu___ ->
    fun f1 ->
      fun g ->
        fun h ->
          fun t ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  f1 (FStar_Pervasives_Native.__proj__Mktuple3__item___1 t) in
                FStar_Class_Monad.op_Less_Dollar_Greater uu___ () ()
                  (fun uu___4 ->
                     (fun uu___4 ->
                        let uu___4 = Obj.magic uu___4 in
                        Obj.magic
                          (fun uu___5 ->
                             fun uu___6 -> (uu___4, uu___5, uu___6))) uu___4)
                  uu___3 in
              let uu___3 =
                g (FStar_Pervasives_Native.__proj__Mktuple3__item___2 t) in
              FStar_Class_Monad.op_Less_Star_Greater uu___ () () uu___2
                uu___3 in
            let uu___2 =
              h (FStar_Pervasives_Native.__proj__Mktuple3__item___3 t) in
            FStar_Class_Monad.op_Less_Star_Greater uu___ () () uu___1 uu___2
let on_sub_layered_eff_combinators :
  'm . 'm lvm -> FStar_Syntax_Syntax.layered_eff_combinators -> 'm =
  fun d ->
    fun lecs ->
      let uu___ =
        let uu___1 = f_tscheme d in
        let uu___2 = f_tscheme d in
        mapTuple2 (_lvm_monad d) uu___1 uu___2
          lecs.FStar_Syntax_Syntax.l_repr in
      FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
        (fun uu___1 ->
           (fun l_repr ->
              let l_repr = Obj.magic l_repr in
              let uu___1 =
                let uu___2 = f_tscheme d in
                let uu___3 = f_tscheme d in
                mapTuple2 (_lvm_monad d) uu___2 uu___3
                  lecs.FStar_Syntax_Syntax.l_return in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___1
                   (fun uu___2 ->
                      (fun l_return ->
                         let l_return = Obj.magic l_return in
                         let uu___2 =
                           let uu___3 = f_tscheme d in
                           let uu___4 = f_tscheme d in
                           mapTuple3 (_lvm_monad d) uu___3 uu___4
                             (fun uu___5 ->
                                (Obj.magic
                                   (FStar_Class_Monad.return (_lvm_monad d)
                                      ())) uu___5)
                             lecs.FStar_Syntax_Syntax.l_bind in
                         Obj.magic
                           (FStar_Class_Monad.op_let_Bang (_lvm_monad d) ()
                              () uu___2
                              (fun uu___3 ->
                                 (fun l_bind ->
                                    let l_bind = Obj.magic l_bind in
                                    let uu___3 =
                                      let uu___4 = f_tscheme d in
                                      let uu___5 = f_tscheme d in
                                      mapTuple3 (_lvm_monad d) uu___4 uu___5
                                        (fun uu___6 ->
                                           (Obj.magic
                                              (FStar_Class_Monad.return
                                                 (_lvm_monad d) ())) uu___6)
                                        lecs.FStar_Syntax_Syntax.l_subcomp in
                                    Obj.magic
                                      (FStar_Class_Monad.op_let_Bang
                                         (_lvm_monad d) () () uu___3
                                         (fun uu___4 ->
                                            (fun l_subcomp ->
                                               let l_subcomp =
                                                 Obj.magic l_subcomp in
                                               let uu___4 =
                                                 let uu___5 = f_tscheme d in
                                                 let uu___6 = f_tscheme d in
                                                 mapTuple3 (_lvm_monad d)
                                                   uu___5 uu___6
                                                   (fun uu___7 ->
                                                      (Obj.magic
                                                         (FStar_Class_Monad.return
                                                            (_lvm_monad d) ()))
                                                        uu___7)
                                                   lecs.FStar_Syntax_Syntax.l_if_then_else in
                                               Obj.magic
                                                 (FStar_Class_Monad.op_let_Bang
                                                    (_lvm_monad d) () ()
                                                    uu___4
                                                    (fun uu___5 ->
                                                       (fun l_if_then_else ->
                                                          let l_if_then_else
                                                            =
                                                            Obj.magic
                                                              l_if_then_else in
                                                          let uu___5 =
                                                            let uu___6 =
                                                              let uu___7 =
                                                                f_tscheme d in
                                                              let uu___8 =
                                                                f_tscheme d in
                                                              mapTuple2
                                                                (_lvm_monad d)
                                                                uu___7 uu___8 in
                                                            FStar_Class_Monad.map_optM
                                                              (_lvm_monad d)
                                                              () ()
                                                              (fun uu___7 ->
                                                                 (Obj.magic
                                                                    uu___6)
                                                                   uu___7)
                                                              (Obj.magic
                                                                 lecs.FStar_Syntax_Syntax.l_close) in
                                                          Obj.magic
                                                            (FStar_Class_Monad.op_let_Bang
                                                               (_lvm_monad d)
                                                               () () uu___5
                                                               (fun uu___6 ->
                                                                  (fun
                                                                    l_close
                                                                    ->
                                                                    let l_close
                                                                    =
                                                                    Obj.magic
                                                                    l_close in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    (_lvm_monad
                                                                    d) ()
                                                                    (Obj.magic
                                                                    {
                                                                    FStar_Syntax_Syntax.l_repr
                                                                    = l_repr;
                                                                    FStar_Syntax_Syntax.l_return
                                                                    =
                                                                    l_return;
                                                                    FStar_Syntax_Syntax.l_bind
                                                                    = l_bind;
                                                                    FStar_Syntax_Syntax.l_subcomp
                                                                    =
                                                                    l_subcomp;
                                                                    FStar_Syntax_Syntax.l_if_then_else
                                                                    =
                                                                    l_if_then_else;
                                                                    FStar_Syntax_Syntax.l_close
                                                                    = l_close
                                                                    })))
                                                                    uu___6)))
                                                         uu___5))) uu___4)))
                                   uu___3))) uu___2))) uu___1)
let on_sub_combinators :
  'm . 'm lvm -> FStar_Syntax_Syntax.eff_combinators -> 'm =
  fun d ->
    fun cbs ->
      match cbs with
      | FStar_Syntax_Syntax.Primitive_eff wpcs ->
          let uu___ = on_sub_wp_eff_combinators d wpcs in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun wpcs1 ->
                  let wpcs1 = Obj.magic wpcs1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic (FStar_Syntax_Syntax.Primitive_eff wpcs1))))
                 uu___1)
      | FStar_Syntax_Syntax.DM4F_eff wpcs ->
          let uu___ = on_sub_wp_eff_combinators d wpcs in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun wpcs1 ->
                  let wpcs1 = Obj.magic wpcs1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic (FStar_Syntax_Syntax.DM4F_eff wpcs1))))
                 uu___1)
      | FStar_Syntax_Syntax.Layered_eff lecs ->
          let uu___ = on_sub_layered_eff_combinators d lecs in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun lecs1 ->
                  let lecs1 = Obj.magic lecs1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic (FStar_Syntax_Syntax.Layered_eff lecs1))))
                 uu___1)
let on_sub_effect_signature :
  'm . 'm lvm -> FStar_Syntax_Syntax.effect_signature -> 'm =
  fun d ->
    fun es ->
      match es with
      | FStar_Syntax_Syntax.Layered_eff_sig (n, (us, t)) ->
          let uu___ = f_term d t in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Layered_eff_sig (n, (us, t1))))))
                 uu___1)
      | FStar_Syntax_Syntax.WP_eff_sig (us, t) ->
          let uu___ = f_term d t in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic (FStar_Syntax_Syntax.WP_eff_sig (us, t1)))))
                 uu___1)
let on_sub_action : 'm . 'm lvm -> FStar_Syntax_Syntax.action -> 'm =
  fun d ->
    fun a ->
      let action_name = a.FStar_Syntax_Syntax.action_name in
      let action_unqualified_name =
        a.FStar_Syntax_Syntax.action_unqualified_name in
      let action_univs = a.FStar_Syntax_Syntax.action_univs in
      let uu___ =
        FStar_Class_Monad.mapM (_lvm_monad d) () ()
          (fun uu___1 -> (Obj.magic (f_binder d)) uu___1)
          (Obj.magic a.FStar_Syntax_Syntax.action_params) in
      FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
        (fun uu___1 ->
           (fun action_params ->
              let action_params = Obj.magic action_params in
              let uu___1 = f_term d a.FStar_Syntax_Syntax.action_defn in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___1
                   (fun uu___2 ->
                      (fun action_defn ->
                         let action_defn = Obj.magic action_defn in
                         let uu___2 =
                           f_term d a.FStar_Syntax_Syntax.action_typ in
                         Obj.magic
                           (FStar_Class_Monad.op_let_Bang (_lvm_monad d) ()
                              () uu___2
                              (fun uu___3 ->
                                 (fun action_typ ->
                                    let action_typ = Obj.magic action_typ in
                                    Obj.magic
                                      (FStar_Class_Monad.return
                                         (_lvm_monad d) ()
                                         (Obj.magic
                                            {
                                              FStar_Syntax_Syntax.action_name
                                                = action_name;
                                              FStar_Syntax_Syntax.action_unqualified_name
                                                = action_unqualified_name;
                                              FStar_Syntax_Syntax.action_univs
                                                = action_univs;
                                              FStar_Syntax_Syntax.action_params
                                                = action_params;
                                              FStar_Syntax_Syntax.action_defn
                                                = action_defn;
                                              FStar_Syntax_Syntax.action_typ
                                                = action_typ
                                            }))) uu___3))) uu___2))) uu___1)
let rec on_sub_sigelt' : 'm . 'm lvm -> FStar_Syntax_Syntax.sigelt' -> 'm =
  fun d ->
    fun se ->
      match se with
      | FStar_Syntax_Syntax.Sig_inductive_typ
          { FStar_Syntax_Syntax.lid = lid; FStar_Syntax_Syntax.us = us;
            FStar_Syntax_Syntax.params = params;
            FStar_Syntax_Syntax.num_uniform_params = num_uniform_params;
            FStar_Syntax_Syntax.t = t; FStar_Syntax_Syntax.mutuals = mutuals;
            FStar_Syntax_Syntax.ds = ds;
            FStar_Syntax_Syntax.injective_type_params = injective_type_params;_}
          ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (f_binder d)) uu___1)
              (Obj.magic params) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun params1 ->
                  let params1 = Obj.magic params1 in
                  let uu___1 = f_term d t in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun t1 ->
                             let t1 = Obj.magic t1 in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic
                                     (FStar_Syntax_Syntax.Sig_inductive_typ
                                        {
                                          FStar_Syntax_Syntax.lid = lid;
                                          FStar_Syntax_Syntax.us = us;
                                          FStar_Syntax_Syntax.params =
                                            params1;
                                          FStar_Syntax_Syntax.num_uniform_params
                                            = num_uniform_params;
                                          FStar_Syntax_Syntax.t = t1;
                                          FStar_Syntax_Syntax.mutuals =
                                            mutuals;
                                          FStar_Syntax_Syntax.ds = ds;
                                          FStar_Syntax_Syntax.injective_type_params
                                            = injective_type_params
                                        })))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Sig_bundle
          { FStar_Syntax_Syntax.ses = ses; FStar_Syntax_Syntax.lids = lids;_}
          ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (on_sub_sigelt d)) uu___1)
              (Obj.magic ses) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun ses1 ->
                  let ses1 = Obj.magic ses1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Sig_bundle
                             {
                               FStar_Syntax_Syntax.ses = ses1;
                               FStar_Syntax_Syntax.lids = lids
                             })))) uu___1)
      | FStar_Syntax_Syntax.Sig_datacon
          { FStar_Syntax_Syntax.lid1 = lid; FStar_Syntax_Syntax.us1 = us;
            FStar_Syntax_Syntax.t1 = t; FStar_Syntax_Syntax.ty_lid = ty_lid;
            FStar_Syntax_Syntax.num_ty_params = num_ty_params;
            FStar_Syntax_Syntax.mutuals1 = mutuals;
            FStar_Syntax_Syntax.injective_type_params1 =
              injective_type_params;_}
          ->
          let uu___ = f_term d t in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Sig_datacon
                             {
                               FStar_Syntax_Syntax.lid1 = lid;
                               FStar_Syntax_Syntax.us1 = us;
                               FStar_Syntax_Syntax.t1 = t1;
                               FStar_Syntax_Syntax.ty_lid = ty_lid;
                               FStar_Syntax_Syntax.num_ty_params =
                                 num_ty_params;
                               FStar_Syntax_Syntax.mutuals1 = mutuals;
                               FStar_Syntax_Syntax.injective_type_params1 =
                                 injective_type_params
                             })))) uu___1)
      | FStar_Syntax_Syntax.Sig_declare_typ
          { FStar_Syntax_Syntax.lid2 = lid; FStar_Syntax_Syntax.us2 = us;
            FStar_Syntax_Syntax.t2 = t;_}
          ->
          let uu___ = f_term d t in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Sig_declare_typ
                             {
                               FStar_Syntax_Syntax.lid2 = lid;
                               FStar_Syntax_Syntax.us2 = us;
                               FStar_Syntax_Syntax.t2 = t1
                             })))) uu___1)
      | FStar_Syntax_Syntax.Sig_let
          { FStar_Syntax_Syntax.lbs1 = (is_rec, lbs);
            FStar_Syntax_Syntax.lids1 = lids;_}
          ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (on_sub_letbinding d)) uu___1)
              (Obj.magic lbs) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun lbs1 ->
                  let lbs1 = Obj.magic lbs1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Sig_let
                             {
                               FStar_Syntax_Syntax.lbs1 = (is_rec, lbs1);
                               FStar_Syntax_Syntax.lids1 = lids
                             })))) uu___1)
      | FStar_Syntax_Syntax.Sig_assume
          { FStar_Syntax_Syntax.lid3 = lid; FStar_Syntax_Syntax.us3 = us;
            FStar_Syntax_Syntax.phi1 = phi;_}
          ->
          let uu___ = f_term d phi in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun phi1 ->
                  let phi1 = Obj.magic phi1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Sig_assume
                             {
                               FStar_Syntax_Syntax.lid3 = lid;
                               FStar_Syntax_Syntax.us3 = us;
                               FStar_Syntax_Syntax.phi1 = phi1
                             })))) uu___1)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let mname = ed.FStar_Syntax_Syntax.mname in
          let cattributes = ed.FStar_Syntax_Syntax.cattributes in
          let univs = ed.FStar_Syntax_Syntax.univs in
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (f_binder d)) uu___1)
              (Obj.magic ed.FStar_Syntax_Syntax.binders) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun binders ->
                  let binders = Obj.magic binders in
                  let uu___1 =
                    on_sub_effect_signature d
                      ed.FStar_Syntax_Syntax.signature in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun signature ->
                             let signature = Obj.magic signature in
                             let uu___2 =
                               on_sub_combinators d
                                 ed.FStar_Syntax_Syntax.combinators in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang (_lvm_monad d)
                                  () () uu___2
                                  (fun uu___3 ->
                                     (fun combinators ->
                                        let combinators =
                                          Obj.magic combinators in
                                        let uu___3 =
                                          FStar_Class_Monad.mapM
                                            (_lvm_monad d) () ()
                                            (fun uu___4 ->
                                               (Obj.magic (on_sub_action d))
                                                 uu___4)
                                            (Obj.magic
                                               ed.FStar_Syntax_Syntax.actions) in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             (_lvm_monad d) () () uu___3
                                             (fun uu___4 ->
                                                (fun actions ->
                                                   let actions =
                                                     Obj.magic actions in
                                                   let uu___4 =
                                                     FStar_Class_Monad.mapM
                                                       (_lvm_monad d) () ()
                                                       (fun uu___5 ->
                                                          (Obj.magic
                                                             (f_term d))
                                                            uu___5)
                                                       (Obj.magic
                                                          ed.FStar_Syntax_Syntax.eff_attrs) in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        (_lvm_monad d) () ()
                                                        uu___4
                                                        (fun uu___5 ->
                                                           (fun eff_attrs ->
                                                              let eff_attrs =
                                                                Obj.magic
                                                                  eff_attrs in
                                                              let extraction_mode
                                                                =
                                                                ed.FStar_Syntax_Syntax.extraction_mode in
                                                              let ed1 =
                                                                {
                                                                  FStar_Syntax_Syntax.mname
                                                                    = mname;
                                                                  FStar_Syntax_Syntax.cattributes
                                                                    =
                                                                    cattributes;
                                                                  FStar_Syntax_Syntax.univs
                                                                    = univs;
                                                                  FStar_Syntax_Syntax.binders
                                                                    = binders;
                                                                  FStar_Syntax_Syntax.signature
                                                                    =
                                                                    signature;
                                                                  FStar_Syntax_Syntax.combinators
                                                                    =
                                                                    combinators;
                                                                  FStar_Syntax_Syntax.actions
                                                                    = actions;
                                                                  FStar_Syntax_Syntax.eff_attrs
                                                                    =
                                                                    eff_attrs;
                                                                  FStar_Syntax_Syntax.extraction_mode
                                                                    =
                                                                    extraction_mode
                                                                } in
                                                              Obj.magic
                                                                (FStar_Class_Monad.return
                                                                   (_lvm_monad
                                                                    d) ()
                                                                   (Obj.magic
                                                                    (FStar_Syntax_Syntax.Sig_new_effect
                                                                    ed1))))
                                                             uu___5))) uu___4)))
                                       uu___3))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Sig_sub_effect se1 ->
          let source = se1.FStar_Syntax_Syntax.source in
          let target = se1.FStar_Syntax_Syntax.target in
          let uu___ =
            let uu___1 = f_tscheme d in
            FStar_Class_Monad.map_optM (_lvm_monad d) () ()
              (fun uu___2 -> (Obj.magic uu___1) uu___2)
              (Obj.magic se1.FStar_Syntax_Syntax.lift_wp) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun lift_wp ->
                  let lift_wp = Obj.magic lift_wp in
                  let uu___1 =
                    let uu___2 = f_tscheme d in
                    FStar_Class_Monad.map_optM (_lvm_monad d) () ()
                      (fun uu___3 -> (Obj.magic uu___2) uu___3)
                      (Obj.magic se1.FStar_Syntax_Syntax.lift) in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun lift ->
                             let lift = Obj.magic lift in
                             let kind = se1.FStar_Syntax_Syntax.kind in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic
                                     (FStar_Syntax_Syntax.Sig_sub_effect
                                        {
                                          FStar_Syntax_Syntax.source = source;
                                          FStar_Syntax_Syntax.target = target;
                                          FStar_Syntax_Syntax.lift_wp =
                                            lift_wp;
                                          FStar_Syntax_Syntax.lift = lift;
                                          FStar_Syntax_Syntax.kind = kind
                                        })))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Sig_effect_abbrev
          { FStar_Syntax_Syntax.lid4 = lid; FStar_Syntax_Syntax.us4 = us;
            FStar_Syntax_Syntax.bs2 = bs; FStar_Syntax_Syntax.comp1 = comp;
            FStar_Syntax_Syntax.cflags = cflags;_}
          ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (f_binder d)) uu___1) (Obj.magic bs) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun binders ->
                  let binders = Obj.magic binders in
                  let uu___1 = f_comp d comp in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun comp1 ->
                             let comp1 = Obj.magic comp1 in
                             let uu___2 =
                               let uu___3 = __on_decreases d (f_term d) in
                               FStar_Class_Monad.mapM (_lvm_monad d) () ()
                                 (fun uu___4 -> (Obj.magic uu___3) uu___4)
                                 (Obj.magic cflags) in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang (_lvm_monad d)
                                  () () uu___2
                                  (fun uu___3 ->
                                     (fun cflags1 ->
                                        let cflags1 = Obj.magic cflags1 in
                                        Obj.magic
                                          (FStar_Class_Monad.return
                                             (_lvm_monad d) ()
                                             (Obj.magic
                                                (FStar_Syntax_Syntax.Sig_effect_abbrev
                                                   {
                                                     FStar_Syntax_Syntax.lid4
                                                       = lid;
                                                     FStar_Syntax_Syntax.us4
                                                       = us;
                                                     FStar_Syntax_Syntax.bs2
                                                       = bs;
                                                     FStar_Syntax_Syntax.comp1
                                                       = comp1;
                                                     FStar_Syntax_Syntax.cflags
                                                       = cflags1
                                                   })))) uu___3))) uu___2)))
                 uu___1)
      | FStar_Syntax_Syntax.Sig_pragma uu___ ->
          FStar_Class_Monad.return (_lvm_monad d) () (Obj.magic se)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind
          { FStar_Syntax_Syntax.m_lid = m_lid;
            FStar_Syntax_Syntax.n_lid = n_lid;
            FStar_Syntax_Syntax.p_lid = p_lid; FStar_Syntax_Syntax.tm3 = tm;
            FStar_Syntax_Syntax.typ = typ;
            FStar_Syntax_Syntax.kind1 = kind;_}
          ->
          let uu___ = let uu___1 = f_tscheme d in uu___1 tm in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun tm1 ->
                  let tm1 = Obj.magic tm1 in
                  let uu___1 = let uu___2 = f_tscheme d in uu___2 typ in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun typ1 ->
                             let typ1 = Obj.magic typ1 in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic
                                     (FStar_Syntax_Syntax.Sig_polymonadic_bind
                                        {
                                          FStar_Syntax_Syntax.m_lid = m_lid;
                                          FStar_Syntax_Syntax.n_lid = n_lid;
                                          FStar_Syntax_Syntax.p_lid = p_lid;
                                          FStar_Syntax_Syntax.tm3 = tm1;
                                          FStar_Syntax_Syntax.typ = typ1;
                                          FStar_Syntax_Syntax.kind1 = kind
                                        })))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp
          { FStar_Syntax_Syntax.m_lid1 = m_lid;
            FStar_Syntax_Syntax.n_lid1 = n_lid; FStar_Syntax_Syntax.tm4 = tm;
            FStar_Syntax_Syntax.typ1 = typ;
            FStar_Syntax_Syntax.kind2 = kind;_}
          ->
          let uu___ = let uu___1 = f_tscheme d in uu___1 tm in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun tm1 ->
                  let tm1 = Obj.magic tm1 in
                  let uu___1 = let uu___2 = f_tscheme d in uu___2 typ in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () ()
                       uu___1
                       (fun uu___2 ->
                          (fun typ1 ->
                             let typ1 = Obj.magic typ1 in
                             Obj.magic
                               (FStar_Class_Monad.return (_lvm_monad d) ()
                                  (Obj.magic
                                     (FStar_Syntax_Syntax.Sig_polymonadic_subcomp
                                        {
                                          FStar_Syntax_Syntax.m_lid1 = m_lid;
                                          FStar_Syntax_Syntax.n_lid1 = n_lid;
                                          FStar_Syntax_Syntax.tm4 = tm1;
                                          FStar_Syntax_Syntax.typ1 = typ1;
                                          FStar_Syntax_Syntax.kind2 = kind
                                        })))) uu___2))) uu___1)
      | FStar_Syntax_Syntax.Sig_fail
          { FStar_Syntax_Syntax.errs = errs;
            FStar_Syntax_Syntax.fail_in_lax = fail_in_lax;
            FStar_Syntax_Syntax.ses1 = ses;_}
          ->
          let uu___ =
            FStar_Class_Monad.mapM (_lvm_monad d) () ()
              (fun uu___1 -> (Obj.magic (on_sub_sigelt d)) uu___1)
              (Obj.magic ses) in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun ses1 ->
                  let ses1 = Obj.magic ses1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Sig_fail
                             {
                               FStar_Syntax_Syntax.errs = errs;
                               FStar_Syntax_Syntax.fail_in_lax = fail_in_lax;
                               FStar_Syntax_Syntax.ses1 = ses1
                             })))) uu___1)
      | FStar_Syntax_Syntax.Sig_splice
          { FStar_Syntax_Syntax.is_typed = is_typed;
            FStar_Syntax_Syntax.lids2 = lids;
            FStar_Syntax_Syntax.tac = tac;_}
          ->
          let uu___ = f_term d tac in
          FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
            (fun uu___1 ->
               (fun tac1 ->
                  let tac1 = Obj.magic tac1 in
                  Obj.magic
                    (FStar_Class_Monad.return (_lvm_monad d) ()
                       (Obj.magic
                          (FStar_Syntax_Syntax.Sig_splice
                             {
                               FStar_Syntax_Syntax.is_typed = is_typed;
                               FStar_Syntax_Syntax.lids2 = lids;
                               FStar_Syntax_Syntax.tac = tac1
                             })))) uu___1)
      | uu___ -> FStar_Compiler_Effect.failwith "on_sub_sigelt: missing case"
and on_sub_sigelt : 'm . 'm lvm -> FStar_Syntax_Syntax.sigelt -> 'm =
  fun d ->
    fun se ->
      let uu___ = on_sub_sigelt' d se.FStar_Syntax_Syntax.sigel in
      FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___
        (fun uu___1 ->
           (fun sigel ->
              let sigel = Obj.magic sigel in
              let sigrng = se.FStar_Syntax_Syntax.sigrng in
              let sigquals = se.FStar_Syntax_Syntax.sigquals in
              let sigmeta = se.FStar_Syntax_Syntax.sigmeta in
              let uu___1 =
                FStar_Class_Monad.mapM (_lvm_monad d) () ()
                  (fun uu___2 -> (Obj.magic (f_term d)) uu___2)
                  (Obj.magic se.FStar_Syntax_Syntax.sigattrs) in
              Obj.magic
                (FStar_Class_Monad.op_let_Bang (_lvm_monad d) () () uu___1
                   (fun uu___2 ->
                      (fun sigattrs ->
                         let sigattrs = Obj.magic sigattrs in
                         let sigopts = se.FStar_Syntax_Syntax.sigopts in
                         let sigopens_and_abbrevs =
                           se.FStar_Syntax_Syntax.sigopens_and_abbrevs in
                         Obj.magic
                           (FStar_Class_Monad.return (_lvm_monad d) ()
                              (Obj.magic
                                 {
                                   FStar_Syntax_Syntax.sigel = sigel;
                                   FStar_Syntax_Syntax.sigrng = sigrng;
                                   FStar_Syntax_Syntax.sigquals = sigquals;
                                   FStar_Syntax_Syntax.sigmeta = sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = sigattrs;
                                   FStar_Syntax_Syntax.sigopens_and_abbrevs =
                                     sigopens_and_abbrevs;
                                   FStar_Syntax_Syntax.sigopts = sigopts
                                 }))) uu___2))) uu___1)
let op_Greater_Greater_Equals :
  'm .
    'm FStar_Class_Monad.monad -> unit -> unit -> 'm -> (Obj.t -> 'm) -> 'm
  =
  fun uu___ ->
    fun a ->
      fun b ->
        fun c ->
          fun f -> FStar_Class_Monad.op_let_Bang uu___ () () c (fun x -> f x)
let op_Less_Less_Bar :
  'm .
    'm FStar_Class_Monad.monad -> unit -> unit -> (Obj.t -> 'm) -> 'm -> 'm
  =
  fun uu___ ->
    fun a ->
      fun b ->
        fun f ->
          fun c -> FStar_Class_Monad.op_let_Bang uu___ () () c (fun x -> f x)
let tie_bu : 'm . 'm FStar_Class_Monad.monad -> 'm lvm -> 'm lvm =
  fun md ->
    fun d ->
      let r = let uu___ = novfs md in FStar_Compiler_Util.mk_ref uu___ in
      (let uu___1 =
         let uu___2 =
           let uu___3 = FStar_Compiler_Effect.op_Bang r in uu___3.lvm_monad in
         {
           lvm_monad = uu___2;
           f_term =
             (fun x ->
                let uu___3 =
                  let uu___4 = FStar_Compiler_Effect.op_Bang r in
                  on_sub_term uu___4 x in
                op_Less_Less_Bar md () ()
                  (fun uu___4 -> (Obj.magic (f_term d)) uu___4) uu___3);
           f_binder =
             (fun x ->
                let uu___3 =
                  let uu___4 = FStar_Compiler_Effect.op_Bang r in
                  on_sub_binder uu___4 x in
                op_Less_Less_Bar md () ()
                  (fun uu___4 -> (Obj.magic (f_binder d)) uu___4) uu___3);
           f_binding_bv =
             (fun x ->
                let uu___3 =
                  let uu___4 = FStar_Compiler_Effect.op_Bang r in
                  on_sub_binding_bv uu___4 x in
                op_Less_Less_Bar md () ()
                  (fun uu___4 -> (Obj.magic (f_binding_bv d)) uu___4) uu___3);
           f_br =
             (fun x ->
                let uu___3 =
                  let uu___4 = FStar_Compiler_Effect.op_Bang r in
                  on_sub_br uu___4 x in
                op_Less_Less_Bar md () ()
                  (fun uu___4 -> (Obj.magic (f_br d)) uu___4) uu___3);
           f_comp =
             (fun x ->
                let uu___3 =
                  let uu___4 = FStar_Compiler_Effect.op_Bang r in
                  on_sub_comp uu___4 x in
                op_Less_Less_Bar md () ()
                  (fun uu___4 -> (Obj.magic (f_comp d)) uu___4) uu___3);
           f_residual_comp =
             (fun x ->
                let uu___3 =
                  let uu___4 = FStar_Compiler_Effect.op_Bang r in
                  on_sub_residual_comp uu___4 x in
                op_Less_Less_Bar md () ()
                  (fun uu___4 -> (Obj.magic (f_residual_comp d)) uu___4)
                  uu___3);
           f_univ =
             (fun x ->
                let uu___3 =
                  let uu___4 = FStar_Compiler_Effect.op_Bang r in
                  on_sub_univ uu___4 x in
                op_Less_Less_Bar md () ()
                  (fun uu___4 -> (Obj.magic (f_univ d)) uu___4) uu___3)
         } in
       FStar_Compiler_Effect.op_Colon_Equals r uu___1);
      FStar_Compiler_Effect.op_Bang r
let visitM_term_univs :
  'm .
    'm FStar_Class_Monad.monad ->
      (FStar_Syntax_Syntax.term -> 'm) ->
        (FStar_Syntax_Syntax.universe -> 'm) ->
          FStar_Syntax_Syntax.term -> 'm
  =
  fun md ->
    fun vt ->
      fun vu ->
        fun tm ->
          let dict =
            let uu___ =
              let uu___1 = novfs md in
              {
                lvm_monad = (uu___1.lvm_monad);
                f_term = vt;
                f_binder = (uu___1.f_binder);
                f_binding_bv = (uu___1.f_binding_bv);
                f_br = (uu___1.f_br);
                f_comp = (uu___1.f_comp);
                f_residual_comp = (uu___1.f_residual_comp);
                f_univ = vu
              } in
            tie_bu md uu___ in
          f_term dict tm
let visitM_term :
  'm .
    'm FStar_Class_Monad.monad ->
      (FStar_Syntax_Syntax.term -> 'm) -> FStar_Syntax_Syntax.term -> 'm
  =
  fun md ->
    fun vt ->
      fun tm ->
        visitM_term_univs md vt
          (fun uu___ -> (Obj.magic (FStar_Class_Monad.return md ())) uu___)
          tm
let visitM_sigelt :
  'm .
    'm FStar_Class_Monad.monad ->
      (FStar_Syntax_Syntax.term -> 'm) ->
        (FStar_Syntax_Syntax.universe -> 'm) ->
          FStar_Syntax_Syntax.sigelt -> 'm
  =
  fun md ->
    fun vt ->
      fun vu ->
        fun tm ->
          let dict =
            let uu___ =
              let uu___1 = novfs md in
              {
                lvm_monad = (uu___1.lvm_monad);
                f_term = vt;
                f_binder = (uu___1.f_binder);
                f_binding_bv = (uu___1.f_binding_bv);
                f_br = (uu___1.f_br);
                f_comp = (uu___1.f_comp);
                f_residual_comp = (uu___1.f_residual_comp);
                f_univ = vu
              } in
            tie_bu md uu___ in
          on_sub_sigelt dict tm