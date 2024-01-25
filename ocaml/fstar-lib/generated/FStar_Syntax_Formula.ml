open Prims
type qpats = FStar_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | QEx of (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ) 
  | BaseConn of (FStar_Ident.lident * FStar_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee -> match projectee with | QAll _0 -> true | uu___ -> false
let (__proj__QAll__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QAll _0 -> _0
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee -> match projectee with | QEx _0 -> true | uu___ -> false
let (__proj__QEx__item___0 :
  connective ->
    (FStar_Syntax_Syntax.binders * qpats * FStar_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QEx _0 -> _0
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee ->
    match projectee with | BaseConn _0 -> true | uu___ -> false
let (__proj__BaseConn__item___0 :
  connective -> (FStar_Ident.lident * FStar_Syntax_Syntax.args)) =
  fun projectee -> match projectee with | BaseConn _0 -> _0
let (connective_to_string : connective -> Prims.string) =
  fun c ->
    match c with
    | QAll p ->
        let uu___ =
          FStar_Class_Show.show
            (FStar_Class_Show.show_tuple3
               (FStar_Class_Show.show_list FStar_Syntax_Print.showable_binder)
               (FStar_Class_Show.show_list FStar_Syntax_Print.showable_args)
               FStar_Syntax_Print.showable_term) p in
        Prims.strcat "QAll " uu___
    | QEx p ->
        let uu___ =
          FStar_Class_Show.show
            (FStar_Class_Show.show_tuple3
               (FStar_Class_Show.show_list FStar_Syntax_Print.showable_binder)
               (FStar_Class_Show.show_list FStar_Syntax_Print.showable_args)
               FStar_Syntax_Print.showable_term) p in
        Prims.strcat "QEx " uu___
    | BaseConn p ->
        let uu___ =
          FStar_Class_Show.show
            (FStar_Class_Show.show_tuple2 FStar_Ident.showable_lident
               FStar_Syntax_Print.showable_args) p in
        Prims.strcat "BaseConn" uu___
let (showable_connective : connective FStar_Class_Show.showable) =
  { FStar_Class_Show.show = connective_to_string }
let (destruct_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  let f x = (x, x) in
  [(Prims.int_zero,
     [f FStar_Parser_Const.true_lid; f FStar_Parser_Const.false_lid]);
  (Prims.int_one, [f FStar_Parser_Const.not_lid]);
  ((Prims.of_int (2)),
    [f FStar_Parser_Const.and_lid;
    f FStar_Parser_Const.or_lid;
    f FStar_Parser_Const.imp_lid;
    f FStar_Parser_Const.iff_lid;
    f FStar_Parser_Const.eq2_lid]);
  ((Prims.of_int (3)),
    [f FStar_Parser_Const.ite_lid; f FStar_Parser_Const.eq2_lid])]
let (destruct_sq_base_table :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list)
  =
  [(Prims.int_zero,
     [(FStar_Parser_Const.c_true_lid, FStar_Parser_Const.true_lid);
     (FStar_Parser_Const.empty_type_lid, FStar_Parser_Const.false_lid)]);
  ((Prims.of_int (2)),
    [(FStar_Parser_Const.c_and_lid, FStar_Parser_Const.and_lid);
    (FStar_Parser_Const.c_or_lid, FStar_Parser_Const.or_lid);
    (FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.eq2_lid)]);
  ((Prims.of_int (3)),
    [(FStar_Parser_Const.c_eq2_lid, FStar_Parser_Const.eq2_lid)])]
let rec (unmeta_monadic :
  FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun f ->
    let f1 = FStar_Syntax_Subst.compress f in
    match f1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        { FStar_Syntax_Syntax.tm2 = t;
          FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_monadic uu___;_}
        -> unmeta_monadic t
    | FStar_Syntax_Syntax.Tm_meta
        { FStar_Syntax_Syntax.tm2 = t;
          FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_monadic_lift
            uu___;_}
        -> unmeta_monadic t
    | uu___ -> f1
let (lookup_arity_lid :
  (Prims.int * (FStar_Ident.lident * FStar_Ident.lident) Prims.list)
    Prims.list ->
    FStar_Ident.lident ->
      FStar_Syntax_Syntax.args -> connective FStar_Pervasives_Native.option)
  =
  fun table ->
    fun target_lid ->
      fun args ->
        let arg_len = FStar_Compiler_List.length args in
        let aux uu___ =
          match uu___ with
          | (arity, lids) ->
              if arg_len = arity
              then
                FStar_Compiler_Util.find_map lids
                  (fun uu___1 ->
                     match uu___1 with
                     | (lid, out_lid) ->
                         let uu___2 = FStar_Ident.lid_equals target_lid lid in
                         if uu___2
                         then
                           FStar_Pervasives_Native.Some
                             (BaseConn (out_lid, args))
                         else FStar_Pervasives_Native.None)
              else FStar_Pervasives_Native.None in
        FStar_Compiler_Util.find_map table aux
let (destruct_base_conn :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Util.un_uinst hd in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             lookup_arity_lid destruct_base_table
               (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v args
         | uu___2 -> FStar_Pervasives_Native.None)
let (destruct_sq_base_conn :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun uu___ ->
    (fun t ->
       let uu___ = FStar_Syntax_Util.un_squash t in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Class_Monad.monad_option () ()
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  let t2 = FStar_Syntax_Util.unmeta t1 in
                  let uu___1 = FStar_Syntax_Util.head_and_args_full t2 in
                  match uu___1 with
                  | (hd, args) ->
                      let uu___2 =
                        let uu___3 = FStar_Syntax_Util.un_uinst hd in
                        uu___3.FStar_Syntax_Syntax.n in
                      (match uu___2 with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           Obj.magic
                             (lookup_arity_lid destruct_sq_base_table
                                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                args)
                       | uu___3 -> Obj.magic FStar_Pervasives_Native.None))
                 uu___1))) uu___
let (patterns :
  FStar_Syntax_Syntax.term ->
    ((FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
      FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list Prims.list * FStar_Syntax_Syntax.term))
  =
  fun t ->
    let t1 = FStar_Syntax_Subst.compress t in
    match t1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_meta
        { FStar_Syntax_Syntax.tm2 = t2;
          FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_pattern
            (uu___, pats);_}
        -> let uu___1 = FStar_Syntax_Subst.compress t2 in (pats, uu___1)
    | uu___ -> ([], t1)
let (destruct_q_conn :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun t ->
    let is_q fa fv =
      if fa
      then
        FStar_Syntax_Util.is_forall
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
      else
        FStar_Syntax_Util.is_exists
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
    let flat t1 =
      let uu___ = FStar_Syntax_Util.head_and_args t1 in
      match uu___ with
      | (t2, args) ->
          let uu___1 = FStar_Syntax_Util.un_uinst t2 in
          let uu___2 =
            FStar_Compiler_List.map
              (fun uu___3 ->
                 match uu___3 with
                 | (t3, imp) ->
                     let uu___4 = FStar_Syntax_Util.unascribe t3 in
                     (uu___4, imp)) args in
          (uu___1, uu___2) in
    let rec aux qopt out t1 =
      let uu___ = let uu___1 = flat t1 in (qopt, uu___1) in
      match uu___ with
      | (FStar_Pervasives_Native.Some fa,
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
            FStar_Syntax_Syntax.pos = uu___1;
            FStar_Syntax_Syntax.vars = uu___2;
            FStar_Syntax_Syntax.hash_code = uu___3;_},
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
               { FStar_Syntax_Syntax.bs = b::[];
                 FStar_Syntax_Syntax.body = t2;
                 FStar_Syntax_Syntax.rc_opt = uu___4;_};
             FStar_Syntax_Syntax.pos = uu___5;
             FStar_Syntax_Syntax.vars = uu___6;
             FStar_Syntax_Syntax.hash_code = uu___7;_},
           uu___8)::[]))
          when is_q fa tc -> aux qopt (b :: out) t2
      | (FStar_Pervasives_Native.Some fa,
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
            FStar_Syntax_Syntax.pos = uu___1;
            FStar_Syntax_Syntax.vars = uu___2;
            FStar_Syntax_Syntax.hash_code = uu___3;_},
          uu___4::({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                       { FStar_Syntax_Syntax.bs = b::[];
                         FStar_Syntax_Syntax.body = t2;
                         FStar_Syntax_Syntax.rc_opt = uu___5;_};
                     FStar_Syntax_Syntax.pos = uu___6;
                     FStar_Syntax_Syntax.vars = uu___7;
                     FStar_Syntax_Syntax.hash_code = uu___8;_},
                   uu___9)::[]))
          when is_q fa tc -> aux qopt (b :: out) t2
      | (FStar_Pervasives_Native.None,
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
            FStar_Syntax_Syntax.pos = uu___1;
            FStar_Syntax_Syntax.vars = uu___2;
            FStar_Syntax_Syntax.hash_code = uu___3;_},
          ({
             FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
               { FStar_Syntax_Syntax.bs = b::[];
                 FStar_Syntax_Syntax.body = t2;
                 FStar_Syntax_Syntax.rc_opt = uu___4;_};
             FStar_Syntax_Syntax.pos = uu___5;
             FStar_Syntax_Syntax.vars = uu___6;
             FStar_Syntax_Syntax.hash_code = uu___7;_},
           uu___8)::[]))
          when
          FStar_Syntax_Util.is_qlid
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          ->
          let uu___9 =
            let uu___10 =
              FStar_Syntax_Util.is_forall
                (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Pervasives_Native.Some uu___10 in
          aux uu___9 (b :: out) t2
      | (FStar_Pervasives_Native.None,
         ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar tc;
            FStar_Syntax_Syntax.pos = uu___1;
            FStar_Syntax_Syntax.vars = uu___2;
            FStar_Syntax_Syntax.hash_code = uu___3;_},
          uu___4::({
                     FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_abs
                       { FStar_Syntax_Syntax.bs = b::[];
                         FStar_Syntax_Syntax.body = t2;
                         FStar_Syntax_Syntax.rc_opt = uu___5;_};
                     FStar_Syntax_Syntax.pos = uu___6;
                     FStar_Syntax_Syntax.vars = uu___7;
                     FStar_Syntax_Syntax.hash_code = uu___8;_},
                   uu___9)::[]))
          when
          FStar_Syntax_Util.is_qlid
            (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
          ->
          let uu___10 =
            let uu___11 =
              FStar_Syntax_Util.is_forall
                (tc.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Pervasives_Native.Some uu___11 in
          aux uu___10 (b :: out) t2
      | (FStar_Pervasives_Native.Some b, uu___1) ->
          let bs = FStar_Compiler_List.rev out in
          let uu___2 = FStar_Syntax_Subst.open_term bs t1 in
          (match uu___2 with
           | (bs1, t2) ->
               let uu___3 = patterns t2 in
               (match uu___3 with
                | (pats, body) ->
                    if b
                    then
                      FStar_Pervasives_Native.Some (QAll (bs1, pats, body))
                    else FStar_Pervasives_Native.Some (QEx (bs1, pats, body))))
      | uu___1 -> FStar_Pervasives_Native.None in
    aux FStar_Pervasives_Native.None [] t
let rec (destruct_sq_forall :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun uu___ ->
    (fun t ->
       let uu___ = FStar_Syntax_Util.un_squash t in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Class_Monad.monad_option () ()
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  let uu___1 = FStar_Syntax_Util.arrow_one t1 in
                  match uu___1 with
                  | FStar_Pervasives_Native.Some (b, c) ->
                      let uu___2 =
                        let uu___3 = FStar_Syntax_Util.is_tot_or_gtot_comp c in
                        Prims.op_Negation uu___3 in
                      if uu___2
                      then Obj.magic FStar_Pervasives_Native.None
                      else
                        (let q = FStar_Syntax_Util.comp_result c in
                         let uu___4 =
                           FStar_Syntax_Util.is_free_in
                             b.FStar_Syntax_Syntax.binder_bv q in
                         if uu___4
                         then
                           let uu___5 = patterns q in
                           match uu___5 with
                           | (pats, q1) ->
                               Obj.magic
                                 (maybe_collect
                                    (FStar_Pervasives_Native.Some
                                       (QAll ([b], pats, q1))))
                         else
                           (let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    FStar_Syntax_Syntax.as_arg
                                      (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                  let uu___10 =
                                    let uu___11 =
                                      FStar_Syntax_Syntax.as_arg q in
                                    [uu___11] in
                                  uu___9 :: uu___10 in
                                (FStar_Parser_Const.imp_lid, uu___8) in
                              BaseConn uu___7 in
                            Obj.magic (FStar_Pervasives_Native.Some uu___6)))
                  | uu___2 -> Obj.magic FStar_Pervasives_Native.None) uu___1)))
      uu___
and (destruct_sq_exists :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun uu___ ->
    (fun t ->
       let uu___ = FStar_Syntax_Util.un_squash t in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang FStar_Class_Monad.monad_option () ()
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  let uu___1 = FStar_Syntax_Util.head_and_args_full t1 in
                  match uu___1 with
                  | (hd, args) ->
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = FStar_Syntax_Util.un_uinst hd in
                          uu___4.FStar_Syntax_Syntax.n in
                        (uu___3, args) in
                      (match uu___2 with
                       | (FStar_Syntax_Syntax.Tm_fvar fv,
                          (a1, uu___3)::(a2, uu___4)::[]) when
                           FStar_Syntax_Syntax.fv_eq_lid fv
                             FStar_Parser_Const.dtuple2_lid
                           ->
                           let uu___5 =
                             let uu___6 = FStar_Syntax_Subst.compress a2 in
                             uu___6.FStar_Syntax_Syntax.n in
                           (match uu___5 with
                            | FStar_Syntax_Syntax.Tm_abs
                                { FStar_Syntax_Syntax.bs = b::[];
                                  FStar_Syntax_Syntax.body = q;
                                  FStar_Syntax_Syntax.rc_opt = uu___6;_}
                                ->
                                let uu___7 =
                                  FStar_Syntax_Subst.open_term [b] q in
                                (match uu___7 with
                                 | (bs, q1) ->
                                     let b1 =
                                       match bs with
                                       | b2::[] -> b2
                                       | uu___8 ->
                                           FStar_Compiler_Effect.failwith
                                             "impossible" in
                                     let uu___8 = patterns q1 in
                                     (match uu___8 with
                                      | (pats, q2) ->
                                          Obj.magic
                                            (maybe_collect
                                               (FStar_Pervasives_Native.Some
                                                  (QEx ([b1], pats, q2))))))
                            | uu___6 ->
                                Obj.magic FStar_Pervasives_Native.None)
                       | uu___3 -> Obj.magic FStar_Pervasives_Native.None))
                 uu___1))) uu___
and (maybe_collect :
  connective FStar_Pervasives_Native.option ->
    connective FStar_Pervasives_Native.option)
  =
  fun f ->
    match f with
    | FStar_Pervasives_Native.Some (QAll (bs, pats, phi)) ->
        let uu___ = destruct_sq_forall phi in
        (match uu___ with
         | FStar_Pervasives_Native.Some (QAll (bs', pats', psi)) ->
             FStar_Pervasives_Native.Some
               (QAll
                  ((FStar_Compiler_List.op_At bs bs'),
                    (FStar_Compiler_List.op_At pats pats'), psi))
         | uu___1 -> f)
    | FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) ->
        let uu___ = destruct_sq_exists phi in
        (match uu___ with
         | FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) ->
             FStar_Pervasives_Native.Some
               (QEx
                  ((FStar_Compiler_List.op_At bs bs'),
                    (FStar_Compiler_List.op_At pats pats'), psi))
         | uu___1 -> f)
    | uu___ -> f
let (destruct_typ_as_formula :
  FStar_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f ->
    let phi = unmeta_monadic f in
    let r =
      let uu___ = destruct_base_conn phi in
      FStar_Compiler_Util.catch_opt uu___
        (fun uu___1 ->
           let uu___2 = destruct_q_conn phi in
           FStar_Compiler_Util.catch_opt uu___2
             (fun uu___3 ->
                let uu___4 = destruct_sq_base_conn phi in
                FStar_Compiler_Util.catch_opt uu___4
                  (fun uu___5 ->
                     let uu___6 = destruct_sq_forall phi in
                     FStar_Compiler_Util.catch_opt uu___6
                       (fun uu___7 ->
                          let uu___8 = destruct_sq_exists phi in
                          FStar_Compiler_Util.catch_opt uu___8
                            (fun uu___9 -> FStar_Pervasives_Native.None))))) in
    r