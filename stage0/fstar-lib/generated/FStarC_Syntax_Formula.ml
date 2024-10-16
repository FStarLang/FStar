open Prims
type qpats = FStarC_Syntax_Syntax.args Prims.list
type connective =
  | QAll of (FStarC_Syntax_Syntax.binders * qpats * FStarC_Syntax_Syntax.typ)
  
  | QEx of (FStarC_Syntax_Syntax.binders * qpats * FStarC_Syntax_Syntax.typ)
  
  | BaseConn of (FStarC_Ident.lident * FStarC_Syntax_Syntax.args) 
let (uu___is_QAll : connective -> Prims.bool) =
  fun projectee -> match projectee with | QAll _0 -> true | uu___ -> false
let (__proj__QAll__item___0 :
  connective ->
    (FStarC_Syntax_Syntax.binders * qpats * FStarC_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QAll _0 -> _0
let (uu___is_QEx : connective -> Prims.bool) =
  fun projectee -> match projectee with | QEx _0 -> true | uu___ -> false
let (__proj__QEx__item___0 :
  connective ->
    (FStarC_Syntax_Syntax.binders * qpats * FStarC_Syntax_Syntax.typ))
  = fun projectee -> match projectee with | QEx _0 -> _0
let (uu___is_BaseConn : connective -> Prims.bool) =
  fun projectee ->
    match projectee with | BaseConn _0 -> true | uu___ -> false
let (__proj__BaseConn__item___0 :
  connective -> (FStarC_Ident.lident * FStarC_Syntax_Syntax.args)) =
  fun projectee -> match projectee with | BaseConn _0 -> _0
let (connective_to_string : connective -> Prims.string) =
  fun c ->
    match c with
    | QAll p ->
        let uu___ =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_tuple3
               (FStarC_Class_Show.show_list
                  FStarC_Syntax_Print.showable_binder)
               (FStarC_Class_Show.show_list
                  (FStarC_Class_Show.show_list
                     (FStarC_Class_Show.show_tuple2
                        FStarC_Syntax_Print.showable_term
                        FStarC_Syntax_Print.showable_aqual)))
               FStarC_Syntax_Print.showable_term) p in
        Prims.strcat "QAll " uu___
    | QEx p ->
        let uu___ =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_tuple3
               (FStarC_Class_Show.show_list
                  FStarC_Syntax_Print.showable_binder)
               (FStarC_Class_Show.show_list
                  (FStarC_Class_Show.show_list
                     (FStarC_Class_Show.show_tuple2
                        FStarC_Syntax_Print.showable_term
                        FStarC_Syntax_Print.showable_aqual)))
               FStarC_Syntax_Print.showable_term) p in
        Prims.strcat "QEx " uu___
    | BaseConn p ->
        let uu___ =
          FStarC_Class_Show.show
            (FStarC_Class_Show.show_tuple2 FStarC_Ident.showable_lident
               (FStarC_Class_Show.show_list
                  (FStarC_Class_Show.show_tuple2
                     FStarC_Syntax_Print.showable_term
                     FStarC_Syntax_Print.showable_aqual))) p in
        Prims.strcat "BaseConn" uu___
let (showable_connective : connective FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = connective_to_string }
let (destruct_base_table :
  (Prims.int * (FStarC_Ident.lident * FStarC_Ident.lident) Prims.list)
    Prims.list)
  =
  let f x = (x, x) in
  [(Prims.int_zero,
     [f FStarC_Parser_Const.true_lid; f FStarC_Parser_Const.false_lid]);
  (Prims.int_one, [f FStarC_Parser_Const.not_lid]);
  ((Prims.of_int (2)),
    [f FStarC_Parser_Const.and_lid;
    f FStarC_Parser_Const.or_lid;
    f FStarC_Parser_Const.imp_lid;
    f FStarC_Parser_Const.iff_lid;
    f FStarC_Parser_Const.eq2_lid]);
  ((Prims.of_int (3)),
    [f FStarC_Parser_Const.ite_lid; f FStarC_Parser_Const.eq2_lid])]
let (destruct_sq_base_table :
  (Prims.int * (FStarC_Ident.lident * FStarC_Ident.lident) Prims.list)
    Prims.list)
  =
  [(Prims.int_zero,
     [(FStarC_Parser_Const.c_true_lid, FStarC_Parser_Const.true_lid);
     (FStarC_Parser_Const.empty_type_lid, FStarC_Parser_Const.false_lid)]);
  ((Prims.of_int (2)),
    [(FStarC_Parser_Const.c_and_lid, FStarC_Parser_Const.and_lid);
    (FStarC_Parser_Const.c_or_lid, FStarC_Parser_Const.or_lid);
    (FStarC_Parser_Const.c_eq2_lid, FStarC_Parser_Const.eq2_lid)]);
  ((Prims.of_int (3)),
    [(FStarC_Parser_Const.c_eq2_lid, FStarC_Parser_Const.eq2_lid)])]
let rec (unmeta_monadic :
  FStarC_Syntax_Syntax.term -> FStarC_Syntax_Syntax.term) =
  fun f ->
    let f1 = FStarC_Syntax_Subst.compress f in
    match f1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic uu___;_}
        -> unmeta_monadic t
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_monadic_lift
            uu___;_}
        -> unmeta_monadic t
    | uu___ -> f1
let (lookup_arity_lid :
  (Prims.int * (FStarC_Ident.lident * FStarC_Ident.lident) Prims.list)
    Prims.list ->
    FStarC_Ident.lident ->
      FStarC_Syntax_Syntax.args -> connective FStar_Pervasives_Native.option)
  =
  fun table ->
    fun target_lid ->
      fun args ->
        let arg_len = FStarC_Compiler_List.length args in
        let aux uu___ =
          match uu___ with
          | (arity, lids) ->
              if arg_len = arity
              then
                FStarC_Compiler_Util.find_map lids
                  (fun uu___1 ->
                     match uu___1 with
                     | (lid, out_lid) ->
                         let uu___2 = FStarC_Ident.lid_equals target_lid lid in
                         if uu___2
                         then
                           FStar_Pervasives_Native.Some
                             (BaseConn (out_lid, args))
                         else FStar_Pervasives_Native.None)
              else FStar_Pervasives_Native.None in
        FStarC_Compiler_Util.find_map table aux
let (destruct_base_conn :
  FStarC_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun t ->
    let uu___ = FStarC_Syntax_Util.head_and_args t in
    match uu___ with
    | (hd, args) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Util.un_uinst hd in
          uu___2.FStarC_Syntax_Syntax.n in
        (match uu___1 with
         | FStarC_Syntax_Syntax.Tm_fvar fv ->
             lookup_arity_lid destruct_base_table
               (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v args
         | uu___2 -> FStar_Pervasives_Native.None)
let (destruct_sq_base_conn :
  FStarC_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun uu___ ->
    (fun t ->
       let uu___ = FStarC_Syntax_Util.un_squash t in
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option ()
            () (Obj.magic uu___)
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  let t2 = FStarC_Syntax_Util.unmeta t1 in
                  let uu___1 = FStarC_Syntax_Util.head_and_args_full t2 in
                  match uu___1 with
                  | (hd, args) ->
                      let uu___2 =
                        let uu___3 = FStarC_Syntax_Util.un_uinst hd in
                        uu___3.FStarC_Syntax_Syntax.n in
                      (match uu___2 with
                       | FStarC_Syntax_Syntax.Tm_fvar fv ->
                           Obj.magic
                             (lookup_arity_lid destruct_sq_base_table
                                (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
                                args)
                       | uu___3 -> Obj.magic FStar_Pervasives_Native.None))
                 uu___1))) uu___
let (patterns :
  FStarC_Syntax_Syntax.term ->
    ((FStarC_Syntax_Syntax.term' FStarC_Syntax_Syntax.syntax *
      FStarC_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
      Prims.list Prims.list * FStarC_Syntax_Syntax.term))
  =
  fun t ->
    let t1 = FStarC_Syntax_Subst.compress t in
    match t1.FStarC_Syntax_Syntax.n with
    | FStarC_Syntax_Syntax.Tm_meta
        { FStarC_Syntax_Syntax.tm2 = t2;
          FStarC_Syntax_Syntax.meta = FStarC_Syntax_Syntax.Meta_pattern
            (uu___, pats);_}
        -> let uu___1 = FStarC_Syntax_Subst.compress t2 in (pats, uu___1)
    | uu___ -> ([], t1)
let (destruct_q_conn :
  FStarC_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun t ->
    let is_q fa fv =
      if fa
      then
        FStarC_Syntax_Util.is_forall
          (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
      else
        FStarC_Syntax_Util.is_exists
          (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
    let flat t1 =
      let uu___ = FStarC_Syntax_Util.head_and_args t1 in
      match uu___ with
      | (t2, args) ->
          let uu___1 = FStarC_Syntax_Util.un_uinst t2 in
          let uu___2 =
            FStarC_Compiler_List.map
              (fun uu___3 ->
                 match uu___3 with
                 | (t3, imp) ->
                     let uu___4 = FStarC_Syntax_Util.unascribe t3 in
                     (uu___4, imp)) args in
          (uu___1, uu___2) in
    let rec aux qopt out t1 =
      let uu___ = let uu___1 = flat t1 in (qopt, uu___1) in
      match uu___ with
      | (FStar_Pervasives_Native.Some fa,
         ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar tc;
            FStarC_Syntax_Syntax.pos = uu___1;
            FStarC_Syntax_Syntax.vars = uu___2;
            FStarC_Syntax_Syntax.hash_code = uu___3;_},
          ({
             FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_abs
               { FStarC_Syntax_Syntax.bs = b::[];
                 FStarC_Syntax_Syntax.body = t2;
                 FStarC_Syntax_Syntax.rc_opt = uu___4;_};
             FStarC_Syntax_Syntax.pos = uu___5;
             FStarC_Syntax_Syntax.vars = uu___6;
             FStarC_Syntax_Syntax.hash_code = uu___7;_},
           uu___8)::[]))
          when is_q fa tc -> aux qopt (b :: out) t2
      | (FStar_Pervasives_Native.Some fa,
         ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar tc;
            FStarC_Syntax_Syntax.pos = uu___1;
            FStarC_Syntax_Syntax.vars = uu___2;
            FStarC_Syntax_Syntax.hash_code = uu___3;_},
          uu___4::({
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_abs
                       { FStarC_Syntax_Syntax.bs = b::[];
                         FStarC_Syntax_Syntax.body = t2;
                         FStarC_Syntax_Syntax.rc_opt = uu___5;_};
                     FStarC_Syntax_Syntax.pos = uu___6;
                     FStarC_Syntax_Syntax.vars = uu___7;
                     FStarC_Syntax_Syntax.hash_code = uu___8;_},
                   uu___9)::[]))
          when is_q fa tc -> aux qopt (b :: out) t2
      | (FStar_Pervasives_Native.None,
         ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar tc;
            FStarC_Syntax_Syntax.pos = uu___1;
            FStarC_Syntax_Syntax.vars = uu___2;
            FStarC_Syntax_Syntax.hash_code = uu___3;_},
          ({
             FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_abs
               { FStarC_Syntax_Syntax.bs = b::[];
                 FStarC_Syntax_Syntax.body = t2;
                 FStarC_Syntax_Syntax.rc_opt = uu___4;_};
             FStarC_Syntax_Syntax.pos = uu___5;
             FStarC_Syntax_Syntax.vars = uu___6;
             FStarC_Syntax_Syntax.hash_code = uu___7;_},
           uu___8)::[]))
          when
          FStarC_Syntax_Util.is_qlid
            (tc.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
          ->
          let uu___9 =
            let uu___10 =
              FStarC_Syntax_Util.is_forall
                (tc.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
            FStar_Pervasives_Native.Some uu___10 in
          aux uu___9 (b :: out) t2
      | (FStar_Pervasives_Native.None,
         ({ FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_fvar tc;
            FStarC_Syntax_Syntax.pos = uu___1;
            FStarC_Syntax_Syntax.vars = uu___2;
            FStarC_Syntax_Syntax.hash_code = uu___3;_},
          uu___4::({
                     FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_abs
                       { FStarC_Syntax_Syntax.bs = b::[];
                         FStarC_Syntax_Syntax.body = t2;
                         FStarC_Syntax_Syntax.rc_opt = uu___5;_};
                     FStarC_Syntax_Syntax.pos = uu___6;
                     FStarC_Syntax_Syntax.vars = uu___7;
                     FStarC_Syntax_Syntax.hash_code = uu___8;_},
                   uu___9)::[]))
          when
          FStarC_Syntax_Util.is_qlid
            (tc.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v
          ->
          let uu___10 =
            let uu___11 =
              FStarC_Syntax_Util.is_forall
                (tc.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
            FStar_Pervasives_Native.Some uu___11 in
          aux uu___10 (b :: out) t2
      | (FStar_Pervasives_Native.Some b, uu___1) ->
          let bs = FStarC_Compiler_List.rev out in
          let uu___2 = FStarC_Syntax_Subst.open_term bs t1 in
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
  FStarC_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun uu___ ->
    (fun t ->
       let uu___ = FStarC_Syntax_Util.un_squash t in
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option ()
            () (Obj.magic uu___)
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  let t2 = FStarC_Syntax_Util.unmeta t1 in
                  let uu___1 = FStarC_Syntax_Util.arrow_one t2 in
                  match uu___1 with
                  | FStar_Pervasives_Native.Some (b, c) ->
                      let uu___2 =
                        let uu___3 = FStarC_Syntax_Util.is_tot_or_gtot_comp c in
                        Prims.op_Negation uu___3 in
                      if uu___2
                      then Obj.magic FStar_Pervasives_Native.None
                      else
                        (let q = FStarC_Syntax_Util.comp_result c in
                         let uu___4 =
                           FStarC_Syntax_Util.is_free_in
                             b.FStarC_Syntax_Syntax.binder_bv q in
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
                                    FStarC_Syntax_Syntax.as_arg
                                      (b.FStarC_Syntax_Syntax.binder_bv).FStarC_Syntax_Syntax.sort in
                                  let uu___10 =
                                    let uu___11 =
                                      FStarC_Syntax_Syntax.as_arg q in
                                    [uu___11] in
                                  uu___9 :: uu___10 in
                                (FStarC_Parser_Const.imp_lid, uu___8) in
                              BaseConn uu___7 in
                            Obj.magic (FStar_Pervasives_Native.Some uu___6)))
                  | uu___2 -> Obj.magic FStar_Pervasives_Native.None) uu___1)))
      uu___
and (destruct_sq_exists :
  FStarC_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun uu___ ->
    (fun t ->
       let uu___ = FStarC_Syntax_Util.un_squash t in
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_option ()
            () (Obj.magic uu___)
            (fun uu___1 ->
               (fun t1 ->
                  let t1 = Obj.magic t1 in
                  let t2 = FStarC_Syntax_Util.unmeta t1 in
                  let uu___1 = FStarC_Syntax_Util.head_and_args_full t2 in
                  match uu___1 with
                  | (hd, args) ->
                      let uu___2 =
                        let uu___3 =
                          let uu___4 = FStarC_Syntax_Util.un_uinst hd in
                          uu___4.FStarC_Syntax_Syntax.n in
                        (uu___3, args) in
                      (match uu___2 with
                       | (FStarC_Syntax_Syntax.Tm_fvar fv,
                          (a1, uu___3)::(a2, uu___4)::[]) when
                           FStarC_Syntax_Syntax.fv_eq_lid fv
                             FStarC_Parser_Const.dtuple2_lid
                           ->
                           let uu___5 =
                             let uu___6 = FStarC_Syntax_Subst.compress a2 in
                             uu___6.FStarC_Syntax_Syntax.n in
                           (match uu___5 with
                            | FStarC_Syntax_Syntax.Tm_abs
                                { FStarC_Syntax_Syntax.bs = b::[];
                                  FStarC_Syntax_Syntax.body = q;
                                  FStarC_Syntax_Syntax.rc_opt = uu___6;_}
                                ->
                                let uu___7 =
                                  FStarC_Syntax_Subst.open_term [b] q in
                                (match uu___7 with
                                 | (bs, q1) ->
                                     let b1 =
                                       match bs with
                                       | b2::[] -> b2
                                       | uu___8 -> failwith "impossible" in
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
                  ((FStarC_Compiler_List.op_At bs bs'),
                    (FStarC_Compiler_List.op_At pats pats'), psi))
         | uu___1 -> f)
    | FStar_Pervasives_Native.Some (QEx (bs, pats, phi)) ->
        let uu___ = destruct_sq_exists phi in
        (match uu___ with
         | FStar_Pervasives_Native.Some (QEx (bs', pats', psi)) ->
             FStar_Pervasives_Native.Some
               (QEx
                  ((FStarC_Compiler_List.op_At bs bs'),
                    (FStarC_Compiler_List.op_At pats pats'), psi))
         | uu___1 -> f)
    | uu___ -> f
let (destruct_typ_as_formula :
  FStarC_Syntax_Syntax.term -> connective FStar_Pervasives_Native.option) =
  fun f ->
    let phi = unmeta_monadic f in
    let r =
      let uu___ = destruct_base_conn phi in
      FStarC_Compiler_Util.catch_opt uu___
        (fun uu___1 ->
           let uu___2 = destruct_q_conn phi in
           FStarC_Compiler_Util.catch_opt uu___2
             (fun uu___3 ->
                let uu___4 = destruct_sq_base_conn phi in
                FStarC_Compiler_Util.catch_opt uu___4
                  (fun uu___5 ->
                     let uu___6 = destruct_sq_forall phi in
                     FStarC_Compiler_Util.catch_opt uu___6
                       (fun uu___7 ->
                          let uu___8 = destruct_sq_exists phi in
                          FStarC_Compiler_Util.catch_opt uu___8
                            (fun uu___9 -> FStar_Pervasives_Native.None))))) in
    r