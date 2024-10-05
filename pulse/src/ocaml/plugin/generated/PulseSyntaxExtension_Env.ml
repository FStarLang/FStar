open Prims
let (r_ : FStar_Compiler_Range_Type.range) =
  FStar_Compiler_Range_Type.dummyRange
let (admit_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Prims"; "admit"] r_
let (pulse_lib_core_lid : Prims.string -> FStar_Ident.lident) =
  fun l ->
    FStar_Ident.lid_of_path
      (FStar_List_Tot_Base.op_At ["Pulse"; "Lib"; "Core"] [l]) r_
let (pulse_lib_ref_lid : Prims.string -> FStar_Ident.lident) =
  fun l ->
    FStar_Ident.lid_of_path
      (FStar_List_Tot_Base.op_At ["Pulse"; "Lib"; "Reference"] [l]) r_
let (assume_lid : FStar_Ident.lident) = pulse_lib_core_lid "assume_"
let (prims_exists_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Prims"; "l_Exists"] r_
let (prims_forall_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["Prims"; "l_Forall"] r_
let (unreachable_lid : FStar_Ident.lident) = pulse_lib_core_lid "unreachable"
let (forall_lid : FStar_Ident.lident) = pulse_lib_core_lid "op_forall_Star"
let (exists_lid : FStar_Ident.lident) = pulse_lib_core_lid "op_exists_Star"
let (star_lid : FStar_Ident.lident) = pulse_lib_core_lid "op_Star_Star"
let (emp_lid : FStar_Ident.lident) = pulse_lib_core_lid "emp"
let (pure_lid : FStar_Ident.lident) = pulse_lib_core_lid "pure"
let (stt_lid : FStar_Ident.lident) = pulse_lib_core_lid "stt"
let (assign_lid : FStar_Ident.lident) = pulse_lib_ref_lid "op_Colon_Equals"
let (stt_ghost_lid : FStar_Ident.lident) = pulse_lib_core_lid "stt_ghost"
let (stt_unobservable_lid : FStar_Ident.lident) =
  pulse_lib_core_lid "stt_unobservable"
let (stt_atomic_lid : FStar_Ident.lident) = pulse_lib_core_lid "stt_atomic"
let (op_colon_equals_lid :
  FStar_Compiler_Range_Type.range -> FStar_Ident.lident) =
  fun r -> FStar_Ident.lid_of_path ["op_Colon_Equals"] r
let (op_array_assignment_lid :
  FStar_Compiler_Range_Type.range -> FStar_Ident.lident) =
  fun r -> FStar_Ident.lid_of_path ["op_Array_Assignment"] r
let (op_bang_lid : FStar_Ident.lident) = pulse_lib_ref_lid "op_Bang"
let (read : FStar_Ident.ident -> FStar_Parser_AST.term) =
  fun x ->
    let range = FStar_Ident.range_of_id x in
    let level = FStar_Parser_AST.Un in
    let head =
      {
        FStar_Parser_AST.tm = (FStar_Parser_AST.Var op_bang_lid);
        FStar_Parser_AST.range = range;
        FStar_Parser_AST.level = level
      } in
    let arg =
      let uu___ =
        let uu___1 = FStar_Ident.lid_of_ids [x] in
        FStar_Parser_AST.Var uu___1 in
      {
        FStar_Parser_AST.tm = uu___;
        FStar_Parser_AST.range = range;
        FStar_Parser_AST.level = level
      } in
    {
      FStar_Parser_AST.tm =
        (FStar_Parser_AST.App (head, arg, FStar_Parser_AST.Nothing));
      FStar_Parser_AST.range = range;
      FStar_Parser_AST.level = level
    }
type env_t =
  {
  dsenv: FStar_Syntax_DsEnv.env ;
  local_refs: FStar_Ident.ident Prims.list }
let (__proj__Mkenv_t__item__dsenv : env_t -> FStar_Syntax_DsEnv.env) =
  fun projectee -> match projectee with | { dsenv; local_refs;_} -> dsenv
let (__proj__Mkenv_t__item__local_refs :
  env_t -> FStar_Ident.ident Prims.list) =
  fun projectee ->
    match projectee with | { dsenv; local_refs;_} -> local_refs
type name = Prims.string Prims.list
let (push_bv :
  env_t -> FStar_Ident.ident -> (env_t * FStar_Syntax_Syntax.bv)) =
  fun env ->
    fun x ->
      let uu___ = FStar_Syntax_DsEnv.push_bv env.dsenv x in
      match uu___ with
      | (dsenv, bv) -> ({ dsenv; local_refs = (env.local_refs) }, bv)
let rec (push_bvs :
  env_t ->
    FStar_Ident.ident Prims.list ->
      (env_t * FStar_Syntax_Syntax.bv Prims.list))
  =
  fun env ->
    fun xs ->
      match xs with
      | [] -> (env, [])
      | x::xs1 ->
          let uu___ = push_bv env x in
          (match uu___ with
           | (env1, bv) ->
               let uu___1 = push_bvs env1 xs1 in
               (match uu___1 with | (env2, bvs) -> (env2, (bv :: bvs))))
let (push_namespace : env_t -> FStar_Ident.lident -> env_t) =
  fun env ->
    fun lid ->
      let dsenv =
        FStar_Syntax_DsEnv.push_namespace env.dsenv lid
          FStar_Syntax_Syntax.Unrestricted in
      { dsenv; local_refs = (env.local_refs) }
let (resolve_lid :
  env_t ->
    FStar_Ident.lident -> FStar_Ident.lident PulseSyntaxExtension_Err.err)
  =
  fun env ->
    fun lid ->
      let uu___ = FStar_Syntax_DsEnv.try_lookup_lid env.dsenv lid in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          let uu___1 =
            let uu___2 =
              FStar_Class_Show.show FStar_Ident.showable_lident lid in
            FStar_Compiler_Util.format1 "Name %s not found" uu___2 in
          let uu___2 =
            FStar_Class_HasRange.pos PulseSyntaxExtension_Err.hasRange_lident
              lid in
          PulseSyntaxExtension_Err.fail uu___1 uu___2
      | FStar_Pervasives_Native.Some t ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Subst.compress t in
            uu___2.FStar_Syntax_Syntax.n in
          (match uu___1 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               let uu___2 = FStar_Syntax_Syntax.lid_of_fv fv in
               PulseSyntaxExtension_Err.return uu___2
           | uu___2 ->
               let uu___3 =
                 let uu___4 =
                   FStar_Class_Show.show FStar_Ident.showable_lident lid in
                 let uu___5 =
                   FStar_Class_Show.show FStar_Syntax_Print.showable_term t in
                 FStar_Compiler_Util.format2
                   "Name %s resolved unexpectedly to %s" uu___4 uu___5 in
               let uu___4 =
                 FStar_Class_HasRange.pos
                   PulseSyntaxExtension_Err.hasRange_lident lid in
               PulseSyntaxExtension_Err.fail uu___3 uu___4)
let (resolve_names :
  env_t ->
    FStar_Ident.lident Prims.list FStar_Pervasives_Native.option ->
      FStar_Ident.lident Prims.list FStar_Pervasives_Native.option
        PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun ns ->
           match ns with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (PulseSyntaxExtension_Err.return
                       FStar_Pervasives_Native.None))
           | FStar_Pervasives_Native.Some ns1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       Obj.magic
                         (FStar_Class_Monad.mapM
                            PulseSyntaxExtension_Err.err_monad () ()
                            (fun uu___1 ->
                               (Obj.magic (resolve_lid env)) uu___1)
                            (Obj.magic ns1)) in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun ns2 ->
                             let ns2 = Obj.magic ns2 in
                             Obj.magic
                               (PulseSyntaxExtension_Err.return
                                  (FStar_Pervasives_Native.Some ns2))) uu___1))))
        uu___1 uu___
let (destruct_binder :
  FStar_Parser_AST.binder ->
    (FStar_Parser_AST.aqual * FStar_Ident.ident * FStar_Parser_AST.term *
      FStar_Parser_AST.term Prims.list))
  =
  fun b ->
    let attrs = b.FStar_Parser_AST.battributes in
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.Annotated (x, t) ->
        ((b.FStar_Parser_AST.aqual), x, t, attrs)
    | FStar_Parser_AST.TAnnotated (x, t) ->
        ((b.FStar_Parser_AST.aqual), x, t, attrs)
    | FStar_Parser_AST.NoName t ->
        let uu___ = FStar_Ident.id_of_text "_" in
        ((b.FStar_Parser_AST.aqual), uu___, t, attrs)
    | FStar_Parser_AST.Variable x ->
        let uu___ =
          let uu___1 = FStar_Ident.range_of_id x in
          FStar_Parser_AST.mk_term FStar_Parser_AST.Wild uu___1
            FStar_Parser_AST.Un in
        ((b.FStar_Parser_AST.aqual), x, uu___, attrs)
    | FStar_Parser_AST.TVariable x ->
        let uu___ =
          let uu___1 = FStar_Ident.range_of_id x in
          FStar_Parser_AST.mk_term FStar_Parser_AST.Wild uu___1
            FStar_Parser_AST.Un in
        ((b.FStar_Parser_AST.aqual), x, uu___, attrs)
let free_vars_list :
  'a .
    (env_t -> 'a -> FStar_Ident.ident Prims.list) ->
      env_t -> 'a Prims.list -> FStar_Ident.ident Prims.list
  = fun f -> fun env -> fun xs -> FStar_Compiler_List.collect (f env) xs
let rec (free_vars_term :
  env_t -> FStar_Parser_AST.term -> FStar_Ident.ident Prims.list) =
  fun env -> fun t -> FStar_ToSyntax_ToSyntax.free_vars false env.dsenv t
and (free_vars_binders :
  env_t ->
    PulseSyntaxExtension_Sugar.binders ->
      (env_t * FStar_Ident.ident Prims.list))
  =
  fun env ->
    fun bs ->
      match bs with
      | [] -> (env, [])
      | b::bs1 ->
          let uu___ = destruct_binder b in
          (match uu___ with
           | (uu___1, x, t, attrs) ->
               let fvs = free_vars_term env t in
               let fvs_attrs = free_vars_list free_vars_term env attrs in
               let uu___2 =
                 let uu___3 =
                   let uu___4 = push_bv env x in
                   FStar_Pervasives_Native.fst uu___4 in
                 free_vars_binders uu___3 bs1 in
               (match uu___2 with
                | (env', res) ->
                    (env',
                      (FStar_List_Tot_Base.op_At fvs
                         (FStar_List_Tot_Base.op_At fvs_attrs res)))))
let (free_vars_slprop :
  env_t -> PulseSyntaxExtension_Sugar.slprop -> FStar_Ident.ident Prims.list)
  =
  fun env ->
    fun t ->
      match t.PulseSyntaxExtension_Sugar.v with
      | PulseSyntaxExtension_Sugar.SLPropTerm t1 -> free_vars_term env t1
let (free_vars_comp :
  env_t ->
    PulseSyntaxExtension_Sugar.computation_type ->
      FStar_Ident.ident Prims.list)
  =
  fun env ->
    fun c ->
      let ids =
        let uu___ =
          free_vars_slprop env c.PulseSyntaxExtension_Sugar.precondition in
        let uu___1 =
          let uu___2 =
            free_vars_term env c.PulseSyntaxExtension_Sugar.return_type in
          let uu___3 =
            let uu___4 =
              let uu___5 =
                push_bv env c.PulseSyntaxExtension_Sugar.return_name in
              FStar_Pervasives_Native.fst uu___5 in
            free_vars_slprop uu___4
              c.PulseSyntaxExtension_Sugar.postcondition in
          FStar_List_Tot_Base.op_At uu___2 uu___3 in
        FStar_List_Tot_Base.op_At uu___ uu___1 in
      FStar_Class_Ord.dedup FStar_Syntax_Syntax.ord_ident ids
let (pat_vars :
  FStar_Parser_AST.pattern ->
    FStar_Ident.ident Prims.list PulseSyntaxExtension_Err.err)
  =
  fun uu___ ->
    (fun p ->
       let r = p.FStar_Parser_AST.prange in
       match p.FStar_Parser_AST.pat with
       | FStar_Parser_AST.PatVar (id, uu___, uu___1) ->
           Obj.magic (Obj.repr (PulseSyntaxExtension_Err.return [id]))
       | FStar_Parser_AST.PatWild uu___ ->
           Obj.magic (Obj.repr (PulseSyntaxExtension_Err.return []))
       | FStar_Parser_AST.PatConst uu___ ->
           Obj.magic (Obj.repr (PulseSyntaxExtension_Err.return []))
       | FStar_Parser_AST.PatName uu___ ->
           Obj.magic (Obj.repr (PulseSyntaxExtension_Err.return []))
       | FStar_Parser_AST.PatApp (uu___, args) ->
           Obj.magic
             (Obj.repr
                (let uu___1 =
                   Obj.magic
                     (FStar_Class_Monad.mapM
                        PulseSyntaxExtension_Err.err_monad () ()
                        (fun uu___2 ->
                           (fun p1 ->
                              let p1 = Obj.magic p1 in
                              match p1.FStar_Parser_AST.pat with
                              | FStar_Parser_AST.PatVar (id, uu___2, uu___3)
                                  ->
                                  Obj.magic
                                    (PulseSyntaxExtension_Err.return [id])
                              | FStar_Parser_AST.PatWild uu___2 ->
                                  Obj.magic
                                    (PulseSyntaxExtension_Err.return [])
                              | uu___2 ->
                                  Obj.magic
                                    (PulseSyntaxExtension_Err.fail
                                       "invalid pattern: no deep patterns allowed"
                                       r)) uu___2) (Obj.magic args)) in
                 FStar_Class_Monad.op_let_Bang
                   PulseSyntaxExtension_Err.err_monad () ()
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun vars ->
                         let vars = Obj.magic vars in
                         Obj.magic
                           (PulseSyntaxExtension_Err.return
                              (FStar_List_Tot_Base.flatten vars))) uu___2)))
       | uu___ ->
           Obj.magic
             (Obj.repr (PulseSyntaxExtension_Err.fail "invalid pattern" r)))
      uu___