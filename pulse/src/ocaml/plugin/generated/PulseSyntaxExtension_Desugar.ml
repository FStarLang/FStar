open Prims
type error =
  (Prims.string * FStar_Compiler_Range_Type.range)
    FStar_Pervasives_Native.option
let rec fold_right1 : 'a . ('a -> 'a -> 'a) -> 'a Prims.list -> 'a =
  fun f ->
    fun l ->
      match l with
      | h::[] -> h
      | h::t -> let uu___ = fold_right1 f t in f h uu___
let (as_term :
  FStar_Syntax_Syntax.term -> PulseSyntaxExtension_SyntaxWrapper.term) =
  fun t ->
    match t.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_unknown ->
        PulseSyntaxExtension_SyntaxWrapper.tm_unknown
          t.FStar_Syntax_Syntax.pos
    | uu___ ->
        PulseSyntaxExtension_SyntaxWrapper.tm_expr t
          t.FStar_Syntax_Syntax.pos
let (desugar_const :
  FStar_Const.sconst -> PulseSyntaxExtension_SyntaxWrapper.constant) =
  fun c -> PulseSyntaxExtension_SyntaxWrapper.inspect_const c
let (slprop_to_ast_term :
  PulseSyntaxExtension_Sugar.slprop ->
    FStar_Parser_AST.term PulseSyntaxExtension_Err.err)
  =
  fun v ->
    match v.PulseSyntaxExtension_Sugar.v with
    | PulseSyntaxExtension_Sugar.SLPropTerm t ->
        PulseSyntaxExtension_Err.return t
let (comp_to_ast_term :
  PulseSyntaxExtension_Sugar.computation_type ->
    FStar_Parser_AST.term PulseSyntaxExtension_Err.err)
  =
  fun uu___ ->
    (fun c ->
       let return_ty = c.PulseSyntaxExtension_Sugar.return_type in
       let r = c.PulseSyntaxExtension_Sugar.range in
       let head =
         match c.PulseSyntaxExtension_Sugar.tag with
         | PulseSyntaxExtension_Sugar.ST ->
             let h =
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Var PulseSyntaxExtension_Env.stt_lid) r
                 FStar_Parser_AST.Expr in
             let h1 =
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    (h, return_ty, FStar_Parser_AST.Nothing)) r
                 FStar_Parser_AST.Expr in
             h1
         | PulseSyntaxExtension_Sugar.STAtomic ->
             let is =
               let uu___ =
                 let uu___1 =
                   FStar_Ident.lid_of_str "Pulse.Lib.Core.emp_inames" in
                 FStar_Parser_AST.Var uu___1 in
               FStar_Parser_AST.mk_term uu___ r FStar_Parser_AST.Expr in
             let h =
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Var
                    PulseSyntaxExtension_Env.stt_atomic_lid) r
                 FStar_Parser_AST.Expr in
             let h1 =
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    (h, return_ty, FStar_Parser_AST.Nothing)) r
                 FStar_Parser_AST.Expr in
             FStar_Parser_AST.mk_term
               (FStar_Parser_AST.App (h1, is, FStar_Parser_AST.Nothing)) r
               FStar_Parser_AST.Expr
         | PulseSyntaxExtension_Sugar.STGhost ->
             let h =
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.Var PulseSyntaxExtension_Env.stt_ghost_lid)
                 r FStar_Parser_AST.Expr in
             let h1 =
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    (h, return_ty, FStar_Parser_AST.Nothing)) r
                 FStar_Parser_AST.Expr in
             h1 in
       let uu___ =
         slprop_to_ast_term c.PulseSyntaxExtension_Sugar.precondition in
       Obj.magic
         (FStar_Class_Monad.op_let_Bang PulseSyntaxExtension_Err.err_monad ()
            () (Obj.magic uu___)
            (fun uu___1 ->
               (fun pre ->
                  let pre = Obj.magic pre in
                  let uu___1 =
                    slprop_to_ast_term
                      c.PulseSyntaxExtension_Sugar.postcondition in
                  Obj.magic
                    (FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun post ->
                             let post = Obj.magic post in
                             let post1 =
                               let pat =
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatVar
                                      ((c.PulseSyntaxExtension_Sugar.return_name),
                                        FStar_Pervasives_Native.None, [])) r in
                               let pat1 =
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatAscribed
                                      (pat,
                                        (return_ty,
                                          FStar_Pervasives_Native.None))) r in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Abs ([pat1], post)) r
                                 FStar_Parser_AST.Expr in
                             let t =
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.App
                                    (head, pre, FStar_Parser_AST.Nothing)) r
                                 FStar_Parser_AST.Expr in
                             let t1 =
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.App
                                    (t, post1, FStar_Parser_AST.Nothing)) r
                                 FStar_Parser_AST.Expr in
                             Obj.magic (PulseSyntaxExtension_Err.return t1))
                            uu___2))) uu___1))) uu___
let (faux :
  (PulseSyntaxExtension_SyntaxWrapper.qualifier
    FStar_Pervasives_Native.option *
    PulseSyntaxExtension_SyntaxWrapper.binder) ->
    FStar_Syntax_Syntax.bv ->
      (PulseSyntaxExtension_SyntaxWrapper.qualifier
        FStar_Pervasives_Native.option *
        PulseSyntaxExtension_SyntaxWrapper.binder *
        PulseSyntaxExtension_SyntaxWrapper.bv))
  =
  fun qb ->
    fun bv ->
      let uu___ = qb in
      match uu___ with
      | (q, b) ->
          let bv1 =
            let uu___1 =
              FStar_Ident.string_of_id bv.FStar_Syntax_Syntax.ppname in
            PulseSyntaxExtension_SyntaxWrapper.mk_bv
              bv.FStar_Syntax_Syntax.index uu___1
              (bv.FStar_Syntax_Syntax.sort).FStar_Syntax_Syntax.pos in
          (q, b, bv1)
let (stapp_assignment :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term Prims.list ->
      FStar_Syntax_Syntax.term ->
        PulseSyntaxExtension_SyntaxWrapper.range ->
          PulseSyntaxExtension_SyntaxWrapper.st_term)
  =
  fun assign_lid ->
    fun args ->
      fun last_arg ->
        fun r ->
          let head_fv =
            FStar_Syntax_Syntax.lid_as_fv assign_lid
              FStar_Pervasives_Native.None in
          let head = FStar_Syntax_Syntax.fv_to_tm head_fv in
          let app =
            FStar_Compiler_List.fold_left
              (fun head1 ->
                 fun arg ->
                   FStar_Syntax_Syntax.mk_Tm_app head1
                     [(arg, FStar_Pervasives_Native.None)]
                     arg.FStar_Syntax_Syntax.pos) head args in
          let uu___ = PulseSyntaxExtension_SyntaxWrapper.tm_expr app r in
          let uu___1 = as_term last_arg in
          PulseSyntaxExtension_SyntaxWrapper.tm_st_app uu___
            FStar_Pervasives_Native.None uu___1 r
let (ret :
  FStar_Syntax_Syntax.term -> PulseSyntaxExtension_SyntaxWrapper.st_term) =
  fun s ->
    let uu___ = as_term s in
    PulseSyntaxExtension_SyntaxWrapper.tm_return uu___
      s.FStar_Syntax_Syntax.pos
type admit_or_return_t =
  | STTerm of PulseSyntaxExtension_SyntaxWrapper.st_term 
  | Return of FStar_Syntax_Syntax.term 
let (uu___is_STTerm : admit_or_return_t -> Prims.bool) =
  fun projectee -> match projectee with | STTerm _0 -> true | uu___ -> false
let (__proj__STTerm__item___0 :
  admit_or_return_t -> PulseSyntaxExtension_SyntaxWrapper.st_term) =
  fun projectee -> match projectee with | STTerm _0 -> _0
let (uu___is_Return : admit_or_return_t -> Prims.bool) =
  fun projectee -> match projectee with | Return _0 -> true | uu___ -> false
let (__proj__Return__item___0 :
  admit_or_return_t -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Return _0 -> _0
let (st_term_of_admit_or_return :
  admit_or_return_t -> PulseSyntaxExtension_SyntaxWrapper.st_term) =
  fun t -> match t with | STTerm t1 -> t1 | Return t1 -> ret t1
let (admit_or_return :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Syntax_Syntax.term -> admit_or_return_t)
  =
  fun env ->
    fun s ->
      let r = s.FStar_Syntax_Syntax.pos in
      let uu___ = FStar_Syntax_Util.head_and_args_full s in
      match uu___ with
      | (head, args) ->
          (match ((head.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar fv, uu___1::[]) ->
               let uu___2 =
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   PulseSyntaxExtension_Env.admit_lid in
               if uu___2
               then
                 let uu___3 = PulseSyntaxExtension_SyntaxWrapper.tm_admit r in
                 STTerm uu___3
               else
                 (let uu___4 =
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      PulseSyntaxExtension_Env.unreachable_lid in
                  if uu___4
                  then
                    let uu___5 =
                      PulseSyntaxExtension_SyntaxWrapper.tm_unreachable r in
                    STTerm uu___5
                  else Return s)
           | uu___1 -> Return s)
let (prepend_ctx_issue :
  FStar_Pprint.document -> FStar_Errors.issue -> FStar_Errors.issue) =
  fun c ->
    fun i ->
      {
        FStar_Errors.issue_msg = (c :: (i.FStar_Errors.issue_msg));
        FStar_Errors.issue_level = (i.FStar_Errors.issue_level);
        FStar_Errors.issue_range = (i.FStar_Errors.issue_range);
        FStar_Errors.issue_number = (i.FStar_Errors.issue_number);
        FStar_Errors.issue_ctx = (i.FStar_Errors.issue_ctx)
      }
let (tosyntax' :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Parser_AST.term ->
      FStar_Syntax_Syntax.term PulseSyntaxExtension_Err.err)
  =
  fun env ->
    fun t ->
      try
        (fun uu___ ->
           match () with
           | () ->
               let uu___1 =
                 FStar_ToSyntax_ToSyntax.desugar_term
                   env.PulseSyntaxExtension_Env.dsenv t in
               PulseSyntaxExtension_Err.return uu___1) ()
      with
      | uu___ ->
          let uu___1 = FStar_Errors.issue_of_exn uu___ in
          (match uu___1 with
           | FStar_Pervasives_Native.Some i ->
               let i1 =
                 let uu___2 =
                   FStar_Pprint.arbitrary_string
                     "Failed to desugar Pulse term" in
                 prepend_ctx_issue uu___2 i in
               (FStar_Errors.add_issues [i1];
                PulseSyntaxExtension_Err.just_fail ())
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 let uu___3 = FStar_Parser_AST.term_to_string t in
                 let uu___4 =
                   PulseSyntaxExtension_SyntaxWrapper.print_exn uu___ in
                 FStar_Compiler_Util.format2
                   "Failed to desugar Pulse term %s\nUnexpected exception: %s\n"
                   uu___3 uu___4 in
               PulseSyntaxExtension_Err.fail uu___2 t.FStar_Parser_AST.range)
let (tosyntax :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Parser_AST.term ->
      FStar_Syntax_Syntax.term PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun t ->
           let uu___ = tosyntax' env t in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang
                PulseSyntaxExtension_Err.err_monad () () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun s ->
                      let s = Obj.magic s in
                      Obj.magic (PulseSyntaxExtension_Err.return s)) uu___1)))
        uu___1 uu___
let (desugar_term :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Parser_AST.term ->
      PulseSyntaxExtension_SyntaxWrapper.term PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun t ->
           let uu___ = tosyntax env t in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang
                PulseSyntaxExtension_Err.err_monad () () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun s ->
                      let s = Obj.magic s in
                      let uu___1 = as_term s in
                      Obj.magic (PulseSyntaxExtension_Err.return uu___1))
                     uu___1))) uu___1 uu___
let (desugar_term_opt :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Parser_AST.term FStar_Pervasives_Native.option ->
      PulseSyntaxExtension_SyntaxWrapper.term PulseSyntaxExtension_Err.err)
  =
  fun env ->
    fun t ->
      match t with
      | FStar_Pervasives_Native.None ->
          let uu___ =
            PulseSyntaxExtension_SyntaxWrapper.tm_unknown
              FStar_Compiler_Range_Type.dummyRange in
          PulseSyntaxExtension_Err.return uu___
      | FStar_Pervasives_Native.Some e -> desugar_term env e
let (idents_as_binders :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Ident.ident Prims.list ->
      (PulseSyntaxExtension_Env.env_t *
        (PulseSyntaxExtension_SyntaxWrapper.qualifier
        FStar_Pervasives_Native.option *
        PulseSyntaxExtension_SyntaxWrapper.binder) Prims.list *
        FStar_Syntax_Syntax.bv Prims.list) PulseSyntaxExtension_Err.err)
  =
  fun env ->
    fun l ->
      let non_tick_idents =
        FStar_Compiler_List.filter
          (fun i ->
             let uu___ = FStar_Ident.string_of_id i in
             Prims.op_Negation (FStar_Compiler_Util.starts_with uu___ "'")) l in
      if (FStar_Compiler_List.length non_tick_idents) <> Prims.int_zero
      then
        let s =
          let uu___ =
            FStar_Compiler_List.map FStar_Ident.string_of_id non_tick_idents in
          FStar_Compiler_Util.concat_l ", " uu___ in
        let uu___ =
          FStar_Compiler_Util.format1
            "Identifiers (%s) not found, consider adding them as binders" s in
        let uu___1 =
          let uu___2 = FStar_Compiler_List.hd non_tick_idents in
          FStar_Ident.range_of_id uu___2 in
        PulseSyntaxExtension_Err.fail uu___ uu___1
      else
        (let erased_tm =
           FStar_Parser_AST.mk_term
             (FStar_Parser_AST.Var FStar_Parser_Const.erased_lid)
             FStar_Compiler_Range_Type.dummyRange FStar_Parser_AST.Un in
         let mk_ty i =
           let wild =
             let uu___1 = FStar_Ident.range_of_id i in
             FStar_Parser_AST.mk_term FStar_Parser_AST.Wild uu___1
               FStar_Parser_AST.Un in
           let uu___1 = FStar_Ident.range_of_id i in
           FStar_Parser_AST.mkApp erased_tm
             [(wild, FStar_Parser_AST.Nothing)] uu___1 in
         let rec aux uu___4 uu___3 uu___2 uu___1 =
           (fun env1 ->
              fun binders ->
                fun bvs ->
                  fun l1 ->
                    match l1 with
                    | [] ->
                        Obj.magic
                          (Obj.repr
                             (PulseSyntaxExtension_Err.return
                                (env1, (FStar_Compiler_List.rev binders),
                                  (FStar_Compiler_List.rev bvs))))
                    | i::l2 ->
                        Obj.magic
                          (Obj.repr
                             (let uu___1 =
                                PulseSyntaxExtension_Env.push_bv env1 i in
                              match uu___1 with
                              | (env2, bv) ->
                                  let qual =
                                    PulseSyntaxExtension_SyntaxWrapper.as_qual
                                      true in
                                  let ty = mk_ty i in
                                  let uu___2 = desugar_term env2 ty in
                                  FStar_Class_Monad.op_let_Bang
                                    PulseSyntaxExtension_Err.err_monad () ()
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun ty1 ->
                                          let ty1 = Obj.magic ty1 in
                                          let uu___3 =
                                            let uu___4 =
                                              let uu___5 =
                                                PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                                  i ty1 in
                                              (qual, uu___5) in
                                            uu___4 :: binders in
                                          Obj.magic
                                            (aux env2 uu___3 (bv :: bvs) l2))
                                         uu___3)))) uu___4 uu___3 uu___2
             uu___1 in
         aux env [] [] l)
let rec (interpret_slprop_constructors :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Syntax_Syntax.term ->
      PulseSyntaxExtension_SyntaxWrapper.term PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun v ->
           let uu___ = FStar_Syntax_Util.head_and_args_full v in
           match uu___ with
           | (head, args) ->
               (match ((head.FStar_Syntax_Syntax.n), args) with
                | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___1)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      PulseSyntaxExtension_Env.pure_lid
                    ->
                    Obj.magic
                      (Obj.repr
                         (let res =
                            let uu___2 = as_term l in
                            PulseSyntaxExtension_SyntaxWrapper.tm_pure uu___2
                              v.FStar_Syntax_Syntax.pos in
                          PulseSyntaxExtension_Err.return res))
                | (FStar_Syntax_Syntax.Tm_fvar fv, []) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      PulseSyntaxExtension_Env.emp_lid
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___1 =
                            PulseSyntaxExtension_SyntaxWrapper.tm_emp
                              v.FStar_Syntax_Syntax.pos in
                          PulseSyntaxExtension_Err.return uu___1))
                | (FStar_Syntax_Syntax.Tm_fvar fv,
                   (l, uu___1)::(r, uu___2)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      PulseSyntaxExtension_Env.star_lid
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___3 = interpret_slprop_constructors env l in
                          FStar_Class_Monad.op_let_Bang
                            PulseSyntaxExtension_Err.err_monad () ()
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun l1 ->
                                  let l1 = Obj.magic l1 in
                                  let uu___4 =
                                    interpret_slprop_constructors env r in
                                  Obj.magic
                                    (FStar_Class_Monad.op_let_Bang
                                       PulseSyntaxExtension_Err.err_monad ()
                                       () (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun r1 ->
                                             let r1 = Obj.magic r1 in
                                             let uu___5 =
                                               PulseSyntaxExtension_SyntaxWrapper.tm_star
                                                 l1 r1
                                                 v.FStar_Syntax_Syntax.pos in
                                             Obj.magic
                                               (PulseSyntaxExtension_Err.return
                                                  uu___5)) uu___5))) uu___4)))
                | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___1)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      PulseSyntaxExtension_Env.exists_lid
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            let uu___3 = FStar_Syntax_Subst.compress l in
                            uu___3.FStar_Syntax_Syntax.n in
                          match uu___2 with
                          | FStar_Syntax_Syntax.Tm_abs
                              { FStar_Syntax_Syntax.bs = b::[];
                                FStar_Syntax_Syntax.body = body;
                                FStar_Syntax_Syntax.rc_opt = uu___3;_}
                              ->
                              Obj.repr
                                (let b1 =
                                   let uu___4 =
                                     as_term
                                       (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                   PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                     (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname
                                     uu___4 in
                                 let uu___4 =
                                   interpret_slprop_constructors env body in
                                 FStar_Class_Monad.op_let_Bang
                                   PulseSyntaxExtension_Err.err_monad () ()
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      (fun body1 ->
                                         let body1 = Obj.magic body1 in
                                         let uu___5 =
                                           PulseSyntaxExtension_SyntaxWrapper.tm_exists
                                             b1 body1
                                             v.FStar_Syntax_Syntax.pos in
                                         Obj.magic
                                           (PulseSyntaxExtension_Err.return
                                              uu___5)) uu___5))
                          | uu___3 ->
                              Obj.repr
                                (let uu___4 = as_term v in
                                 PulseSyntaxExtension_Err.return uu___4)))
                | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___1)::[]) when
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      PulseSyntaxExtension_Env.forall_lid
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            let uu___3 = FStar_Syntax_Subst.compress l in
                            uu___3.FStar_Syntax_Syntax.n in
                          match uu___2 with
                          | FStar_Syntax_Syntax.Tm_abs
                              { FStar_Syntax_Syntax.bs = b::[];
                                FStar_Syntax_Syntax.body = body;
                                FStar_Syntax_Syntax.rc_opt = uu___3;_}
                              ->
                              Obj.repr
                                (let b1 =
                                   let uu___4 =
                                     as_term
                                       (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort in
                                   PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                     (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.ppname
                                     uu___4 in
                                 let uu___4 =
                                   interpret_slprop_constructors env body in
                                 FStar_Class_Monad.op_let_Bang
                                   PulseSyntaxExtension_Err.err_monad () ()
                                   (Obj.magic uu___4)
                                   (fun uu___5 ->
                                      (fun body1 ->
                                         let body1 = Obj.magic body1 in
                                         let uu___5 =
                                           PulseSyntaxExtension_SyntaxWrapper.tm_forall
                                             b1 body1
                                             v.FStar_Syntax_Syntax.pos in
                                         Obj.magic
                                           (PulseSyntaxExtension_Err.return
                                              uu___5)) uu___5))
                          | uu___3 ->
                              Obj.repr
                                (let uu___4 = as_term v in
                                 PulseSyntaxExtension_Err.return uu___4)))
                | (FStar_Syntax_Syntax.Tm_fvar fv, (l, uu___1)::[]) when
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       PulseSyntaxExtension_Env.prims_exists_lid)
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         PulseSyntaxExtension_Env.prims_forall_lid)
                    ->
                    Obj.magic
                      (Obj.repr
                         (PulseSyntaxExtension_Err.fail
                            "exists/forall are prop connectives; you probably meant to use exists*/forall*"
                            v.FStar_Syntax_Syntax.pos))
                | uu___1 ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = as_term v in
                          PulseSyntaxExtension_Err.return uu___2)))) uu___1
        uu___
let (desugar_slprop :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.slprop ->
      PulseSyntaxExtension_SyntaxWrapper.slprop PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun v ->
           match v.PulseSyntaxExtension_Sugar.v with
           | PulseSyntaxExtension_Sugar.SLPropTerm t ->
               let uu___ = tosyntax env t in
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang
                    PulseSyntaxExtension_Err.err_monad () ()
                    (Obj.magic uu___)
                    (fun uu___1 ->
                       (fun t1 ->
                          let t1 = Obj.magic t1 in
                          Obj.magic (interpret_slprop_constructors env t1))
                         uu___1))) uu___1 uu___
let (desugar_computation_type :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.computation_type ->
      PulseSyntaxExtension_SyntaxWrapper.comp PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun c ->
           let uu___ =
             desugar_slprop env c.PulseSyntaxExtension_Sugar.precondition in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang
                PulseSyntaxExtension_Err.err_monad () () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun pre ->
                      let pre = Obj.magic pre in
                      let uu___1 =
                        desugar_term env
                          c.PulseSyntaxExtension_Sugar.return_type in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang
                           PulseSyntaxExtension_Err.err_monad () ()
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun ret1 ->
                                 let ret1 = Obj.magic ret1 in
                                 let uu___2 =
                                   match c.PulseSyntaxExtension_Sugar.opens
                                   with
                                   | FStar_Pervasives_Native.Some t ->
                                       desugar_term env t
                                   | FStar_Pervasives_Native.None ->
                                       PulseSyntaxExtension_Err.return
                                         PulseSyntaxExtension_SyntaxWrapper.tm_emp_inames in
                                 Obj.magic
                                   (FStar_Class_Monad.op_let_Bang
                                      PulseSyntaxExtension_Err.err_monad ()
                                      () (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun opens ->
                                            let opens = Obj.magic opens in
                                            let uu___3 =
                                              PulseSyntaxExtension_Env.push_bv
                                                env
                                                c.PulseSyntaxExtension_Sugar.return_name in
                                            match uu___3 with
                                            | (env1, bv) ->
                                                let uu___4 =
                                                  desugar_slprop env1
                                                    c.PulseSyntaxExtension_Sugar.postcondition in
                                                Obj.magic
                                                  (FStar_Class_Monad.op_let_Bang
                                                     PulseSyntaxExtension_Err.err_monad
                                                     () () (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun post ->
                                                           let post =
                                                             Obj.magic post in
                                                           let post1 =
                                                             PulseSyntaxExtension_SyntaxWrapper.close_term
                                                               post
                                                               bv.FStar_Syntax_Syntax.index in
                                                           match c.PulseSyntaxExtension_Sugar.tag
                                                           with
                                                           | PulseSyntaxExtension_Sugar.ST
                                                               ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    let uu___5
                                                                    =
                                                                    if
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    c.PulseSyntaxExtension_Sugar.opens
                                                                    then
                                                                    PulseSyntaxExtension_Err.fail
                                                                    "STT computations are not indexed by invariants. Either remove the `opens` or make this function ghost/atomic."
                                                                    (FStar_Pervasives_Native.__proj__Some__item__v
                                                                    c.PulseSyntaxExtension_Sugar.opens).FStar_Parser_AST.range
                                                                    else
                                                                    PulseSyntaxExtension_Err.return
                                                                    () in
                                                                    FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    uu___5
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    uu___6 in
                                                                    let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                                                    c.PulseSyntaxExtension_Sugar.return_name
                                                                    ret1 in
                                                                    PulseSyntaxExtension_SyntaxWrapper.mk_comp
                                                                    pre
                                                                    uu___8
                                                                    post1 in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    uu___7))
                                                                    uu___6)))
                                                           | PulseSyntaxExtension_Sugar.STAtomic
                                                               ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    let uu___5
                                                                    =
                                                                    let uu___6
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                                                    c.PulseSyntaxExtension_Sugar.return_name
                                                                    ret1 in
                                                                    PulseSyntaxExtension_SyntaxWrapper.atomic_comp
                                                                    opens pre
                                                                    uu___6
                                                                    post1 in
                                                                    PulseSyntaxExtension_Err.return
                                                                    uu___5))
                                                           | PulseSyntaxExtension_Sugar.STGhost
                                                               ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    let uu___5
                                                                    =
                                                                    let uu___6
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                                                    c.PulseSyntaxExtension_Sugar.return_name
                                                                    ret1 in
                                                                    PulseSyntaxExtension_SyntaxWrapper.ghost_comp
                                                                    opens pre
                                                                    uu___6
                                                                    post1 in
                                                                    PulseSyntaxExtension_Err.return
                                                                    uu___5)))
                                                          uu___5))) uu___3)))
                                uu___2))) uu___1))) uu___1 uu___
let (mk_totbind :
  PulseSyntaxExtension_SyntaxWrapper.binder ->
    PulseSyntaxExtension_SyntaxWrapper.term ->
      PulseSyntaxExtension_SyntaxWrapper.st_term ->
        PulseSyntaxExtension_SyntaxWrapper.range ->
          PulseSyntaxExtension_SyntaxWrapper.st_term)
  =
  fun b ->
    fun s1 ->
      fun s2 ->
        fun r -> PulseSyntaxExtension_SyntaxWrapper.tm_totbind b s1 s2 r
let (mk_bind :
  PulseSyntaxExtension_SyntaxWrapper.binder ->
    PulseSyntaxExtension_SyntaxWrapper.st_term ->
      PulseSyntaxExtension_SyntaxWrapper.st_term ->
        PulseSyntaxExtension_SyntaxWrapper.range ->
          PulseSyntaxExtension_SyntaxWrapper.st_term)
  =
  fun b ->
    fun s1 ->
      fun s2 -> fun r -> PulseSyntaxExtension_SyntaxWrapper.tm_bind b s1 s2 r
let (explicit_rvalues :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.stmt -> PulseSyntaxExtension_Sugar.stmt)
  = fun env -> fun s -> s
type qual =
  PulseSyntaxExtension_SyntaxWrapper.qualifier FStar_Pervasives_Native.option
let (as_qual :
  FStar_Parser_AST.aqual ->
    FStar_Compiler_Range_Type.range -> qual PulseSyntaxExtension_Err.err)
  =
  fun q ->
    fun rng ->
      match q with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) ->
          let uu___ = PulseSyntaxExtension_SyntaxWrapper.as_qual true in
          PulseSyntaxExtension_Err.return uu___
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.TypeClassArg) ->
          PulseSyntaxExtension_Err.return
            PulseSyntaxExtension_SyntaxWrapper.tc_qual
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          PulseSyntaxExtension_Err.fail
            "Pulse does not yet support meta arguments" rng
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) ->
          PulseSyntaxExtension_Err.fail
            "Pulse does not yet support equality arguments" rng
      | FStar_Pervasives_Native.None ->
          let uu___ = PulseSyntaxExtension_SyntaxWrapper.as_qual false in
          PulseSyntaxExtension_Err.return uu___
let (desugar_tac_opt :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Parser_AST.term FStar_Pervasives_Native.option ->
      PulseSyntaxExtension_SyntaxWrapper.term FStar_Pervasives_Native.option
        PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun topt ->
           match topt with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (Obj.repr
                    (PulseSyntaxExtension_Err.return
                       FStar_Pervasives_Native.None))
           | FStar_Pervasives_Native.Some t ->
               Obj.magic
                 (Obj.repr
                    (let tactics_module_lid =
                       FStar_Ident.lid_of_str "FStar.Tactics.V2" in
                     let env1 =
                       PulseSyntaxExtension_Env.push_namespace env
                         tactics_module_lid in
                     let uu___ = desugar_term env1 t in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun t1 ->
                             let t1 = Obj.magic t1 in
                             Obj.magic
                               (PulseSyntaxExtension_Err.return
                                  (FStar_Pervasives_Native.Some t1))) uu___1))))
        uu___1 uu___
let (desugar_hint_type :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.hint_type ->
      PulseSyntaxExtension_SyntaxWrapper.hint_type
        PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun ht ->
           match ht with
           | PulseSyntaxExtension_Sugar.ASSERT vp ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_slprop env vp in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun vp1 ->
                             let vp1 = Obj.magic vp1 in
                             let uu___1 =
                               PulseSyntaxExtension_SyntaxWrapper.mk_assert_hint_type
                                 vp1 in
                             Obj.magic
                               (PulseSyntaxExtension_Err.return uu___1))
                            uu___1)))
           | PulseSyntaxExtension_Sugar.UNFOLD (ns, vp) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_slprop env vp in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun vp1 ->
                             let vp1 = Obj.magic vp1 in
                             let uu___1 =
                               PulseSyntaxExtension_Env.resolve_names env ns in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun ns1 ->
                                        let ns1 = Obj.magic ns1 in
                                        let ns2 =
                                          FStar_Compiler_Util.map_opt ns1
                                            (FStar_Compiler_List.map
                                               FStar_Ident.string_of_lid) in
                                        let uu___2 =
                                          PulseSyntaxExtension_SyntaxWrapper.mk_unfold_hint_type
                                            ns2 vp1 in
                                        Obj.magic
                                          (PulseSyntaxExtension_Err.return
                                             uu___2)) uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.FOLD (ns, vp) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_slprop env vp in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun vp1 ->
                             let vp1 = Obj.magic vp1 in
                             let uu___1 =
                               PulseSyntaxExtension_Env.resolve_names env ns in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun ns1 ->
                                        let ns1 = Obj.magic ns1 in
                                        let ns2 =
                                          FStar_Compiler_Util.map_opt ns1
                                            (FStar_Compiler_List.map
                                               FStar_Ident.string_of_lid) in
                                        let uu___2 =
                                          PulseSyntaxExtension_SyntaxWrapper.mk_fold_hint_type
                                            ns2 vp1 in
                                        Obj.magic
                                          (PulseSyntaxExtension_Err.return
                                             uu___2)) uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.RENAME (pairs, goal, tac_opt) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       Obj.magic
                         (FStar_Class_Monad.mapM
                            PulseSyntaxExtension_Err.err_monad () ()
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  let uu___1 = Obj.magic uu___1 in
                                  match uu___1 with
                                  | (t1, t2) ->
                                      let uu___2 = desugar_term env t1 in
                                      Obj.magic
                                        (FStar_Class_Monad.op_let_Bang
                                           PulseSyntaxExtension_Err.err_monad
                                           () () (Obj.magic uu___2)
                                           (fun uu___3 ->
                                              (fun t11 ->
                                                 let t11 = Obj.magic t11 in
                                                 let uu___3 =
                                                   desugar_term env t2 in
                                                 Obj.magic
                                                   (FStar_Class_Monad.op_let_Bang
                                                      PulseSyntaxExtension_Err.err_monad
                                                      () ()
                                                      (Obj.magic uu___3)
                                                      (fun uu___4 ->
                                                         (fun t21 ->
                                                            let t21 =
                                                              Obj.magic t21 in
                                                            Obj.magic
                                                              (PulseSyntaxExtension_Err.return
                                                                 (t11, t21)))
                                                           uu___4))) uu___3)))
                                 uu___1) (Obj.magic pairs)) in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun pairs1 ->
                             let pairs1 = Obj.magic pairs1 in
                             let uu___1 =
                               PulseSyntaxExtension_Err.map_err_opt
                                 (desugar_slprop env) goal in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun goal1 ->
                                        let goal1 = Obj.magic goal1 in
                                        let uu___2 =
                                          desugar_tac_opt env tac_opt in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun tac_opt1 ->
                                                   let tac_opt1 =
                                                     Obj.magic tac_opt1 in
                                                   let uu___3 =
                                                     PulseSyntaxExtension_SyntaxWrapper.mk_rename_hint_type
                                                       pairs1 goal1 tac_opt1 in
                                                   Obj.magic
                                                     (PulseSyntaxExtension_Err.return
                                                        uu___3)) uu___3)))
                                       uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.REWRITE (t1, t2, tac_opt) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_slprop env t1 in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun t11 ->
                             let t11 = Obj.magic t11 in
                             let uu___1 = desugar_slprop env t2 in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun t21 ->
                                        let t21 = Obj.magic t21 in
                                        let uu___2 =
                                          desugar_tac_opt env tac_opt in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun tac_opt1 ->
                                                   let tac_opt1 =
                                                     Obj.magic tac_opt1 in
                                                   let uu___3 =
                                                     PulseSyntaxExtension_SyntaxWrapper.mk_rewrite_hint_type
                                                       t11 t21 tac_opt1 in
                                                   Obj.magic
                                                     (PulseSyntaxExtension_Err.return
                                                        uu___3)) uu___3)))
                                       uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.WILD ->
               Obj.magic
                 (Obj.repr
                    (PulseSyntaxExtension_Err.return
                       PulseSyntaxExtension_SyntaxWrapper.mk_wild_hint_type))
           | PulseSyntaxExtension_Sugar.SHOW_PROOF_STATE r ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       PulseSyntaxExtension_SyntaxWrapper.mk_show_proof_state_hint_type
                         r in
                     PulseSyntaxExtension_Err.return uu___))) uu___1 uu___
let (desugar_datacon :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Ident.lid ->
      PulseSyntaxExtension_SyntaxWrapper.fv PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun l ->
           let rng = FStar_Ident.range_of_lid l in
           let t =
             FStar_Parser_AST.mk_term (FStar_Parser_AST.Name l) rng
               FStar_Parser_AST.Expr in
           let uu___ = tosyntax env t in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang
                PulseSyntaxExtension_Err.err_monad () () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun tt ->
                      let tt = Obj.magic tt in
                      let uu___1 =
                        let uu___2 =
                          let uu___3 = FStar_Syntax_Subst.compress tt in
                          uu___3.FStar_Syntax_Syntax.n in
                        match uu___2 with
                        | FStar_Syntax_Syntax.Tm_fvar fv ->
                            PulseSyntaxExtension_Err.return fv
                        | FStar_Syntax_Syntax.Tm_uinst
                            ({
                               FStar_Syntax_Syntax.n =
                                 FStar_Syntax_Syntax.Tm_fvar fv;
                               FStar_Syntax_Syntax.pos = uu___3;
                               FStar_Syntax_Syntax.vars = uu___4;
                               FStar_Syntax_Syntax.hash_code = uu___5;_},
                             uu___6)
                            -> PulseSyntaxExtension_Err.return fv
                        | uu___3 ->
                            let uu___4 =
                              let uu___5 = FStar_Ident.string_of_lid l in
                              FStar_Compiler_Util.format1 "Not a datacon? %s"
                                uu___5 in
                            PulseSyntaxExtension_Err.fail uu___4 rng in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang
                           PulseSyntaxExtension_Err.err_monad () ()
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun sfv ->
                                 let sfv = Obj.magic sfv in
                                 let uu___2 =
                                   let uu___3 =
                                     FStar_Syntax_Syntax.lid_of_fv sfv in
                                   PulseSyntaxExtension_SyntaxWrapper.mk_fv
                                     uu___3 rng in
                                 Obj.magic
                                   (PulseSyntaxExtension_Err.return uu___2))
                                uu___2))) uu___1))) uu___1 uu___
let rec (desugar_stmt :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.stmt ->
      PulseSyntaxExtension_SyntaxWrapper.st_term PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun s ->
           match s.PulseSyntaxExtension_Sugar.s with
           | PulseSyntaxExtension_Sugar.Expr
               { PulseSyntaxExtension_Sugar.e = e;_} ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = tosyntax env e in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun tm ->
                             let tm = Obj.magic tm in
                             let uu___1 =
                               let uu___2 = admit_or_return env tm in
                               st_term_of_admit_or_return uu___2 in
                             Obj.magic
                               (PulseSyntaxExtension_Err.return uu___1))
                            uu___1)))
           | PulseSyntaxExtension_Sugar.Assignment
               { PulseSyntaxExtension_Sugar.lhs = lhs;
                 PulseSyntaxExtension_Sugar.value = value;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = tosyntax env lhs in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun lhs1 ->
                             let lhs1 = Obj.magic lhs1 in
                             let uu___1 = tosyntax env value in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun rhs ->
                                        let rhs = Obj.magic rhs in
                                        let uu___2 =
                                          let uu___3 =
                                            PulseSyntaxExtension_Env.op_colon_equals_lid
                                              s.PulseSyntaxExtension_Sugar.range1 in
                                          PulseSyntaxExtension_Env.resolve_lid
                                            env uu___3 in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun assignment_lid ->
                                                   let assignment_lid =
                                                     Obj.magic assignment_lid in
                                                   let uu___3 =
                                                     stapp_assignment
                                                       assignment_lid 
                                                       [lhs1] rhs
                                                       s.PulseSyntaxExtension_Sugar.range1 in
                                                   Obj.magic
                                                     (PulseSyntaxExtension_Err.return
                                                        uu___3)) uu___3)))
                                       uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.ArrayAssignment
               { PulseSyntaxExtension_Sugar.arr = arr;
                 PulseSyntaxExtension_Sugar.index = index;
                 PulseSyntaxExtension_Sugar.value1 = value;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = tosyntax env arr in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun arr1 ->
                             let arr1 = Obj.magic arr1 in
                             let uu___1 = tosyntax env index in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun index1 ->
                                        let index1 = Obj.magic index1 in
                                        let uu___2 = tosyntax env value in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun value1 ->
                                                   let value1 =
                                                     Obj.magic value1 in
                                                   let uu___3 =
                                                     let uu___4 =
                                                       PulseSyntaxExtension_Env.op_array_assignment_lid
                                                         s.PulseSyntaxExtension_Sugar.range1 in
                                                     PulseSyntaxExtension_Env.resolve_lid
                                                       env uu___4 in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        PulseSyntaxExtension_Err.err_monad
                                                        () ()
                                                        (Obj.magic uu___3)
                                                        (fun uu___4 ->
                                                           (fun
                                                              array_assignment_lid
                                                              ->
                                                              let array_assignment_lid
                                                                =
                                                                Obj.magic
                                                                  array_assignment_lid in
                                                              let uu___4 =
                                                                stapp_assignment
                                                                  array_assignment_lid
                                                                  [arr1;
                                                                  index1]
                                                                  value1
                                                                  s.PulseSyntaxExtension_Sugar.range1 in
                                                              Obj.magic
                                                                (PulseSyntaxExtension_Err.return
                                                                   uu___4))
                                                             uu___4))) uu___3)))
                                       uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.Sequence
               {
                 PulseSyntaxExtension_Sugar.s1 =
                   {
                     PulseSyntaxExtension_Sugar.s =
                       PulseSyntaxExtension_Sugar.Open l;
                     PulseSyntaxExtension_Sugar.range1 = range;_};
                 PulseSyntaxExtension_Sugar.s2 = s2;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       try
                         (fun uu___1 ->
                            match () with
                            | () ->
                                let env1 =
                                  PulseSyntaxExtension_Env.push_namespace env
                                    l in
                                PulseSyntaxExtension_Err.return env1) ()
                       with
                       | FStar_Errors.Error (e, msg, r, ctx) ->
                           let uu___2 =
                             let uu___3 = FStar_Ident.string_of_lid l in
                             let uu___4 = FStar_Ident.string_of_lid l in
                             FStar_Compiler_Util.format2
                               "Failed to open namespace %s; You may need to bind this namespace outside Pulse for the F* dependency scanner to pick it up, e.g., write ``module _X = %s`` in F*"
                               uu___3 uu___4 in
                           PulseSyntaxExtension_Err.fail uu___2 range in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun env1 ->
                             let env1 = Obj.magic env1 in
                             Obj.magic (desugar_stmt env1 s2)) uu___1)))
           | PulseSyntaxExtension_Sugar.Sequence
               {
                 PulseSyntaxExtension_Sugar.s1 =
                   {
                     PulseSyntaxExtension_Sugar.s =
                       PulseSyntaxExtension_Sugar.LetBinding lb;
                     PulseSyntaxExtension_Sugar.range1 = uu___;_};
                 PulseSyntaxExtension_Sugar.s2 = s2;_}
               ->
               Obj.magic
                 (Obj.repr
                    (desugar_bind env lb s2
                       s.PulseSyntaxExtension_Sugar.range1))
           | PulseSyntaxExtension_Sugar.ProofHintWithBinders uu___ ->
               Obj.magic
                 (Obj.repr
                    (desugar_proof_hint_with_binders env s
                       FStar_Pervasives_Native.None
                       s.PulseSyntaxExtension_Sugar.range1))
           | PulseSyntaxExtension_Sugar.Sequence
               { PulseSyntaxExtension_Sugar.s1 = s1;
                 PulseSyntaxExtension_Sugar.s2 = s2;_}
               when
               PulseSyntaxExtension_Sugar.uu___is_ProofHintWithBinders
                 s1.PulseSyntaxExtension_Sugar.s
               ->
               Obj.magic
                 (Obj.repr
                    (desugar_proof_hint_with_binders env s1
                       (FStar_Pervasives_Native.Some s2)
                       s1.PulseSyntaxExtension_Sugar.range1))
           | PulseSyntaxExtension_Sugar.Sequence
               { PulseSyntaxExtension_Sugar.s1 = s1;
                 PulseSyntaxExtension_Sugar.s2 = s2;_}
               ->
               Obj.magic
                 (Obj.repr
                    (desugar_sequence env s1 s2
                       s.PulseSyntaxExtension_Sugar.range1))
           | PulseSyntaxExtension_Sugar.Block
               { PulseSyntaxExtension_Sugar.stmt = stmt;_} ->
               Obj.magic (Obj.repr (desugar_stmt env stmt))
           | PulseSyntaxExtension_Sugar.If
               { PulseSyntaxExtension_Sugar.head1 = head;
                 PulseSyntaxExtension_Sugar.join_slprop = join_slprop;
                 PulseSyntaxExtension_Sugar.then_ = then_;
                 PulseSyntaxExtension_Sugar.else_opt = else_opt;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_term env head in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun head1 ->
                             let head1 = Obj.magic head1 in
                             let uu___1 =
                               match join_slprop with
                               | FStar_Pervasives_Native.None ->
                                   Obj.magic
                                     (Obj.repr
                                        (PulseSyntaxExtension_Err.return
                                           FStar_Pervasives_Native.None))
                               | FStar_Pervasives_Native.Some
                                   (FStar_Pervasives_Native.None, t, _opens)
                                   ->
                                   Obj.magic
                                     (Obj.repr
                                        (let uu___2 = desugar_slprop env t in
                                         FStar_Class_Monad.op_let_Bang
                                           PulseSyntaxExtension_Err.err_monad
                                           () () (Obj.magic uu___2)
                                           (fun uu___3 ->
                                              (fun vp ->
                                                 let vp = Obj.magic vp in
                                                 Obj.magic
                                                   (PulseSyntaxExtension_Err.return
                                                      (FStar_Pervasives_Native.Some
                                                         vp))) uu___3))) in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun join_slprop1 ->
                                        let join_slprop1 =
                                          Obj.magic join_slprop1 in
                                        let uu___2 = desugar_stmt env then_ in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun then_1 ->
                                                   let then_1 =
                                                     Obj.magic then_1 in
                                                   let uu___3 =
                                                     match else_opt with
                                                     | FStar_Pervasives_Native.None
                                                         ->
                                                         let uu___4 =
                                                           let uu___5 =
                                                             PulseSyntaxExtension_SyntaxWrapper.tm_expr
                                                               FStar_Syntax_Syntax.unit_const
                                                               FStar_Compiler_Range_Type.dummyRange in
                                                           PulseSyntaxExtension_SyntaxWrapper.tm_return
                                                             uu___5
                                                             FStar_Compiler_Range_Type.dummyRange in
                                                         PulseSyntaxExtension_Err.return
                                                           uu___4
                                                     | FStar_Pervasives_Native.Some
                                                         e ->
                                                         desugar_stmt env e in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        PulseSyntaxExtension_Err.err_monad
                                                        () ()
                                                        (Obj.magic uu___3)
                                                        (fun uu___4 ->
                                                           (fun else_ ->
                                                              let else_ =
                                                                Obj.magic
                                                                  else_ in
                                                              let uu___4 =
                                                                PulseSyntaxExtension_SyntaxWrapper.tm_if
                                                                  head1
                                                                  join_slprop1
                                                                  then_1
                                                                  else_
                                                                  s.PulseSyntaxExtension_Sugar.range1 in
                                                              Obj.magic
                                                                (PulseSyntaxExtension_Err.return
                                                                   uu___4))
                                                             uu___4))) uu___3)))
                                       uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.Match
               { PulseSyntaxExtension_Sugar.head2 = head;
                 PulseSyntaxExtension_Sugar.returns_annot = returns_annot;
                 PulseSyntaxExtension_Sugar.branches = branches;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_term env head in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun head1 ->
                             let head1 = Obj.magic head1 in
                             let uu___1 =
                               PulseSyntaxExtension_Err.map_err_opt
                                 (fun uu___2 ->
                                    match uu___2 with
                                    | (uu___3, t, _opens) ->
                                        desugar_slprop env t) returns_annot in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun returns_annot1 ->
                                        let returns_annot1 =
                                          Obj.magic returns_annot1 in
                                        let uu___2 =
                                          Obj.magic
                                            (FStar_Class_Monad.mapM
                                               PulseSyntaxExtension_Err.err_monad
                                               () ()
                                               (fun uu___3 ->
                                                  (Obj.magic
                                                     (desugar_branch env))
                                                    uu___3)
                                               (Obj.magic branches)) in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun branches1 ->
                                                   let branches1 =
                                                     Obj.magic branches1 in
                                                   let uu___3 =
                                                     PulseSyntaxExtension_SyntaxWrapper.tm_match
                                                       head1 returns_annot1
                                                       branches1
                                                       s.PulseSyntaxExtension_Sugar.range1 in
                                                   Obj.magic
                                                     (PulseSyntaxExtension_Err.return
                                                        uu___3)) uu___3)))
                                       uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.While
               { PulseSyntaxExtension_Sugar.guard = guard;
                 PulseSyntaxExtension_Sugar.id1 = id;
                 PulseSyntaxExtension_Sugar.invariant = invariant;
                 PulseSyntaxExtension_Sugar.body = body;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_stmt env guard in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun guard1 ->
                             let guard1 = Obj.magic guard1 in
                             let uu___1 =
                               let uu___2 =
                                 PulseSyntaxExtension_Env.push_bv env id in
                               match uu___2 with
                               | (env1, bv) ->
                                   let uu___3 = desugar_slprop env1 invariant in
                                   Obj.magic
                                     (FStar_Class_Monad.op_let_Bang
                                        PulseSyntaxExtension_Err.err_monad ()
                                        () (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           (fun inv ->
                                              let inv = Obj.magic inv in
                                              let uu___4 =
                                                PulseSyntaxExtension_SyntaxWrapper.close_term
                                                  inv
                                                  bv.FStar_Syntax_Syntax.index in
                                              Obj.magic
                                                (PulseSyntaxExtension_Err.return
                                                   uu___4)) uu___4)) in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun invariant1 ->
                                        let invariant1 = Obj.magic invariant1 in
                                        let uu___2 = desugar_stmt env body in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun body1 ->
                                                   let body1 =
                                                     Obj.magic body1 in
                                                   let uu___3 =
                                                     PulseSyntaxExtension_SyntaxWrapper.tm_while
                                                       guard1
                                                       (id, invariant1) body1
                                                       s.PulseSyntaxExtension_Sugar.range1 in
                                                   Obj.magic
                                                     (PulseSyntaxExtension_Err.return
                                                        uu___3)) uu___3)))
                                       uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.Introduce
               { PulseSyntaxExtension_Sugar.slprop = slprop;
                 PulseSyntaxExtension_Sugar.witnesses = witnesses;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_slprop env slprop in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun vp ->
                             let vp = Obj.magic vp in
                             let uu___1 =
                               let uu___2 =
                                 let uu___3 =
                                   PulseSyntaxExtension_SyntaxWrapper.is_tm_exists
                                     vp in
                                 Prims.op_Negation uu___3 in
                               PulseSyntaxExtension_Err.fail_if uu___2
                                 "introduce expects an existential formula"
                                 s.PulseSyntaxExtension_Sugar.range1 in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  uu___1
                                  (fun uu___2 ->
                                     (fun uu___2 ->
                                        let uu___2 = Obj.magic uu___2 in
                                        let uu___3 =
                                          Obj.magic
                                            (FStar_Class_Monad.mapM
                                               PulseSyntaxExtension_Err.err_monad
                                               () ()
                                               (fun uu___4 ->
                                                  (Obj.magic
                                                     (desugar_term env))
                                                    uu___4)
                                               (Obj.magic witnesses)) in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                (fun witnesses1 ->
                                                   let witnesses1 =
                                                     Obj.magic witnesses1 in
                                                   let uu___4 =
                                                     PulseSyntaxExtension_SyntaxWrapper.tm_intro_exists
                                                       vp witnesses1
                                                       s.PulseSyntaxExtension_Sugar.range1 in
                                                   Obj.magic
                                                     (PulseSyntaxExtension_Err.return
                                                        uu___4)) uu___4)))
                                       uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.Parallel
               { PulseSyntaxExtension_Sugar.p1 = p1;
                 PulseSyntaxExtension_Sugar.p2 = p2;
                 PulseSyntaxExtension_Sugar.q1 = q1;
                 PulseSyntaxExtension_Sugar.q2 = q2;
                 PulseSyntaxExtension_Sugar.b1 = b1;
                 PulseSyntaxExtension_Sugar.b2 = b2;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_slprop env p1 in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun p11 ->
                             let p11 = Obj.magic p11 in
                             let uu___1 = desugar_slprop env p2 in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun p21 ->
                                        let p21 = Obj.magic p21 in
                                        let uu___2 = desugar_slprop env q1 in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun q11 ->
                                                   let q11 = Obj.magic q11 in
                                                   let uu___3 =
                                                     desugar_slprop env q2 in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        PulseSyntaxExtension_Err.err_monad
                                                        () ()
                                                        (Obj.magic uu___3)
                                                        (fun uu___4 ->
                                                           (fun q21 ->
                                                              let q21 =
                                                                Obj.magic q21 in
                                                              let uu___4 =
                                                                desugar_stmt
                                                                  env b1 in
                                                              Obj.magic
                                                                (FStar_Class_Monad.op_let_Bang
                                                                   PulseSyntaxExtension_Err.err_monad
                                                                   () ()
                                                                   (Obj.magic
                                                                    uu___4)
                                                                   (fun
                                                                    uu___5 ->
                                                                    (fun b11
                                                                    ->
                                                                    let b11 =
                                                                    Obj.magic
                                                                    b11 in
                                                                    let uu___5
                                                                    =
                                                                    desugar_stmt
                                                                    env b2 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun b21
                                                                    ->
                                                                    let b21 =
                                                                    Obj.magic
                                                                    b21 in
                                                                    let uu___6
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_par
                                                                    p11 p21
                                                                    q11 q21
                                                                    b11 b21
                                                                    s.PulseSyntaxExtension_Sugar.range1 in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    uu___6))
                                                                    uu___6)))
                                                                    uu___5)))
                                                             uu___4))) uu___3)))
                                       uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.LetBinding uu___ ->
               Obj.magic
                 (Obj.repr
                    (PulseSyntaxExtension_Err.fail "Terminal let binding"
                       s.PulseSyntaxExtension_Sugar.range1))
           | PulseSyntaxExtension_Sugar.WithInvariants
               { PulseSyntaxExtension_Sugar.names = n1::names;
                 PulseSyntaxExtension_Sugar.body1 = body;
                 PulseSyntaxExtension_Sugar.returns_ = returns_;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = tosyntax env n1 in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun n11 ->
                             let n11 = Obj.magic n11 in
                             let uu___1 =
                               Obj.magic
                                 (FStar_Class_Monad.mapM
                                    PulseSyntaxExtension_Err.err_monad () ()
                                    (fun uu___2 ->
                                       (Obj.magic (tosyntax env)) uu___2)
                                    (Obj.magic names)) in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun names1 ->
                                        let names1 = Obj.magic names1 in
                                        let uu___2 = desugar_stmt env body in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun body1 ->
                                                   let body1 =
                                                     Obj.magic body1 in
                                                   let uu___3 =
                                                     let opens_tm opens_opt =
                                                       match opens_opt with
                                                       | FStar_Pervasives_Native.Some
                                                           opens ->
                                                           desugar_term env
                                                             opens
                                                       | FStar_Pervasives_Native.None
                                                           ->
                                                           let all_names =
                                                             n11 :: names1 in
                                                           let opens_tm1 =
                                                             FStar_Compiler_List.fold_left
                                                               (fun names2 ->
                                                                  fun n ->
                                                                    let uu___4
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_expr
                                                                    n
                                                                    s.PulseSyntaxExtension_Sugar.range1 in
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_add_inv
                                                                    names2
                                                                    uu___4
                                                                    s.PulseSyntaxExtension_Sugar.range1)
                                                               PulseSyntaxExtension_SyntaxWrapper.tm_emp_inames
                                                               all_names in
                                                           PulseSyntaxExtension_Err.return
                                                             opens_tm1 in
                                                     match returns_ with
                                                     | FStar_Pervasives_Native.None
                                                         ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (PulseSyntaxExtension_Err.return
                                                                 FStar_Pervasives_Native.None))
                                                     | FStar_Pervasives_Native.Some
                                                         (FStar_Pervasives_Native.None,
                                                          v, opens_opt)
                                                         ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (let uu___4 =
                                                                 desugar_slprop
                                                                   env v in
                                                               FStar_Class_Monad.op_let_Bang
                                                                 PulseSyntaxExtension_Err.err_monad
                                                                 () ()
                                                                 (Obj.magic
                                                                    uu___4)
                                                                 (fun uu___5
                                                                    ->
                                                                    (fun v1
                                                                    ->
                                                                    let v1 =
                                                                    Obj.magic
                                                                    v1 in
                                                                    let b =
                                                                    let uu___5
                                                                    =
                                                                    FStar_Ident.id_of_text
                                                                    "_" in
                                                                    let uu___6
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_unknown
                                                                    s.PulseSyntaxExtension_Sugar.range1 in
                                                                    PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                                                    uu___5
                                                                    uu___6 in
                                                                    let uu___5
                                                                    =
                                                                    opens_tm
                                                                    opens_opt in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    opens ->
                                                                    let opens
                                                                    =
                                                                    Obj.magic
                                                                    opens in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    (FStar_Pervasives_Native.Some
                                                                    (b, v1,
                                                                    opens))))
                                                                    uu___6)))
                                                                    uu___5)))
                                                     | FStar_Pervasives_Native.Some
                                                         (FStar_Pervasives_Native.Some
                                                          (x, t), v,
                                                          opens_opt)
                                                         ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (let uu___4 =
                                                                 desugar_term
                                                                   env t in
                                                               FStar_Class_Monad.op_let_Bang
                                                                 PulseSyntaxExtension_Err.err_monad
                                                                 () ()
                                                                 (Obj.magic
                                                                    uu___4)
                                                                 (fun uu___5
                                                                    ->
                                                                    (fun t1
                                                                    ->
                                                                    let t1 =
                                                                    Obj.magic
                                                                    t1 in
                                                                    let uu___5
                                                                    =
                                                                    PulseSyntaxExtension_Env.push_bv
                                                                    env x in
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (env1,
                                                                    bv) ->
                                                                    let uu___6
                                                                    =
                                                                    desugar_slprop
                                                                    env1 v in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun v1
                                                                    ->
                                                                    let v1 =
                                                                    Obj.magic
                                                                    v1 in
                                                                    let v2 =
                                                                    PulseSyntaxExtension_SyntaxWrapper.close_term
                                                                    v1
                                                                    bv.FStar_Syntax_Syntax.index in
                                                                    let b =
                                                                    PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                                                    x t1 in
                                                                    let uu___7
                                                                    =
                                                                    opens_tm
                                                                    opens_opt in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    opens ->
                                                                    let opens
                                                                    =
                                                                    Obj.magic
                                                                    opens in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    (FStar_Pervasives_Native.Some
                                                                    (b, v2,
                                                                    opens))))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___5))) in
                                                   Obj.magic
                                                     (FStar_Class_Monad.op_let_Bang
                                                        PulseSyntaxExtension_Err.err_monad
                                                        () ()
                                                        (Obj.magic uu___3)
                                                        (fun uu___4 ->
                                                           (fun returns_1 ->
                                                              let returns_1 =
                                                                Obj.magic
                                                                  returns_1 in
                                                              let tt =
                                                                FStar_Compiler_List.fold_right
                                                                  (fun nm ->
                                                                    fun body2
                                                                    ->
                                                                    let nm1 =
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_expr
                                                                    nm
                                                                    s.PulseSyntaxExtension_Sugar.range1 in
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_with_inv
                                                                    nm1 body2
                                                                    FStar_Pervasives_Native.None
                                                                    s.PulseSyntaxExtension_Sugar.range1)
                                                                  names1
                                                                  body1 in
                                                              let n12 =
                                                                PulseSyntaxExtension_SyntaxWrapper.tm_expr
                                                                  n11
                                                                  s.PulseSyntaxExtension_Sugar.range1 in
                                                              let uu___4 =
                                                                PulseSyntaxExtension_SyntaxWrapper.tm_with_inv
                                                                  n12 tt
                                                                  returns_1
                                                                  s.PulseSyntaxExtension_Sugar.range1 in
                                                              Obj.magic
                                                                (PulseSyntaxExtension_Err.return
                                                                   uu___4))
                                                             uu___4))) uu___3)))
                                       uu___2))) uu___1)))) uu___1 uu___
and (desugar_branch :
  PulseSyntaxExtension_Env.env_t ->
    (FStar_Parser_AST.pattern * PulseSyntaxExtension_Sugar.stmt) ->
      PulseSyntaxExtension_SyntaxWrapper.branch PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun br ->
           let uu___ = br in
           match uu___ with
           | (p, e) ->
               let uu___1 = desugar_pat env p in
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang
                    PulseSyntaxExtension_Err.err_monad () ()
                    (Obj.magic uu___1)
                    (fun uu___2 ->
                       (fun uu___2 ->
                          let uu___2 = Obj.magic uu___2 in
                          match uu___2 with
                          | (p1, vs) ->
                              let uu___3 =
                                PulseSyntaxExtension_Env.push_bvs env vs in
                              (match uu___3 with
                               | (env1, bvs) ->
                                   let uu___4 = desugar_stmt env1 e in
                                   Obj.magic
                                     (FStar_Class_Monad.op_let_Bang
                                        PulseSyntaxExtension_Err.err_monad ()
                                        () (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           (fun e1 ->
                                              let e1 = Obj.magic e1 in
                                              let e2 =
                                                let uu___5 =
                                                  FStar_Compiler_List.map
                                                    (fun v ->
                                                       v.FStar_Syntax_Syntax.index)
                                                    bvs in
                                                PulseSyntaxExtension_SyntaxWrapper.close_st_term_n
                                                  e1 uu___5 in
                                              Obj.magic
                                                (PulseSyntaxExtension_Err.return
                                                   (p1, e2))) uu___5))))
                         uu___2))) uu___1 uu___
and (desugar_pat :
  PulseSyntaxExtension_Env.env_t ->
    FStar_Parser_AST.pattern ->
      (PulseSyntaxExtension_SyntaxWrapper.pattern * FStar_Ident.ident
        Prims.list) PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun p ->
           let r = p.FStar_Parser_AST.prange in
           match p.FStar_Parser_AST.pat with
           | FStar_Parser_AST.PatVar (id, uu___, uu___1) ->
               Obj.magic
                 (Obj.repr
                    (let uu___2 =
                       let uu___3 =
                         let uu___4 = FStar_Ident.string_of_id id in
                         PulseSyntaxExtension_SyntaxWrapper.pat_var uu___4 r in
                       (uu___3, [id]) in
                     PulseSyntaxExtension_Err.return uu___2))
           | FStar_Parser_AST.PatWild uu___ ->
               Obj.magic
                 (Obj.repr
                    (let id = FStar_Ident.mk_ident ("_", r) in
                     let uu___1 =
                       let uu___2 =
                         PulseSyntaxExtension_SyntaxWrapper.pat_var "_" r in
                       (uu___2, [id]) in
                     PulseSyntaxExtension_Err.return uu___1))
           | FStar_Parser_AST.PatConst c ->
               Obj.magic
                 (Obj.repr
                    (let c1 = desugar_const c in
                     let uu___ =
                       let uu___1 =
                         PulseSyntaxExtension_SyntaxWrapper.pat_constant c1 r in
                       (uu___1, []) in
                     PulseSyntaxExtension_Err.return uu___))
           | FStar_Parser_AST.PatName lid ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = desugar_datacon env lid in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun fv ->
                             let fv = Obj.magic fv in
                             let uu___1 =
                               let uu___2 =
                                 PulseSyntaxExtension_SyntaxWrapper.pat_cons
                                   fv [] r in
                               (uu___2, []) in
                             Obj.magic
                               (PulseSyntaxExtension_Err.return uu___1))
                            uu___1)))
           | FStar_Parser_AST.PatApp
               ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName lid;
                  FStar_Parser_AST.prange = uu___;_},
                args)
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___1 = desugar_datacon env lid in
                     FStar_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun fv ->
                             let fv = Obj.magic fv in
                             let uu___2 =
                               Obj.magic
                                 (FStar_Class_Monad.mapM
                                    PulseSyntaxExtension_Err.err_monad () ()
                                    (fun uu___3 ->
                                       (fun p1 ->
                                          let p1 = Obj.magic p1 in
                                          match p1.FStar_Parser_AST.pat with
                                          | FStar_Parser_AST.PatVar
                                              (id, uu___3, uu___4) ->
                                              Obj.magic
                                                (PulseSyntaxExtension_Err.return
                                                   id)
                                          | FStar_Parser_AST.PatWild uu___3
                                              ->
                                              let uu___4 =
                                                FStar_Ident.mk_ident ("_", r) in
                                              Obj.magic
                                                (PulseSyntaxExtension_Err.return
                                                   uu___4)
                                          | uu___3 ->
                                              Obj.magic
                                                (PulseSyntaxExtension_Err.fail
                                                   "invalid pattern: no deep patterns allowed"
                                                   r)) uu___3)
                                    (Obj.magic args)) in
                             Obj.magic
                               (FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun idents ->
                                        let idents = Obj.magic idents in
                                        let strs =
                                          FStar_Compiler_List.map
                                            FStar_Ident.string_of_id idents in
                                        let pats =
                                          FStar_Compiler_List.map
                                            (fun s ->
                                               PulseSyntaxExtension_SyntaxWrapper.pat_var
                                                 s r) strs in
                                        let uu___3 =
                                          let uu___4 =
                                            PulseSyntaxExtension_SyntaxWrapper.pat_cons
                                              fv pats r in
                                          (uu___4, idents) in
                                        Obj.magic
                                          (PulseSyntaxExtension_Err.return
                                             uu___3)) uu___3))) uu___2)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (PulseSyntaxExtension_Err.fail "invalid pattern" r)))
        uu___1 uu___
and (desugar_bind :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.stmt'__LetBinding__payload ->
      PulseSyntaxExtension_Sugar.stmt ->
        FStar_Compiler_Range_Type.range ->
          PulseSyntaxExtension_SyntaxWrapper.st_term
            PulseSyntaxExtension_Err.err)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun env ->
             fun lb ->
               fun s2 ->
                 fun r ->
                   let uu___ =
                     desugar_term_opt env lb.PulseSyntaxExtension_Sugar.typ in
                   Obj.magic
                     (FStar_Class_Monad.op_let_Bang
                        PulseSyntaxExtension_Err.err_monad () ()
                        (Obj.magic uu___)
                        (fun uu___1 ->
                           (fun annot ->
                              let annot = Obj.magic annot in
                              let b =
                                PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                  lb.PulseSyntaxExtension_Sugar.id annot in
                              let uu___1 =
                                let uu___2 =
                                  PulseSyntaxExtension_Env.push_bv env
                                    lb.PulseSyntaxExtension_Sugar.id in
                                match uu___2 with
                                | (env1, bv) ->
                                    let uu___3 = desugar_stmt env1 s2 in
                                    Obj.magic
                                      (FStar_Class_Monad.op_let_Bang
                                         PulseSyntaxExtension_Err.err_monad
                                         () () (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun s21 ->
                                               let s21 = Obj.magic s21 in
                                               let uu___4 =
                                                 PulseSyntaxExtension_SyntaxWrapper.close_st_term
                                                   s21
                                                   bv.FStar_Syntax_Syntax.index in
                                               Obj.magic
                                                 (PulseSyntaxExtension_Err.return
                                                    uu___4)) uu___4)) in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   PulseSyntaxExtension_Err.err_monad () ()
                                   (Obj.magic uu___1)
                                   (fun uu___2 ->
                                      (fun s21 ->
                                         let s21 = Obj.magic s21 in
                                         match lb.PulseSyntaxExtension_Sugar.init1
                                         with
                                         | FStar_Pervasives_Native.None ->
                                             Obj.magic
                                               (Obj.repr
                                                  (PulseSyntaxExtension_Err.fail
                                                     "Uninitialized variables are not yet handled"
                                                     r))
                                         | FStar_Pervasives_Native.Some e1 ->
                                             Obj.magic
                                               (Obj.repr
                                                  (match lb.PulseSyntaxExtension_Sugar.qualifier
                                                   with
                                                   | FStar_Pervasives_Native.None
                                                       ->
                                                       Obj.repr
                                                         (match e1 with
                                                          | PulseSyntaxExtension_Sugar.Array_initializer
                                                              uu___2 ->
                                                              Obj.repr
                                                                (PulseSyntaxExtension_Err.fail
                                                                   "immutable local arrays are not yet supported"
                                                                   r)
                                                          | PulseSyntaxExtension_Sugar.Lambda_initializer
                                                              {
                                                                PulseSyntaxExtension_Sugar.id2
                                                                  = id;
                                                                PulseSyntaxExtension_Sugar.is_rec
                                                                  = false;
                                                                PulseSyntaxExtension_Sugar.binders2
                                                                  = binders;
                                                                PulseSyntaxExtension_Sugar.ascription1
                                                                  =
                                                                  FStar_Pervasives.Inl
                                                                  c;
                                                                PulseSyntaxExtension_Sugar.measure
                                                                  =
                                                                  FStar_Pervasives_Native.None;
                                                                PulseSyntaxExtension_Sugar.body3
                                                                  =
                                                                  FStar_Pervasives.Inl
                                                                  stmt;
                                                                PulseSyntaxExtension_Sugar.decorations
                                                                  = uu___2;
                                                                PulseSyntaxExtension_Sugar.range3
                                                                  = range;_}
                                                              ->
                                                              Obj.repr
                                                                (let lam =
                                                                   {
                                                                    PulseSyntaxExtension_Sugar.binders1
                                                                    = binders;
                                                                    PulseSyntaxExtension_Sugar.ascription
                                                                    =
                                                                    (FStar_Pervasives_Native.Some
                                                                    c);
                                                                    PulseSyntaxExtension_Sugar.body2
                                                                    = stmt;
                                                                    PulseSyntaxExtension_Sugar.range2
                                                                    = range
                                                                   } in
                                                                 let uu___3 =
                                                                   desugar_lambda
                                                                    env lam in
                                                                 FStar_Class_Monad.op_let_Bang
                                                                   PulseSyntaxExtension_Err.err_monad
                                                                   () ()
                                                                   (Obj.magic
                                                                    uu___3)
                                                                   (fun
                                                                    uu___4 ->
                                                                    (fun lam1
                                                                    ->
                                                                    let lam1
                                                                    =
                                                                    Obj.magic
                                                                    lam1 in
                                                                    let uu___4
                                                                    =
                                                                    mk_bind b
                                                                    lam1 s21
                                                                    r in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    uu___4))
                                                                    uu___4))
                                                          | PulseSyntaxExtension_Sugar.Lambda_initializer
                                                              uu___2 ->
                                                              Obj.repr
                                                                (PulseSyntaxExtension_Err.fail
                                                                   "Nested functions are not yet fully supported"
                                                                   r)
                                                          | PulseSyntaxExtension_Sugar.Default_initializer
                                                              e11 ->
                                                              Obj.repr
                                                                (let uu___2 =
                                                                   tosyntax
                                                                    env e11 in
                                                                 FStar_Class_Monad.op_let_Bang
                                                                   PulseSyntaxExtension_Err.err_monad
                                                                   () ()
                                                                   (Obj.magic
                                                                    uu___2)
                                                                   (fun
                                                                    uu___3 ->
                                                                    (fun s1
                                                                    ->
                                                                    let s1 =
                                                                    Obj.magic
                                                                    s1 in
                                                                    let t =
                                                                    let uu___3
                                                                    =
                                                                    admit_or_return
                                                                    env s1 in
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    STTerm
                                                                    s11 ->
                                                                    mk_bind b
                                                                    s11 s21 r
                                                                    | 
                                                                    Return
                                                                    s11 ->
                                                                    let uu___4
                                                                    =
                                                                    as_term
                                                                    s11 in
                                                                    mk_totbind
                                                                    b uu___4
                                                                    s21 r in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    t))
                                                                    uu___3))
                                                          | PulseSyntaxExtension_Sugar.Stmt_initializer
                                                              e ->
                                                              Obj.repr
                                                                (let uu___2 =
                                                                   desugar_stmt
                                                                    env e in
                                                                 FStar_Class_Monad.op_let_Bang
                                                                   PulseSyntaxExtension_Err.err_monad
                                                                   () ()
                                                                   (Obj.magic
                                                                    uu___2)
                                                                   (fun
                                                                    uu___3 ->
                                                                    (fun s ->
                                                                    let s =
                                                                    Obj.magic
                                                                    s in
                                                                    let uu___3
                                                                    =
                                                                    mk_bind b
                                                                    s s21 r in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    uu___3))
                                                                    uu___3)))
                                                   | FStar_Pervasives_Native.Some
                                                       (PulseSyntaxExtension_Sugar.MUT)
                                                       ->
                                                       Obj.repr
                                                         (let b1 =
                                                            PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                                              lb.PulseSyntaxExtension_Sugar.id
                                                              annot in
                                                          match e1 with
                                                          | PulseSyntaxExtension_Sugar.Array_initializer
                                                              {
                                                                PulseSyntaxExtension_Sugar.init
                                                                  = init;
                                                                PulseSyntaxExtension_Sugar.len
                                                                  = len;_}
                                                              ->
                                                              let uu___2 =
                                                                desugar_term
                                                                  env init in
                                                              FStar_Class_Monad.op_let_Bang
                                                                PulseSyntaxExtension_Err.err_monad
                                                                () ()
                                                                (Obj.magic
                                                                   uu___2)
                                                                (fun uu___3
                                                                   ->
                                                                   (fun init1
                                                                    ->
                                                                    let init1
                                                                    =
                                                                    Obj.magic
                                                                    init1 in
                                                                    let uu___3
                                                                    =
                                                                    desugar_term
                                                                    env len in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___3)
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun len1
                                                                    ->
                                                                    let len1
                                                                    =
                                                                    Obj.magic
                                                                    len1 in
                                                                    let uu___4
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_let_mut_array
                                                                    b1 init1
                                                                    len1 s21
                                                                    r in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    uu___4))
                                                                    uu___4)))
                                                                    uu___3)
                                                          | PulseSyntaxExtension_Sugar.Default_initializer
                                                              e11 ->
                                                              let uu___2 =
                                                                desugar_term
                                                                  env e11 in
                                                              FStar_Class_Monad.op_let_Bang
                                                                PulseSyntaxExtension_Err.err_monad
                                                                () ()
                                                                (Obj.magic
                                                                   uu___2)
                                                                (fun uu___3
                                                                   ->
                                                                   (fun e12
                                                                    ->
                                                                    let e12 =
                                                                    Obj.magic
                                                                    e12 in
                                                                    let uu___3
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_let_mut
                                                                    b1 e12
                                                                    s21 r in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    uu___3))
                                                                    uu___3))
                                                   | FStar_Pervasives_Native.Some
                                                       (PulseSyntaxExtension_Sugar.REF)
                                                       ->
                                                       Obj.repr
                                                         (let b1 =
                                                            PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                                              lb.PulseSyntaxExtension_Sugar.id
                                                              annot in
                                                          match e1 with
                                                          | PulseSyntaxExtension_Sugar.Array_initializer
                                                              {
                                                                PulseSyntaxExtension_Sugar.init
                                                                  = init;
                                                                PulseSyntaxExtension_Sugar.len
                                                                  = len;_}
                                                              ->
                                                              let uu___2 =
                                                                desugar_term
                                                                  env init in
                                                              FStar_Class_Monad.op_let_Bang
                                                                PulseSyntaxExtension_Err.err_monad
                                                                () ()
                                                                (Obj.magic
                                                                   uu___2)
                                                                (fun uu___3
                                                                   ->
                                                                   (fun init1
                                                                    ->
                                                                    let init1
                                                                    =
                                                                    Obj.magic
                                                                    init1 in
                                                                    let uu___3
                                                                    =
                                                                    desugar_term
                                                                    env len in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___3)
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun len1
                                                                    ->
                                                                    let len1
                                                                    =
                                                                    Obj.magic
                                                                    len1 in
                                                                    let uu___4
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_let_mut_array
                                                                    b1 init1
                                                                    len1 s21
                                                                    r in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    uu___4))
                                                                    uu___4)))
                                                                    uu___3)
                                                          | PulseSyntaxExtension_Sugar.Default_initializer
                                                              e11 ->
                                                              let uu___2 =
                                                                desugar_term
                                                                  env e11 in
                                                              FStar_Class_Monad.op_let_Bang
                                                                PulseSyntaxExtension_Err.err_monad
                                                                () ()
                                                                (Obj.magic
                                                                   uu___2)
                                                                (fun uu___3
                                                                   ->
                                                                   (fun e12
                                                                    ->
                                                                    let e12 =
                                                                    Obj.magic
                                                                    e12 in
                                                                    let uu___3
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_let_mut
                                                                    b1 e12
                                                                    s21 r in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    uu___3))
                                                                    uu___3)))))
                                        uu___2))) uu___1))) uu___3 uu___2
            uu___1 uu___
and (desugar_sequence :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.stmt ->
      PulseSyntaxExtension_Sugar.stmt ->
        PulseSyntaxExtension_Sugar.rng ->
          PulseSyntaxExtension_SyntaxWrapper.st_term
            PulseSyntaxExtension_Err.err)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun env ->
             fun s1 ->
               fun s2 ->
                 fun r ->
                   let uu___ = desugar_stmt env s1 in
                   Obj.magic
                     (FStar_Class_Monad.op_let_Bang
                        PulseSyntaxExtension_Err.err_monad () ()
                        (Obj.magic uu___)
                        (fun uu___1 ->
                           (fun s11 ->
                              let s11 = Obj.magic s11 in
                              let uu___1 = desugar_stmt env s2 in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   PulseSyntaxExtension_Err.err_monad () ()
                                   (Obj.magic uu___1)
                                   (fun uu___2 ->
                                      (fun s21 ->
                                         let s21 = Obj.magic s21 in
                                         let annot =
                                           let uu___2 =
                                             FStar_Ident.id_of_text "_" in
                                           let uu___3 =
                                             PulseSyntaxExtension_SyntaxWrapper.tm_unknown
                                               r in
                                           PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                             uu___2 uu___3 in
                                         let uu___2 = mk_bind annot s11 s21 r in
                                         Obj.magic
                                           (PulseSyntaxExtension_Err.return
                                              uu___2)) uu___2))) uu___1)))
            uu___3 uu___2 uu___1 uu___
and (desugar_proof_hint_with_binders :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.stmt ->
      PulseSyntaxExtension_Sugar.stmt FStar_Pervasives_Native.option ->
        PulseSyntaxExtension_Sugar.rng ->
          PulseSyntaxExtension_SyntaxWrapper.st_term
            PulseSyntaxExtension_Err.err)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun env ->
             fun s1 ->
               fun k ->
                 fun r ->
                   match s1.PulseSyntaxExtension_Sugar.s with
                   | PulseSyntaxExtension_Sugar.ProofHintWithBinders
                       { PulseSyntaxExtension_Sugar.hint_type = hint_type;
                         PulseSyntaxExtension_Sugar.binders = bs;_}
                       ->
                       Obj.magic
                         (Obj.repr
                            (let uu___ = desugar_binders env bs in
                             FStar_Class_Monad.op_let_Bang
                               PulseSyntaxExtension_Err.err_monad () ()
                               (Obj.magic uu___)
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     let uu___1 = Obj.magic uu___1 in
                                     match uu___1 with
                                     | (env1, binders, bvs) ->
                                         let vars =
                                           FStar_Compiler_List.map
                                             (fun bv ->
                                                bv.FStar_Syntax_Syntax.index)
                                             bvs in
                                         let uu___2 =
                                           desugar_hint_type env1 hint_type in
                                         Obj.magic
                                           (FStar_Class_Monad.op_let_Bang
                                              PulseSyntaxExtension_Err.err_monad
                                              () () (Obj.magic uu___2)
                                              (fun uu___3 ->
                                                 (fun ht ->
                                                    let ht = Obj.magic ht in
                                                    let uu___3 =
                                                      match k with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          let uu___4 =
                                                            let uu___5 =
                                                              PulseSyntaxExtension_SyntaxWrapper.tm_expr
                                                                FStar_Syntax_Syntax.unit_const
                                                                r in
                                                            PulseSyntaxExtension_SyntaxWrapper.tm_ghost_return
                                                              uu___5 r in
                                                          PulseSyntaxExtension_Err.return
                                                            uu___4
                                                      | FStar_Pervasives_Native.Some
                                                          s2 ->
                                                          desugar_stmt env1
                                                            s2 in
                                                    Obj.magic
                                                      (FStar_Class_Monad.op_let_Bang
                                                         PulseSyntaxExtension_Err.err_monad
                                                         () ()
                                                         (Obj.magic uu___3)
                                                         (fun uu___4 ->
                                                            (fun s2 ->
                                                               let s2 =
                                                                 Obj.magic s2 in
                                                               let binders1 =
                                                                 FStar_Compiler_List.map
                                                                   FStar_Pervasives_Native.snd
                                                                   binders in
                                                               let sub =
                                                                 PulseSyntaxExtension_SyntaxWrapper.bvs_as_subst
                                                                   vars in
                                                               let s21 =
                                                                 PulseSyntaxExtension_SyntaxWrapper.subst_st_term
                                                                   sub s2 in
                                                               let ht1 =
                                                                 PulseSyntaxExtension_SyntaxWrapper.subst_proof_hint
                                                                   sub ht in
                                                               let uu___4 =
                                                                 let uu___5 =
                                                                   PulseSyntaxExtension_SyntaxWrapper.close_binders
                                                                    binders1
                                                                    vars in
                                                                 PulseSyntaxExtension_SyntaxWrapper.tm_proof_hint_with_binders
                                                                   ht1 uu___5
                                                                   s21 r in
                                                               Obj.magic
                                                                 (PulseSyntaxExtension_Err.return
                                                                    uu___4))
                                                              uu___4)))
                                                   uu___3))) uu___1)))
                   | uu___ ->
                       Obj.magic
                         (Obj.repr
                            (PulseSyntaxExtension_Err.fail
                               "Expected ProofHintWithBinders"
                               s1.PulseSyntaxExtension_Sugar.range1))) uu___3
            uu___2 uu___1 uu___
and (desugar_binders :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.binders ->
      (PulseSyntaxExtension_Env.env_t *
        (PulseSyntaxExtension_SyntaxWrapper.qualifier
        FStar_Pervasives_Native.option *
        PulseSyntaxExtension_SyntaxWrapper.binder) Prims.list *
        FStar_Syntax_Syntax.bv Prims.list) PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun bs ->
           let rec aux uu___1 uu___ =
             (fun env1 ->
                fun bs1 ->
                  match bs1 with
                  | [] ->
                      Obj.magic
                        (Obj.repr
                           (PulseSyntaxExtension_Err.return (env1, [], [])))
                  | b::bs2 ->
                      Obj.magic
                        (Obj.repr
                           (let rng = b.FStar_Parser_AST.brange in
                            let uu___ =
                              PulseSyntaxExtension_Env.destruct_binder b in
                            match uu___ with
                            | (aq, b1, t, attrs) ->
                                let uu___1 = desugar_term env1 t in
                                FStar_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun t1 ->
                                        let t1 = Obj.magic t1 in
                                        let uu___2 =
                                          Obj.magic
                                            (FStar_Class_Monad.mapM
                                               PulseSyntaxExtension_Err.err_monad
                                               () ()
                                               (fun uu___3 ->
                                                  (Obj.magic
                                                     (desugar_term env1))
                                                    uu___3) (Obj.magic attrs)) in
                                        Obj.magic
                                          (FStar_Class_Monad.op_let_Bang
                                             PulseSyntaxExtension_Err.err_monad
                                             () () (Obj.magic uu___2)
                                             (fun uu___3 ->
                                                (fun attrs1 ->
                                                   let attrs1 =
                                                     Obj.magic attrs1 in
                                                   let uu___3 =
                                                     PulseSyntaxExtension_Env.push_bv
                                                       env1 b1 in
                                                   match uu___3 with
                                                   | (env2, bv) ->
                                                       let uu___4 =
                                                         aux env2 bs2 in
                                                       Obj.magic
                                                         (FStar_Class_Monad.op_let_Bang
                                                            PulseSyntaxExtension_Err.err_monad
                                                            () ()
                                                            (Obj.magic uu___4)
                                                            (fun uu___5 ->
                                                               (fun uu___5 ->
                                                                  let uu___5
                                                                    =
                                                                    Obj.magic
                                                                    uu___5 in
                                                                  match uu___5
                                                                  with
                                                                  | (env3,
                                                                    bs3, bvs)
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    as_qual
                                                                    aq rng in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun aq1
                                                                    ->
                                                                    let aq1 =
                                                                    Obj.magic
                                                                    aq1 in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    (env3,
                                                                    ((aq1,
                                                                    b1, t1,
                                                                    attrs1)
                                                                    :: bs3),
                                                                    (bv ::
                                                                    bvs))))
                                                                    uu___7)))
                                                                 uu___5)))
                                                  uu___3))) uu___2)))) uu___1
               uu___ in
           let uu___ = aux env bs in
           Obj.magic
             (FStar_Class_Monad.op_let_Bang
                PulseSyntaxExtension_Err.err_monad () () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | (env1, bs1, bvs) ->
                          let uu___2 =
                            let uu___3 =
                              FStar_Compiler_List.map
                                (fun uu___4 ->
                                   match uu___4 with
                                   | (aq, b, t, attrs) ->
                                       let uu___5 =
                                         PulseSyntaxExtension_SyntaxWrapper.mk_binder_with_attrs
                                           b t attrs in
                                       (aq, uu___5)) bs1 in
                            (env1, uu___3, bvs) in
                          Obj.magic (PulseSyntaxExtension_Err.return uu___2))
                     uu___1))) uu___1 uu___
and (desugar_lambda :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.lambda ->
      PulseSyntaxExtension_SyntaxWrapper.st_term PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun l ->
           let uu___ = l in
           match uu___ with
           | { PulseSyntaxExtension_Sugar.binders1 = binders;
               PulseSyntaxExtension_Sugar.ascription = ascription;
               PulseSyntaxExtension_Sugar.body2 = body;
               PulseSyntaxExtension_Sugar.range2 = range;_} ->
               let uu___1 = desugar_binders env binders in
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang
                    PulseSyntaxExtension_Err.err_monad () ()
                    (Obj.magic uu___1)
                    (fun uu___2 ->
                       (fun uu___2 ->
                          let uu___2 = Obj.magic uu___2 in
                          match uu___2 with
                          | (env1, bs, bvs) ->
                              let uu___3 =
                                match ascription with
                                | FStar_Pervasives_Native.None ->
                                    Obj.magic
                                      (Obj.repr
                                         (PulseSyntaxExtension_Err.return
                                            (env1, bs, bvs,
                                              FStar_Pervasives_Native.None)))
                                | FStar_Pervasives_Native.Some c ->
                                    Obj.magic
                                      (Obj.repr
                                         (let fvs =
                                            PulseSyntaxExtension_Env.free_vars_comp
                                              env1 c in
                                          let uu___4 =
                                            idents_as_binders env1 fvs in
                                          FStar_Class_Monad.op_let_Bang
                                            PulseSyntaxExtension_Err.err_monad
                                            () () (Obj.magic uu___4)
                                            (fun uu___5 ->
                                               (fun uu___5 ->
                                                  let uu___5 =
                                                    Obj.magic uu___5 in
                                                  match uu___5 with
                                                  | (env2, bs', bvs') ->
                                                      let bs1 =
                                                        FStar_List_Tot_Base.op_At
                                                          bs bs' in
                                                      let bvs1 =
                                                        FStar_List_Tot_Base.op_At
                                                          bvs bvs' in
                                                      let uu___6 =
                                                        desugar_computation_type
                                                          env2 c in
                                                      Obj.magic
                                                        (FStar_Class_Monad.op_let_Bang
                                                           PulseSyntaxExtension_Err.err_monad
                                                           () ()
                                                           (Obj.magic uu___6)
                                                           (fun uu___7 ->
                                                              (fun comp ->
                                                                 let comp =
                                                                   Obj.magic
                                                                    comp in
                                                                 Obj.magic
                                                                   (PulseSyntaxExtension_Err.return
                                                                    (env2,
                                                                    bs1,
                                                                    bvs1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    comp))))
                                                                uu___7)))
                                                 uu___5))) in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   PulseSyntaxExtension_Err.err_monad () ()
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         let uu___4 = Obj.magic uu___4 in
                                         match uu___4 with
                                         | (env2, bs1, bvs1, comp) ->
                                             let uu___5 =
                                               let uu___6 =
                                                 let uu___7 =
                                                   FStar_Options.ext_getv
                                                     "pulse:rvalues" in
                                                 uu___7 <> "" in
                                               if uu___6
                                               then
                                                 PulseSyntaxExtension_TransformRValues.transform
                                                   env2 body
                                               else
                                                 PulseSyntaxExtension_Err.return
                                                   body in
                                             Obj.magic
                                               (FStar_Class_Monad.op_let_Bang
                                                  PulseSyntaxExtension_Err.err_monad
                                                  () () (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     (fun body1 ->
                                                        let body1 =
                                                          Obj.magic body1 in
                                                        let uu___6 =
                                                          desugar_stmt env2
                                                            body1 in
                                                        Obj.magic
                                                          (FStar_Class_Monad.op_let_Bang
                                                             PulseSyntaxExtension_Err.err_monad
                                                             () ()
                                                             (Obj.magic
                                                                uu___6)
                                                             (fun uu___7 ->
                                                                (fun body2 ->
                                                                   let body2
                                                                    =
                                                                    Obj.magic
                                                                    body2 in
                                                                   let uu___7
                                                                    =
                                                                    PulseSyntaxExtension_Err.map2
                                                                    faux bs1
                                                                    bvs1 in
                                                                   Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun qbs
                                                                    ->
                                                                    let qbs =
                                                                    Obj.magic
                                                                    qbs in
                                                                    let uu___8
                                                                    =
                                                                    FStar_Compiler_List.fold_right
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    match 
                                                                    (uu___9,
                                                                    uu___10)
                                                                    with
                                                                    | 
                                                                    ((q, b,
                                                                    bv),
                                                                    (c,
                                                                    body3))
                                                                    ->
                                                                    let body'
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.index_of_bv
                                                                    bv in
                                                                    PulseSyntaxExtension_SyntaxWrapper.close_st_term
                                                                    body3
                                                                    uu___11 in
                                                                    let asc =
                                                                    match c
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    c1 ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.index_of_bv
                                                                    bv in
                                                                    PulseSyntaxExtension_SyntaxWrapper.close_comp
                                                                    c1
                                                                    uu___12 in
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___11 in
                                                                    let uu___11
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.tm_abs
                                                                    b q asc
                                                                    body'
                                                                    range in
                                                                    (FStar_Pervasives_Native.None,
                                                                    uu___11))
                                                                    qbs
                                                                    (comp,
                                                                    body2) in
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    (uu___9,
                                                                    abs) ->
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    abs))
                                                                    uu___8)))
                                                                  uu___7)))
                                                       uu___6))) uu___4)))
                         uu___2))) uu___1 uu___
and (desugar_decl :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.decl ->
      PulseSyntaxExtension_SyntaxWrapper.decl PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun env ->
         fun d ->
           let mk_knot_arr uu___3 uu___2 uu___1 uu___ =
             (fun env1 ->
                fun meas ->
                  fun bs ->
                    fun res ->
                      let r =
                        FStar_Ident.range_of_id
                          res.PulseSyntaxExtension_Sugar.return_name in
                      let uu___ = desugar_binders env1 bs in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang
                           PulseSyntaxExtension_Err.err_monad () ()
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___1 = Obj.magic uu___1 in
                                 match uu___1 with
                                 | (env2, bs', uu___2) ->
                                     let uu___3 = comp_to_ast_term res in
                                     Obj.magic
                                       (FStar_Class_Monad.op_let_Bang
                                          PulseSyntaxExtension_Err.err_monad
                                          () () (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             (fun res_t ->
                                                let res_t = Obj.magic res_t in
                                                let bs'' =
                                                  FStar_Compiler_List.map
                                                    (fun b ->
                                                       let uu___4 =
                                                         PulseSyntaxExtension_Env.destruct_binder
                                                           b in
                                                       match uu___4 with
                                                       | (q, x, ty, uu___5)
                                                           ->
                                                           FStar_Parser_AST.mk_binder
                                                             (FStar_Parser_AST.Annotated
                                                                (x, ty)) r
                                                             FStar_Parser_AST.Expr
                                                             q) bs in
                                                let last =
                                                  FStar_Compiler_List.last
                                                    bs'' in
                                                let init =
                                                  FStar_Compiler_List.init
                                                    bs'' in
                                                let bs''1 =
                                                  FStar_List_Tot_Base.op_At
                                                    init [last] in
                                                let uu___4 =
                                                  FStar_Parser_AST.mk_term
                                                    (FStar_Parser_AST.Product
                                                       (bs''1, res_t)) r
                                                    FStar_Parser_AST.Expr in
                                                Obj.magic
                                                  (PulseSyntaxExtension_Err.return
                                                     uu___4)) uu___4)))
                                uu___1))) uu___3 uu___2 uu___1 uu___ in
           match d with
           | PulseSyntaxExtension_Sugar.FnDefn
               { PulseSyntaxExtension_Sugar.id2 = id;
                 PulseSyntaxExtension_Sugar.is_rec = is_rec;
                 PulseSyntaxExtension_Sugar.binders2 = binders;
                 PulseSyntaxExtension_Sugar.ascription1 =
                   FStar_Pervasives.Inl ascription;
                 PulseSyntaxExtension_Sugar.measure = measure;
                 PulseSyntaxExtension_Sugar.body3 = FStar_Pervasives.Inl body;
                 PulseSyntaxExtension_Sugar.decorations = uu___;
                 PulseSyntaxExtension_Sugar.range3 = range;_}
               ->
               let uu___1 = desugar_binders env binders in
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang
                    PulseSyntaxExtension_Err.err_monad () ()
                    (Obj.magic uu___1)
                    (fun uu___2 ->
                       (fun uu___2 ->
                          let uu___2 = Obj.magic uu___2 in
                          match uu___2 with
                          | (env1, bs, bvs) ->
                              let fvs =
                                PulseSyntaxExtension_Env.free_vars_comp env1
                                  ascription in
                              let uu___3 = idents_as_binders env1 fvs in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   PulseSyntaxExtension_Err.err_monad () ()
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         let uu___4 = Obj.magic uu___4 in
                                         match uu___4 with
                                         | (env2, bs', bvs') ->
                                             let bs1 =
                                               FStar_List_Tot_Base.op_At bs
                                                 bs' in
                                             let bvs1 =
                                               FStar_List_Tot_Base.op_At bvs
                                                 bvs' in
                                             let uu___5 =
                                               desugar_computation_type env2
                                                 ascription in
                                             Obj.magic
                                               (FStar_Class_Monad.op_let_Bang
                                                  PulseSyntaxExtension_Err.err_monad
                                                  () () (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     (fun comp ->
                                                        let comp =
                                                          Obj.magic comp in
                                                        let uu___6 =
                                                          let uu___7 =
                                                            let uu___8 =
                                                              FStar_Options.ext_getv
                                                                "pulse:rvalues" in
                                                            uu___8 <> "" in
                                                          if uu___7
                                                          then
                                                            PulseSyntaxExtension_TransformRValues.transform
                                                              env2 body
                                                          else
                                                            PulseSyntaxExtension_Err.return
                                                              body in
                                                        Obj.magic
                                                          (FStar_Class_Monad.op_let_Bang
                                                             PulseSyntaxExtension_Err.err_monad
                                                             () ()
                                                             (Obj.magic
                                                                uu___6)
                                                             (fun uu___7 ->
                                                                (fun body1 ->
                                                                   let body1
                                                                    =
                                                                    Obj.magic
                                                                    body1 in
                                                                   let uu___7
                                                                    =
                                                                    PulseSyntaxExtension_Err.map_err_opt
                                                                    (desugar_term
                                                                    env2)
                                                                    measure in
                                                                   Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun meas
                                                                    ->
                                                                    let meas
                                                                    =
                                                                    Obj.magic
                                                                    meas in
                                                                    let uu___8
                                                                    =
                                                                    if is_rec
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___9
                                                                    =
                                                                    mk_knot_arr
                                                                    env2
                                                                    measure
                                                                    binders
                                                                    ascription in
                                                                    FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun ty
                                                                    ->
                                                                    let ty =
                                                                    Obj.magic
                                                                    ty in
                                                                    let uu___10
                                                                    =
                                                                    desugar_term
                                                                    env2 ty in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun ty1
                                                                    ->
                                                                    let ty1 =
                                                                    Obj.magic
                                                                    ty1 in
                                                                    let uu___11
                                                                    =
                                                                    PulseSyntaxExtension_Env.push_bv
                                                                    env2 id in
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    (env3,
                                                                    bv) ->
                                                                    let b =
                                                                    PulseSyntaxExtension_SyntaxWrapper.mk_binder
                                                                    id ty1 in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    (env3,
                                                                    (FStar_List_Tot_Base.op_At
                                                                    bs1
                                                                    [
                                                                    (FStar_Pervasives_Native.None,
                                                                    b)]),
                                                                    (FStar_List_Tot_Base.op_At
                                                                    bvs1 
                                                                    [bv]))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (PulseSyntaxExtension_Err.return
                                                                    (env2,
                                                                    bs1,
                                                                    bvs1))) in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    uu___9 in
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    (env3,
                                                                    bs2,
                                                                    bvs2) ->
                                                                    let uu___10
                                                                    =
                                                                    desugar_stmt
                                                                    env3
                                                                    body1 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    body2 ->
                                                                    let body2
                                                                    =
                                                                    Obj.magic
                                                                    body2 in
                                                                    let uu___11
                                                                    =
                                                                    PulseSyntaxExtension_Err.map2
                                                                    faux bs2
                                                                    bvs2 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    PulseSyntaxExtension_Err.err_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun qbs
                                                                    ->
                                                                    let qbs =
                                                                    Obj.magic
                                                                    qbs in
                                                                    let uu___12
                                                                    =
                                                                    PulseSyntaxExtension_SyntaxWrapper.fn_defn
                                                                    range id
                                                                    is_rec
                                                                    qbs comp
                                                                    meas
                                                                    body2 in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    uu___12))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                  uu___7)))
                                                       uu___6))) uu___4)))
                         uu___2))
           | PulseSyntaxExtension_Sugar.FnDefn
               { PulseSyntaxExtension_Sugar.id2 = id;
                 PulseSyntaxExtension_Sugar.is_rec = false;
                 PulseSyntaxExtension_Sugar.binders2 = binders;
                 PulseSyntaxExtension_Sugar.ascription1 =
                   FStar_Pervasives.Inr ascription;
                 PulseSyntaxExtension_Sugar.measure =
                   FStar_Pervasives_Native.None;
                 PulseSyntaxExtension_Sugar.body3 = FStar_Pervasives.Inr body;
                 PulseSyntaxExtension_Sugar.decorations = uu___;
                 PulseSyntaxExtension_Sugar.range3 = range;_}
               ->
               let uu___1 = desugar_binders env binders in
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang
                    PulseSyntaxExtension_Err.err_monad () ()
                    (Obj.magic uu___1)
                    (fun uu___2 ->
                       (fun uu___2 ->
                          let uu___2 = Obj.magic uu___2 in
                          match uu___2 with
                          | (env1, bs, bvs) ->
                              let uu___3 =
                                match ascription with
                                | FStar_Pervasives_Native.None ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___4 =
                                            let uu___5 =
                                              PulseSyntaxExtension_SyntaxWrapper.tm_unknown
                                                range in
                                            PulseSyntaxExtension_SyntaxWrapper.mk_tot
                                              uu___5 in
                                          PulseSyntaxExtension_Err.return
                                            uu___4))
                                | FStar_Pervasives_Native.Some t ->
                                    Obj.magic
                                      (Obj.repr
                                         (let uu___4 = desugar_term env1 t in
                                          FStar_Class_Monad.op_let_Bang
                                            PulseSyntaxExtension_Err.err_monad
                                            () () (Obj.magic uu___4)
                                            (fun uu___5 ->
                                               (fun t1 ->
                                                  let t1 = Obj.magic t1 in
                                                  let uu___5 =
                                                    PulseSyntaxExtension_SyntaxWrapper.mk_tot
                                                      t1 in
                                                  Obj.magic
                                                    (PulseSyntaxExtension_Err.return
                                                       uu___5)) uu___5))) in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   PulseSyntaxExtension_Err.err_monad () ()
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun comp ->
                                         let comp = Obj.magic comp in
                                         let uu___4 =
                                           desugar_lambda env1 body in
                                         Obj.magic
                                           (FStar_Class_Monad.op_let_Bang
                                              PulseSyntaxExtension_Err.err_monad
                                              () () (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun body1 ->
                                                    let body1 =
                                                      Obj.magic body1 in
                                                    let uu___5 =
                                                      PulseSyntaxExtension_Err.map2
                                                        faux bs bvs in
                                                    Obj.magic
                                                      (FStar_Class_Monad.op_let_Bang
                                                         PulseSyntaxExtension_Err.err_monad
                                                         () ()
                                                         (Obj.magic uu___5)
                                                         (fun uu___6 ->
                                                            (fun qbs ->
                                                               let qbs =
                                                                 Obj.magic
                                                                   qbs in
                                                               let uu___6 =
                                                                 PulseSyntaxExtension_SyntaxWrapper.fn_defn
                                                                   range id
                                                                   false qbs
                                                                   comp
                                                                   FStar_Pervasives_Native.None
                                                                   body1 in
                                                               Obj.magic
                                                                 (PulseSyntaxExtension_Err.return
                                                                    uu___6))
                                                              uu___6)))
                                                   uu___5))) uu___4))) uu___2))
           | PulseSyntaxExtension_Sugar.FnDecl
               { PulseSyntaxExtension_Sugar.id3 = id;
                 PulseSyntaxExtension_Sugar.binders3 = binders;
                 PulseSyntaxExtension_Sugar.ascription2 =
                   FStar_Pervasives.Inl ascription;
                 PulseSyntaxExtension_Sugar.decorations1 = uu___;
                 PulseSyntaxExtension_Sugar.range4 = range;_}
               ->
               let uu___1 = desugar_binders env binders in
               Obj.magic
                 (FStar_Class_Monad.op_let_Bang
                    PulseSyntaxExtension_Err.err_monad () ()
                    (Obj.magic uu___1)
                    (fun uu___2 ->
                       (fun uu___2 ->
                          let uu___2 = Obj.magic uu___2 in
                          match uu___2 with
                          | (env1, bs, bvs) ->
                              let uu___3 =
                                desugar_computation_type env1 ascription in
                              Obj.magic
                                (FStar_Class_Monad.op_let_Bang
                                   PulseSyntaxExtension_Err.err_monad () ()
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun comp ->
                                         let comp = Obj.magic comp in
                                         let uu___4 =
                                           PulseSyntaxExtension_Err.map2 faux
                                             bs bvs in
                                         Obj.magic
                                           (FStar_Class_Monad.op_let_Bang
                                              PulseSyntaxExtension_Err.err_monad
                                              () () (Obj.magic uu___4)
                                              (fun uu___5 ->
                                                 (fun qbs ->
                                                    let qbs = Obj.magic qbs in
                                                    let uu___5 =
                                                      PulseSyntaxExtension_SyntaxWrapper.fn_decl
                                                        range id qbs comp in
                                                    Obj.magic
                                                      (PulseSyntaxExtension_Err.return
                                                         uu___5)) uu___5)))
                                        uu___4))) uu___2))) uu___1 uu___
let (reinitialize_env :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident ->
      PulseSyntaxExtension_Env.name Prims.list ->
        (Prims.string * PulseSyntaxExtension_Env.name) Prims.list ->
          PulseSyntaxExtension_Env.env_t)
  =
  fun dsenv ->
    fun curmod ->
      fun open_namespaces ->
        fun module_abbrevs ->
          let dsenv1 = FStar_Syntax_DsEnv.set_current_module dsenv curmod in
          let dsenv2 =
            FStar_Compiler_List.fold_right
              (fun ns ->
                 fun env ->
                   let uu___ =
                     FStar_Ident.lid_of_path ns PulseSyntaxExtension_Env.r_ in
                   FStar_Syntax_DsEnv.push_namespace env uu___)
              open_namespaces dsenv1 in
          let dsenv3 = FStar_Syntax_DsEnv.push_namespace dsenv2 curmod in
          let dsenv4 =
            FStar_Compiler_List.fold_left
              (fun env ->
                 fun uu___ ->
                   match uu___ with
                   | (m, n) ->
                       let uu___1 = FStar_Ident.id_of_text m in
                       let uu___2 =
                         FStar_Ident.lid_of_path n
                           PulseSyntaxExtension_Env.r_ in
                       FStar_Syntax_DsEnv.push_module_abbrev env uu___1
                         uu___2) dsenv3 module_abbrevs in
          {
            PulseSyntaxExtension_Env.dsenv = dsenv4;
            PulseSyntaxExtension_Env.local_refs = []
          }
let (mk_env : FStar_Syntax_DsEnv.env -> PulseSyntaxExtension_Env.env_t) =
  fun dsenv ->
    {
      PulseSyntaxExtension_Env.dsenv = dsenv;
      PulseSyntaxExtension_Env.local_refs = []
    }