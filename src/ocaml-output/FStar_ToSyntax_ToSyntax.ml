open Prims
type annotated_pat =
  (FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv *
    FStar_Syntax_Syntax.typ) Prims.list)
let (desugar_disjunctive_pattern :
  (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t *
    (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term'
    FStar_Syntax_Syntax.syntax) Prims.list) Prims.list ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
      FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.branch Prims.list)
  =
  fun annotated_pats  ->
    fun when_opt  ->
      fun branch  ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____103  ->
                match uu____103 with
                | (pat,annots) ->
                    let branch1 =
                      FStar_List.fold_left
                        (fun br  ->
                           fun uu____158  ->
                             match uu____158 with
                             | (bv,ty) ->
                                 let lb =
                                   let uu____176 =
                                     FStar_Syntax_Syntax.bv_to_name bv  in
                                   FStar_Syntax_Util.mk_letbinding
                                     (FStar_Util.Inl bv) [] ty
                                     FStar_Parser_Const.effect_Tot_lid
                                     uu____176 [] br.FStar_Syntax_Syntax.pos
                                    in
                                 let branch1 =
                                   let uu____182 =
                                     let uu____183 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____183]  in
                                   FStar_Syntax_Subst.close uu____182 branch
                                    in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch1))
                                   FStar_Pervasives_Native.None
                                   br.FStar_Syntax_Syntax.pos) branch annots
                       in
                    FStar_Syntax_Util.branch (pat, when_opt, branch1)))
  
let (trans_qual :
  FStar_Range.range ->
    FStar_Ident.lident FStar_Pervasives_Native.option ->
      FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
  =
  fun r  ->
    fun maybe_effect_id  ->
      fun uu___0_240  ->
        match uu___0_240 with
        | FStar_Parser_AST.Private  -> FStar_Syntax_Syntax.Private
        | FStar_Parser_AST.Assumption  -> FStar_Syntax_Syntax.Assumption
        | FStar_Parser_AST.Unfold_for_unification_and_vcgen  ->
            FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
        | FStar_Parser_AST.Inline_for_extraction  ->
            FStar_Syntax_Syntax.Inline_for_extraction
        | FStar_Parser_AST.NoExtract  -> FStar_Syntax_Syntax.NoExtract
        | FStar_Parser_AST.Irreducible  -> FStar_Syntax_Syntax.Irreducible
        | FStar_Parser_AST.Logic  -> FStar_Syntax_Syntax.Logic
        | FStar_Parser_AST.TotalEffect  -> FStar_Syntax_Syntax.TotalEffect
        | FStar_Parser_AST.Effect_qual  -> FStar_Syntax_Syntax.Effect
        | FStar_Parser_AST.New  -> FStar_Syntax_Syntax.New
        | FStar_Parser_AST.Abstract  -> FStar_Syntax_Syntax.Abstract
        | FStar_Parser_AST.Opaque  ->
            (FStar_Errors.log_issue r
               (FStar_Errors.Warning_DeprecatedOpaqueQualifier,
                 "The 'opaque' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given 'opaque val f : t', the behavior was to exclude the definition of 'f' to the SMT solver. This corresponds roughly to the new 'irreducible' qualifier. (2) Given 'opaque type t = t'', the behavior was to provide the definition of 't' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of 'unfoldable' (which is currently the default).");
             FStar_Syntax_Syntax.Visible_default)
        | FStar_Parser_AST.Reflectable  ->
            (match maybe_effect_id with
             | FStar_Pervasives_Native.None  ->
                 FStar_Errors.raise_error
                   (FStar_Errors.Fatal_ReflectOnlySupportedOnEffects,
                     "Qualifier reflect only supported on effects") r
             | FStar_Pervasives_Native.Some effect_id ->
                 FStar_Syntax_Syntax.Reflectable effect_id)
        | FStar_Parser_AST.Reifiable  -> FStar_Syntax_Syntax.Reifiable
        | FStar_Parser_AST.Noeq  -> FStar_Syntax_Syntax.Noeq
        | FStar_Parser_AST.Unopteq  -> FStar_Syntax_Syntax.Unopteq
        | FStar_Parser_AST.DefaultEffect  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_DefaultQualifierNotAllowedOnEffects,
                "The 'default' qualifier on effects is no longer supported")
              r
        | FStar_Parser_AST.Inline  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
        | FStar_Parser_AST.Visible  ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnsupportedQualifier,
                "Unsupported qualifier") r
  
let (trans_pragma : FStar_Parser_AST.pragma -> FStar_Syntax_Syntax.pragma) =
  fun uu___1_260  ->
    match uu___1_260 with
    | FStar_Parser_AST.SetOptions s -> FStar_Syntax_Syntax.SetOptions s
    | FStar_Parser_AST.ResetOptions sopt ->
        FStar_Syntax_Syntax.ResetOptions sopt
    | FStar_Parser_AST.PushOptions sopt ->
        FStar_Syntax_Syntax.PushOptions sopt
    | FStar_Parser_AST.PopOptions  -> FStar_Syntax_Syntax.PopOptions
    | FStar_Parser_AST.RestartSolver  -> FStar_Syntax_Syntax.RestartSolver
    | FStar_Parser_AST.LightOff  -> FStar_Syntax_Syntax.LightOff
  
let (as_imp :
  FStar_Parser_AST.imp ->
    FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
  =
  fun uu___2_278  ->
    match uu___2_278 with
    | FStar_Parser_AST.Hash  ->
        FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
    | uu____281 -> FStar_Pervasives_Native.None
  
let arg_withimp_e :
  'uuuuuu289 .
    FStar_Parser_AST.imp ->
      'uuuuuu289 ->
        ('uuuuuu289 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'uuuuuu315 .
    FStar_Parser_AST.imp ->
      'uuuuuu315 ->
        ('uuuuuu315 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  =
  fun imp  ->
    fun t  ->
      match imp with
      | FStar_Parser_AST.Hash  ->
          (t, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag))
      | uu____334 -> (t, FStar_Pervasives_Native.None)
  
let (contains_binder : FStar_Parser_AST.binder Prims.list -> Prims.bool) =
  fun binders  ->
    FStar_All.pipe_right binders
      (FStar_Util.for_some
         (fun b  ->
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated uu____355 -> true
            | uu____361 -> false))
  
let rec (unparen : FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Paren t1 -> unparen t1
    | uu____370 -> t
  
let (tm_type_z : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____377 =
      let uu____378 = FStar_Ident.lid_of_path ["Type0"] r  in
      FStar_Parser_AST.Name uu____378  in
    FStar_Parser_AST.mk_term uu____377 r FStar_Parser_AST.Kind
  
let (tm_type : FStar_Range.range -> FStar_Parser_AST.term) =
  fun r  ->
    let uu____388 =
      let uu____389 = FStar_Ident.lid_of_path ["Type"] r  in
      FStar_Parser_AST.Name uu____389  in
    FStar_Parser_AST.mk_term uu____388 r FStar_Parser_AST.Kind
  
let rec (is_comp_type :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____405 =
        let uu____406 = unparen t  in uu____406.FStar_Parser_AST.tm  in
      match uu____405 with
      | FStar_Parser_AST.Name l ->
          let uu____409 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____409 FStar_Option.isSome
      | FStar_Parser_AST.Construct (l,uu____416) ->
          let uu____429 = FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
          FStar_All.pipe_right uu____429 FStar_Option.isSome
      | FStar_Parser_AST.App (head,uu____436,uu____437) ->
          is_comp_type env head
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,uu____442,uu____443) ->
          is_comp_type env t1
      | FStar_Parser_AST.LetOpen (uu____448,t1) -> is_comp_type env t1
      | uu____450 -> false
  
let (unit_ty : FStar_Range.range -> FStar_Parser_AST.term) =
  fun rng  ->
    FStar_Parser_AST.mk_term
      (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid) rng
      FStar_Parser_AST.Type_level
  
type env_t = FStar_Syntax_DsEnv.env
type lenv_t = FStar_Syntax_Syntax.bv Prims.list
let (desugar_name' :
  (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
    env_t ->
      Prims.bool ->
        FStar_Ident.lid ->
          FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun setpos  ->
    fun env  ->
      fun resolve  ->
        fun l  ->
          let tm_attrs_opt =
            if resolve
            then FStar_Syntax_DsEnv.try_lookup_lid_with_attributes env l
            else
              FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
                env l
             in
          match tm_attrs_opt with
          | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
          | FStar_Pervasives_Native.Some (tm,attrs) ->
              let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1
  
let desugar_name :
  'uuuuuu546 .
    'uuuuuu546 ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        env_t -> Prims.bool -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun mk  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            FStar_Syntax_DsEnv.fail_or env (desugar_name' setpos env resolve)
              l
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n  ->
    fun s  ->
      fun r  ->
        let uu____599 =
          let uu____600 =
            let uu____601 =
              let uu____607 = FStar_Parser_AST.compile_op n s r  in
              (uu____607, r)  in
            FStar_Ident.mk_ident uu____601  in
          [uu____600]  in
        FStar_All.pipe_right uu____599 FStar_Ident.lid_of_ids
  
let (op_as_term :
  env_t ->
    Prims.int ->
      FStar_Ident.ident ->
        FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun arity  ->
      fun op  ->
        let r l dd =
          let uu____645 =
            let uu____646 =
              let uu____647 =
                let uu____648 = FStar_Ident.range_of_id op  in
                FStar_Ident.set_lid_range l uu____648  in
              FStar_Syntax_Syntax.lid_as_fv uu____647 dd
                FStar_Pervasives_Native.None
               in
            FStar_All.pipe_right uu____646 FStar_Syntax_Syntax.fv_to_tm  in
          FStar_Pervasives_Native.Some uu____645  in
        let fallback uu____656 =
          let uu____657 = FStar_Ident.text_of_id op  in
          match uu____657 with
          | "=" ->
              r FStar_Parser_Const.op_Eq FStar_Syntax_Syntax.delta_equational
          | ":=" ->
              r FStar_Parser_Const.write_lid
                FStar_Syntax_Syntax.delta_equational
          | "<" ->
              r FStar_Parser_Const.op_LT FStar_Syntax_Syntax.delta_equational
          | "<=" ->
              r FStar_Parser_Const.op_LTE
                FStar_Syntax_Syntax.delta_equational
          | ">" ->
              r FStar_Parser_Const.op_GT FStar_Syntax_Syntax.delta_equational
          | ">=" ->
              r FStar_Parser_Const.op_GTE
                FStar_Syntax_Syntax.delta_equational
          | "&&" ->
              r FStar_Parser_Const.op_And
                FStar_Syntax_Syntax.delta_equational
          | "||" ->
              r FStar_Parser_Const.op_Or FStar_Syntax_Syntax.delta_equational
          | "+" ->
              r FStar_Parser_Const.op_Addition
                FStar_Syntax_Syntax.delta_equational
          | "-" when arity = Prims.int_one ->
              r FStar_Parser_Const.op_Minus
                FStar_Syntax_Syntax.delta_equational
          | "-" ->
              r FStar_Parser_Const.op_Subtraction
                FStar_Syntax_Syntax.delta_equational
          | "/" ->
              r FStar_Parser_Const.op_Division
                FStar_Syntax_Syntax.delta_equational
          | "%" ->
              r FStar_Parser_Const.op_Modulus
                FStar_Syntax_Syntax.delta_equational
          | "!" ->
              r FStar_Parser_Const.read_lid
                FStar_Syntax_Syntax.delta_equational
          | "@" ->
              let uu____678 = FStar_Options.ml_ish ()  in
              if uu____678
              then
                r FStar_Parser_Const.list_append_lid
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                     (Prims.of_int (2)))
              else
                r FStar_Parser_Const.list_tot_append_lid
                  (FStar_Syntax_Syntax.Delta_equational_at_level
                     (Prims.of_int (2)))
          | "|>" ->
              r FStar_Parser_Const.pipe_right_lid
                FStar_Syntax_Syntax.delta_equational
          | "<|" ->
              r FStar_Parser_Const.pipe_left_lid
                FStar_Syntax_Syntax.delta_equational
          | "<>" ->
              r FStar_Parser_Const.op_notEq
                FStar_Syntax_Syntax.delta_equational
          | "~" ->
              r FStar_Parser_Const.not_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level
                   (Prims.of_int (2)))
          | "==" ->
              r FStar_Parser_Const.eq2_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level
                   (Prims.of_int (2)))
          | "<<" ->
              r FStar_Parser_Const.precedes_lid
                FStar_Syntax_Syntax.delta_constant
          | "/\\" ->
              r FStar_Parser_Const.and_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          | "\\/" ->
              r FStar_Parser_Const.or_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          | "==>" ->
              r FStar_Parser_Const.imp_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level Prims.int_one)
          | "<==>" ->
              r FStar_Parser_Const.iff_lid
                (FStar_Syntax_Syntax.Delta_constant_at_level
                   (Prims.of_int (2)))
          | uu____703 -> FStar_Pervasives_Native.None  in
        let uu____705 =
          let uu____708 =
            let uu____709 = FStar_Ident.text_of_id op  in
            let uu____711 = FStar_Ident.range_of_id op  in
            compile_op_lid arity uu____709 uu____711  in
          desugar_name'
            (fun t  ->
               let uu___177_719 = t  in
               let uu____720 = FStar_Ident.range_of_id op  in
               {
                 FStar_Syntax_Syntax.n = (uu___177_719.FStar_Syntax_Syntax.n);
                 FStar_Syntax_Syntax.pos = uu____720;
                 FStar_Syntax_Syntax.vars =
                   (uu___177_719.FStar_Syntax_Syntax.vars)
               }) env true uu____708
           in
        match uu____705 with
        | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
        | uu____725 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____740 =
      FStar_Util.remove_dups
        (fun x  ->
           fun y  ->
             let uu____749 = FStar_Ident.text_of_id x  in
             let uu____751 = FStar_Ident.text_of_id y  in
             uu____749 = uu____751) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              let uu____764 = FStar_Ident.text_of_id x  in
              let uu____766 = FStar_Ident.text_of_id y  in
              FStar_String.compare uu____764 uu____766)) uu____740
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____801 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____805 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____805 with | (env1,uu____817) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____820,term) ->
          let uu____822 = free_type_vars env term  in (env, uu____822)
      | FStar_Parser_AST.TAnnotated (id,uu____828) ->
          let uu____829 = FStar_Syntax_DsEnv.push_bv env id  in
          (match uu____829 with | (env1,uu____841) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____845 = free_type_vars env t  in (env, uu____845)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____852 =
        let uu____853 = unparen t  in uu____853.FStar_Parser_AST.tm  in
      match uu____852 with
      | FStar_Parser_AST.Labeled uu____856 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____869 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____869 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____874 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____877 -> []
      | FStar_Parser_AST.Uvar uu____878 -> []
      | FStar_Parser_AST.Var uu____879 -> []
      | FStar_Parser_AST.Projector uu____880 -> []
      | FStar_Parser_AST.Discrim uu____885 -> []
      | FStar_Parser_AST.Name uu____886 -> []
      | FStar_Parser_AST.Requires (t1,uu____888) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____896) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____903,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____922,ts) ->
          FStar_List.collect
            (fun uu____943  ->
               match uu____943 with | (t1,uu____951) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____952,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____960) ->
          let uu____961 = free_type_vars env t1  in
          let uu____964 = free_type_vars env t2  in
          FStar_List.append uu____961 uu____964
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____969 = free_type_vars_b env b  in
          (match uu____969 with
           | (env1,f) ->
               let uu____984 = free_type_vars env1 t1  in
               FStar_List.append f uu____984)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1001 =
            FStar_List.fold_left
              (fun uu____1025  ->
                 fun bt  ->
                   match uu____1025 with
                   | (env1,free) ->
                       let uu____1049 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1064 = free_type_vars env1 body  in
                             (env1, uu____1064)
                          in
                       (match uu____1049 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1001 with
           | (env1,free) ->
               let uu____1093 = free_type_vars env1 body  in
               FStar_List.append free uu____1093)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1102 =
            FStar_List.fold_left
              (fun uu____1122  ->
                 fun binder  ->
                   match uu____1122 with
                   | (env1,free) ->
                       let uu____1142 = free_type_vars_b env1 binder  in
                       (match uu____1142 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1102 with
           | (env1,free) ->
               let uu____1173 = free_type_vars env1 body  in
               FStar_List.append free uu____1173)
      | FStar_Parser_AST.Project (t1,uu____1177) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init,steps) ->
          let uu____1188 = free_type_vars env rel  in
          let uu____1191 =
            let uu____1194 = free_type_vars env init  in
            let uu____1197 =
              FStar_List.collect
                (fun uu____1206  ->
                   match uu____1206 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1212 = free_type_vars env rel1  in
                       let uu____1215 =
                         let uu____1218 = free_type_vars env just  in
                         let uu____1221 = free_type_vars env next  in
                         FStar_List.append uu____1218 uu____1221  in
                       FStar_List.append uu____1212 uu____1215) steps
               in
            FStar_List.append uu____1194 uu____1197  in
          FStar_List.append uu____1188 uu____1191
      | FStar_Parser_AST.Abs uu____1224 -> []
      | FStar_Parser_AST.Let uu____1231 -> []
      | FStar_Parser_AST.LetOpen uu____1252 -> []
      | FStar_Parser_AST.If uu____1257 -> []
      | FStar_Parser_AST.QForall uu____1264 -> []
      | FStar_Parser_AST.QExists uu____1283 -> []
      | FStar_Parser_AST.Record uu____1302 -> []
      | FStar_Parser_AST.Match uu____1315 -> []
      | FStar_Parser_AST.TryWith uu____1330 -> []
      | FStar_Parser_AST.Bind uu____1345 -> []
      | FStar_Parser_AST.Quote uu____1352 -> []
      | FStar_Parser_AST.VQuote uu____1357 -> []
      | FStar_Parser_AST.Antiquote uu____1358 -> []
      | FStar_Parser_AST.Seq uu____1359 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1413 =
        let uu____1414 = unparen t1  in uu____1414.FStar_Parser_AST.tm  in
      match uu____1413 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1456 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1481 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1481  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1504 =
                     let uu____1505 =
                       let uu____1510 =
                         let uu____1511 = FStar_Ident.range_of_id x  in
                         tm_type uu____1511  in
                       (x, uu____1510)  in
                     FStar_Parser_AST.TAnnotated uu____1505  in
                   let uu____1512 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1504 uu____1512
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t))
             t.FStar_Parser_AST.range t.FStar_Parser_AST.level
            in
         result)
  
let (close_fun :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1530 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1530  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1553 =
                     let uu____1554 =
                       let uu____1559 =
                         let uu____1560 = FStar_Ident.range_of_id x  in
                         tm_type uu____1560  in
                       (x, uu____1559)  in
                     FStar_Parser_AST.TAnnotated uu____1554  in
                   let uu____1561 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1553 uu____1561
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1563 =
             let uu____1564 = unparen t  in uu____1564.FStar_Parser_AST.tm
              in
           match uu____1563 with
           | FStar_Parser_AST.Product uu____1565 -> t
           | uu____1572 ->
               FStar_Parser_AST.mk_term
                 (FStar_Parser_AST.App
                    ((FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Name
                           FStar_Parser_Const.effect_Tot_lid)
                        t.FStar_Parser_AST.range t.FStar_Parser_AST.level),
                      t, FStar_Parser_AST.Nothing)) t.FStar_Parser_AST.range
                 t.FStar_Parser_AST.level
            in
         let result =
           FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (binders, t1))
             t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level
            in
         result)
  
let rec (uncurry :
  FStar_Parser_AST.binder Prims.list ->
    FStar_Parser_AST.term ->
      (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term))
  =
  fun bs  ->
    fun t  ->
      match t.FStar_Parser_AST.tm with
      | FStar_Parser_AST.Product (binders,t1) ->
          uncurry (FStar_List.append bs binders) t1
      | uu____1609 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1620 -> true
    | FStar_Parser_AST.PatTvar (uu____1624,uu____1625) -> true
    | FStar_Parser_AST.PatVar (uu____1631,uu____1632) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1639) -> is_var_pattern p1
    | uu____1652 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1663) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1676;
           FStar_Parser_AST.prange = uu____1677;_},uu____1678)
        -> true
    | uu____1690 -> false
  
let (replace_unit_pattern :
  FStar_Parser_AST.pattern -> FStar_Parser_AST.pattern) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatConst (FStar_Const.Const_unit ) ->
        FStar_Parser_AST.mk_pattern
          (FStar_Parser_AST.PatAscribed
             ((FStar_Parser_AST.mk_pattern
                 (FStar_Parser_AST.PatWild FStar_Pervasives_Native.None)
                 p.FStar_Parser_AST.prange),
               ((unit_ty p.FStar_Parser_AST.prange),
                 FStar_Pervasives_Native.None))) p.FStar_Parser_AST.prange
    | uu____1706 -> p
  
let rec (destruct_app_pattern :
  FStar_Syntax_DsEnv.env ->
    Prims.bool ->
      FStar_Parser_AST.pattern ->
        ((FStar_Ident.ident,FStar_Ident.lident) FStar_Util.either *
          FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term *
          FStar_Parser_AST.term FStar_Pervasives_Native.option)
          FStar_Pervasives_Native.option))
  =
  fun env  ->
    fun is_top_level  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1779 = destruct_app_pattern env is_top_level p1  in
            (match uu____1779 with
             | (name,args,uu____1822) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1872);
               FStar_Parser_AST.prange = uu____1873;_},args)
            when is_top_level ->
            let uu____1883 =
              let uu____1888 = FStar_Syntax_DsEnv.qualify env id  in
              FStar_Util.Inr uu____1888  in
            (uu____1883, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1910);
               FStar_Parser_AST.prange = uu____1911;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1941 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____1993 -> acc
      | FStar_Parser_AST.PatConst uu____1996 -> acc
      | FStar_Parser_AST.PatName uu____1997 -> acc
      | FStar_Parser_AST.PatOp uu____1998 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x,uu____2006) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x,uu____2012) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____2021) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____2038 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____2038
      | FStar_Parser_AST.PatAscribed (pat,uu____2046) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           let uu____2074 =
             let uu____2076 = FStar_Ident.text_of_id id1  in
             let uu____2078 = FStar_Ident.text_of_id id2  in
             uu____2076 = uu____2078  in
           if uu____2074 then Prims.int_zero else Prims.int_one)
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2126 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2167 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (is_implicit : bnd -> Prims.bool) =
  fun b  ->
    match b with
    | LocalBinder
        (uu____2215,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2216))
        -> true
    | uu____2219 -> false
  
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2230  ->
    match uu___3_2230 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2237 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2270  ->
    match uu____2270 with
    | (attrs,n,t,e,pos) ->
        {
          FStar_Syntax_Syntax.lbname = n;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid;
          FStar_Syntax_Syntax.lbdef = e;
          FStar_Syntax_Syntax.lbattrs = attrs;
          FStar_Syntax_Syntax.lbpos = pos
        }
  
let (no_annot_abs :
  FStar_Syntax_Syntax.binders ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun bs  ->
    fun t  -> FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None
  
let (mk_ref_read :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2352 =
        let uu____2369 =
          let uu____2372 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2372  in
        let uu____2373 =
          let uu____2384 =
            let uu____2393 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2393)  in
          [uu____2384]  in
        (uu____2369, uu____2373)  in
      FStar_Syntax_Syntax.Tm_app uu____2352  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2442 =
        let uu____2459 =
          let uu____2462 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2462  in
        let uu____2463 =
          let uu____2474 =
            let uu____2483 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2483)  in
          [uu____2474]  in
        (uu____2459, uu____2463)  in
      FStar_Syntax_Syntax.Tm_app uu____2442  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_assign :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Range.range ->
        FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun t1  ->
    fun t2  ->
      fun pos  ->
        let tm =
          let uu____2546 =
            let uu____2563 =
              let uu____2566 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2566  in
            let uu____2567 =
              let uu____2578 =
                let uu____2587 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2587)  in
              let uu____2595 =
                let uu____2606 =
                  let uu____2615 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2615)  in
                [uu____2606]  in
              uu____2578 :: uu____2595  in
            (uu____2563, uu____2567)  in
          FStar_Syntax_Syntax.Tm_app uu____2546  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2675 =
        let uu____2690 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2709  ->
               match uu____2709 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2720;
                    FStar_Syntax_Syntax.index = uu____2721;
                    FStar_Syntax_Syntax.sort = t;_},uu____2723)
                   ->
                   let uu____2731 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2731) uu____2690
         in
      FStar_All.pipe_right bs uu____2675  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2747 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2765 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2793 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2814,uu____2815,bs,t,uu____2818,uu____2819)
                            ->
                            let uu____2828 = bs_univnames bs  in
                            let uu____2831 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2828 uu____2831
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2834,uu____2835,t,uu____2837,uu____2838,uu____2839)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2846 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2793 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___564_2855 = s  in
        let uu____2856 =
          let uu____2857 =
            let uu____2866 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2884,bs,t,lids1,lids2) ->
                          let uu___575_2897 = se  in
                          let uu____2898 =
                            let uu____2899 =
                              let uu____2916 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2917 =
                                let uu____2918 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2918 t  in
                              (lid, uvs, uu____2916, uu____2917, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2899
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2898;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___575_2897.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___575_2897.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___575_2897.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___575_2897.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___575_2897.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2932,t,tlid,n,lids1) ->
                          let uu___585_2943 = se  in
                          let uu____2944 =
                            let uu____2945 =
                              let uu____2961 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2961, tlid, n, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2945  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2944;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___585_2943.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___585_2943.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___585_2943.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___585_2943.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___585_2943.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____2965 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2866, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2857  in
        {
          FStar_Syntax_Syntax.sigel = uu____2856;
          FStar_Syntax_Syntax.sigrng =
            (uu___564_2855.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___564_2855.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___564_2855.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___564_2855.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___564_2855.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2972,t) ->
        let uvs =
          let uu____2975 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2975 FStar_Util.set_elements  in
        let uu___594_2980 = s  in
        let uu____2981 =
          let uu____2982 =
            let uu____2989 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2989)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2982  in
        {
          FStar_Syntax_Syntax.sigel = uu____2981;
          FStar_Syntax_Syntax.sigrng =
            (uu___594_2980.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___594_2980.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___594_2980.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___594_2980.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___594_2980.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3013 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3016 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3023) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3056,(FStar_Util.Inl t,uu____3058),uu____3059)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3106,(FStar_Util.Inr c,uu____3108),uu____3109)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3156 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3158) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3179,(FStar_Util.Inl t,uu____3181),uu____3182) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3229,(FStar_Util.Inr c,uu____3231),uu____3232) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3279 -> empty_set  in
          FStar_Util.set_union uu____3013 uu____3016  in
        let all_lb_univs =
          let uu____3283 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3299 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3299) empty_set)
             in
          FStar_All.pipe_right uu____3283 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___653_3309 = s  in
        let uu____3310 =
          let uu____3311 =
            let uu____3318 =
              let uu____3319 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___656_3331 = lb  in
                        let uu____3332 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3335 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___656_3331.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3332;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___656_3331.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3335;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___656_3331.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___656_3331.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3319)  in
            (uu____3318, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3311  in
        {
          FStar_Syntax_Syntax.sigel = uu____3310;
          FStar_Syntax_Syntax.sigrng =
            (uu___653_3309.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___653_3309.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___653_3309.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___653_3309.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___653_3309.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3344,fml) ->
        let uvs =
          let uu____3347 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3347 FStar_Util.set_elements  in
        let uu___664_3352 = s  in
        let uu____3353 =
          let uu____3354 =
            let uu____3361 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3361)  in
          FStar_Syntax_Syntax.Sig_assume uu____3354  in
        {
          FStar_Syntax_Syntax.sigel = uu____3353;
          FStar_Syntax_Syntax.sigrng =
            (uu___664_3352.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___664_3352.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___664_3352.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___664_3352.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___664_3352.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3363,bs,c,flags) ->
        let uvs =
          let uu____3372 =
            let uu____3375 = bs_univnames bs  in
            let uu____3378 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3375 uu____3378  in
          FStar_All.pipe_right uu____3372 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___675_3386 = s  in
        let uu____3387 =
          let uu____3388 =
            let uu____3401 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3402 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3401, uu____3402, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3388  in
        {
          FStar_Syntax_Syntax.sigel = uu____3387;
          FStar_Syntax_Syntax.sigrng =
            (uu___675_3386.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___675_3386.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___675_3386.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___675_3386.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___675_3386.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs,lax,ses) ->
        let uu___682_3420 = s  in
        let uu____3421 =
          let uu____3422 =
            let uu____3435 = FStar_List.map generalize_annotated_univs ses
               in
            (errs, lax, uu____3435)  in
          FStar_Syntax_Syntax.Sig_fail uu____3422  in
        {
          FStar_Syntax_Syntax.sigel = uu____3421;
          FStar_Syntax_Syntax.sigrng =
            (uu___682_3420.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___682_3420.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___682_3420.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___682_3420.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___682_3420.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3444 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3445 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3446 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3457 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3464 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3472  ->
    match uu___4_3472 with
    | "lift1" -> true
    | "lift2" -> true
    | "pure" -> true
    | "app" -> true
    | "push" -> true
    | "wp_if_then_else" -> true
    | "wp_assert" -> true
    | "wp_assume" -> true
    | "wp_close" -> true
    | "stronger" -> true
    | "ite_wp" -> true
    | "wp_trivial" -> true
    | "ctx" -> true
    | "gctx" -> true
    | "lift_from_pure" -> true
    | "return_wp" -> true
    | "return_elab" -> true
    | "bind_wp" -> true
    | "bind_elab" -> true
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____3521 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3542 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3542)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3568 =
      let uu____3569 = unparen t  in uu____3569.FStar_Parser_AST.tm  in
    match uu____3568 with
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3579)) ->
        let n = FStar_Util.int_of_string repr  in
        (if n < Prims.int_zero
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n,FStar_Util.Inr u) ->
             let uu____3670 = sum_to_universe u n  in
             FStar_Util.Inr uu____3670
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3687 = sum_to_universe u n  in
             FStar_Util.Inr uu____3687
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3703 =
               let uu____3709 =
                 let uu____3711 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3711
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3709)
                in
             FStar_Errors.raise_error uu____3703 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3720 ->
        let rec aux t1 univargs =
          let uu____3757 =
            let uu____3758 = unparen t1  in uu____3758.FStar_Parser_AST.tm
             in
          match uu____3757 with
          | FStar_Parser_AST.App (t2,targ,uu____3766) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3793  ->
                     match uu___5_3793 with
                     | FStar_Util.Inr uu____3800 -> true
                     | uu____3803 -> false) univargs
              then
                let uu____3811 =
                  let uu____3812 =
                    FStar_List.map
                      (fun uu___6_3822  ->
                         match uu___6_3822 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3812  in
                FStar_Util.Inr uu____3811
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3848  ->
                        match uu___7_3848 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3858 -> failwith "impossible")
                     univargs
                    in
                 let uu____3862 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3862)
          | uu____3878 ->
              let uu____3879 =
                let uu____3885 =
                  let uu____3887 =
                    let uu____3889 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3889 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3887  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3885)  in
              FStar_Errors.raise_error uu____3879 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3904 ->
        let uu____3905 =
          let uu____3911 =
            let uu____3913 =
              let uu____3915 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3915 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3913  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3911)  in
        FStar_Errors.raise_error uu____3905 t.FStar_Parser_AST.range
  
let (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n -> int_to_universe n
    | FStar_Util.Inr u1 -> u1
  
let (check_no_aq : FStar_Syntax_Syntax.antiquotations -> unit) =
  fun aq  ->
    match aq with
    | [] -> ()
    | (bv,{
            FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted
              (e,{
                   FStar_Syntax_Syntax.qkind =
                     FStar_Syntax_Syntax.Quote_dynamic ;
                   FStar_Syntax_Syntax.antiquotes = uu____3956;_});
            FStar_Syntax_Syntax.pos = uu____3957;
            FStar_Syntax_Syntax.vars = uu____3958;_})::uu____3959
        ->
        let uu____3990 =
          let uu____3996 =
            let uu____3998 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3998
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____3996)  in
        FStar_Errors.raise_error uu____3990 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4004 ->
        let uu____4023 =
          let uu____4029 =
            let uu____4031 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4031
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4029)  in
        FStar_Errors.raise_error uu____4023 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4044 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4044) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4072 = FStar_List.hd fields  in
        match uu____4072 with
        | (f,uu____4082) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4093 =
              match uu____4093 with
              | (f',uu____4099) ->
                  let uu____4100 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4100
                  then ()
                  else
                    (let msg =
                       let uu____4107 = FStar_Ident.string_of_lid f  in
                       let uu____4109 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4111 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4107 uu____4109 uu____4111
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4116 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4116);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4164 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4171 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4172 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4174,pats1) ->
            let aux out uu____4215 =
              match uu____4215 with
              | (p1,uu____4228) ->
                  let intersection =
                    let uu____4238 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4238 out  in
                  let uu____4241 = FStar_Util.set_is_empty intersection  in
                  if uu____4241
                  then
                    let uu____4246 = pat_vars p1  in
                    FStar_Util.set_union out uu____4246
                  else
                    (let duplicate_bv =
                       let uu____4252 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4252  in
                     let uu____4255 =
                       let uu____4261 =
                         let uu____4263 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4263
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4261)
                        in
                     FStar_Errors.raise_error uu____4255 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4287 = pat_vars p  in
          FStar_All.pipe_right uu____4287 (fun uu____4292  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4316 =
              let uu____4318 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4318  in
            if uu____4316
            then ()
            else
              (let nonlinear_vars =
                 let uu____4327 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4327  in
               let first_nonlinear_var =
                 let uu____4331 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4331  in
               let uu____4334 =
                 let uu____4340 =
                   let uu____4342 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4342
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4340)  in
               FStar_Errors.raise_error uu____4334 r)
             in
          FStar_List.iter aux ps
  
let (smt_pat_lid : FStar_Range.range -> FStar_Ident.lident) =
  fun r  -> FStar_Ident.set_lid_range FStar_Parser_Const.smtpat_lid r 
let (smt_pat_or_lid : FStar_Range.range -> FStar_Ident.lident) =
  fun r  -> FStar_Ident.set_lid_range FStar_Parser_Const.smtpatOr_lid r 
let rec (desugar_data_pat :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top_level_ascr_allowed  ->
    fun env  ->
      fun p  ->
        let resolvex l e x =
          let uu____4669 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4676 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4678 = FStar_Ident.text_of_id x  in
                 uu____4676 = uu____4678) l
             in
          match uu____4669 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4692 ->
              let uu____4695 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4695 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4836 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4858 =
                  let uu____4864 =
                    let uu____4866 = FStar_Ident.text_of_id op  in
                    let uu____4868 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4866
                      uu____4868
                     in
                  let uu____4870 = FStar_Ident.range_of_id op  in
                  (uu____4864, uu____4870)  in
                FStar_Ident.mk_ident uu____4858  in
              let p2 =
                let uu___907_4873 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___907_4873.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4890 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4893 = aux loc env1 p2  in
                match uu____4893 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____4949 =
                      match binder with
                      | LetBinder uu____4970 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____4995 = close_fun env1 t  in
                            desugar_term env1 uu____4995  in
                          let x1 =
                            let uu___933_4997 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___933_4997.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___933_4997.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____4949 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5043 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5044 -> ()
                           | uu____5045 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5046 ->
                               FStar_Errors.raise_error
                                 (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                                   "Type ascriptions within patterns are only allowed on variables")
                                 orig.FStar_Parser_AST.prange);
                          (loc1, env', binder1, p3,
                            (FStar_List.append annots' annots))))))
          | FStar_Parser_AST.PatWild aq ->
              let aq1 = trans_aqual env1 aq  in
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5064 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5064, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5077 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5077, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5095 = resolvex loc env1 x  in
              (match uu____5095 with
               | (loc1,env2,xbv) ->
                   let uu____5127 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5127, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5145 = resolvex loc env1 x  in
              (match uu____5145 with
               | (loc1,env2,xbv) ->
                   let uu____5177 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5177, []))
          | FStar_Parser_AST.PatName l ->
              let l1 =
                FStar_Syntax_DsEnv.fail_or env1
                  (FStar_Syntax_DsEnv.try_lookup_datacon env1) l
                 in
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5191 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5191, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5219;_},args)
              ->
              let uu____5225 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5286  ->
                       match uu____5286 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5367 = aux loc1 env2 arg  in
                           (match uu____5367 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5225 with
               | (loc1,env2,annots,args1) ->
                   let l1 =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                      in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____5539 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5539, annots))
          | FStar_Parser_AST.PatApp uu____5555 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5583 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5633  ->
                       match uu____5633 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5694 = aux loc1 env2 pat  in
                           (match uu____5694 with
                            | (loc2,env3,uu____5733,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5583 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5827 =
                       let uu____5830 =
                         let uu____5837 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5837  in
                       let uu____5838 =
                         let uu____5839 =
                           let uu____5853 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5853, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5839  in
                       FStar_All.pipe_left uu____5830 uu____5838  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____5887 =
                              let uu____5888 =
                                let uu____5902 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5902, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____5888  in
                            FStar_All.pipe_left (pos_r r) uu____5887) pats1
                       uu____5827
                      in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                     annots))
          | FStar_Parser_AST.PatTuple (args,dep) ->
              let uu____5958 =
                FStar_List.fold_left
                  (fun uu____6017  ->
                     fun p2  ->
                       match uu____6017 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6099 = aux loc1 env2 p2  in
                           (match uu____6099 with
                            | (loc2,env3,uu____6143,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____5958 with
               | (loc1,env2,annots,args1) ->
                   let args2 = FStar_List.rev args1  in
                   let l =
                     if dep
                     then
                       FStar_Parser_Const.mk_dtuple_data_lid
                         (FStar_List.length args2) p1.FStar_Parser_AST.prange
                     else
                       FStar_Parser_Const.mk_tuple_data_lid
                         (FStar_List.length args2) p1.FStar_Parser_AST.prange
                      in
                   let constr =
                     FStar_Syntax_DsEnv.fail_or env2
                       (FStar_Syntax_DsEnv.try_lookup_lid env2) l
                      in
                   let l1 =
                     match constr.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                     | uu____6306 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6309 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6309, annots))
          | FStar_Parser_AST.PatRecord [] ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatRecord fields ->
              let record =
                check_fields env1 fields p1.FStar_Parser_AST.prange  in
              let fields1 =
                FStar_All.pipe_right fields
                  (FStar_List.map
                     (fun uu____6386  ->
                        match uu____6386 with
                        | (f,p2) ->
                            let uu____6397 = FStar_Ident.ident_of_lid f  in
                            (uu____6397, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6417  ->
                        match uu____6417 with
                        | (f,uu____6423) ->
                            let uu____6424 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6452  ->
                                      match uu____6452 with
                                      | (g,uu____6459) ->
                                          let uu____6460 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6462 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6460 = uu____6462))
                               in
                            (match uu____6424 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6469,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6476 =
                  let uu____6477 =
                    let uu____6484 =
                      let uu____6485 =
                        let uu____6486 =
                          let uu____6487 =
                            let uu____6488 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6488
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6487  in
                        FStar_Parser_AST.PatName uu____6486  in
                      FStar_Parser_AST.mk_pattern uu____6485
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6484, args)  in
                  FStar_Parser_AST.PatApp uu____6477  in
                FStar_Parser_AST.mk_pattern uu____6476
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6493 = aux loc env1 app  in
              (match uu____6493 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6570 =
                           let uu____6571 =
                             let uu____6585 =
                               let uu___1083_6586 = fv  in
                               let uu____6587 =
                                 let uu____6590 =
                                   let uu____6591 =
                                     let uu____6598 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6598)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6591
                                    in
                                 FStar_Pervasives_Native.Some uu____6590  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1083_6586.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1083_6586.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6587
                               }  in
                             (uu____6585, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6571  in
                         FStar_All.pipe_left pos uu____6570
                     | uu____6624 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6708 = aux' true loc env1 p2  in
              (match uu____6708 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6761 =
                     FStar_List.fold_left
                       (fun uu____6809  ->
                          fun p4  ->
                            match uu____6809 with
                            | (loc2,env3,ps1) ->
                                let uu____6874 = aux' true loc2 env3 p4  in
                                (match uu____6874 with
                                 | (loc3,env4,uu____6912,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6761 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7073 ->
              let uu____7074 = aux' true loc env1 p1  in
              (match uu____7074 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7165 = aux_maybe_or env p  in
        match uu____7165 with
        | (env1,b,pats) ->
            ((let uu____7220 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7220
                p.FStar_Parser_AST.prange);
             (env1, b, pats))

and (desugar_binding_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top  ->
    fun env  ->
      fun p  ->
        if top
        then
          let mklet x ty tacopt =
            let uu____7294 =
              let uu____7295 =
                let uu____7306 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7306, (ty, tacopt))  in
              LetBinder uu____7295  in
            (env, uu____7294, [])  in
          let op_to_ident x =
            let uu____7323 =
              let uu____7329 =
                let uu____7331 = FStar_Ident.text_of_id x  in
                let uu____7333 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7331
                  uu____7333
                 in
              let uu____7335 = FStar_Ident.range_of_id x  in
              (uu____7329, uu____7335)  in
            FStar_Ident.mk_ident uu____7323  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7346 = op_to_ident x  in
              mklet uu____7346 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7348) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7354;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7370 = op_to_ident x  in
              let uu____7371 = desugar_term env t  in
              mklet uu____7370 uu____7371 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7373);
                 FStar_Parser_AST.prange = uu____7374;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7394 = desugar_term env t  in
              mklet x uu____7394 tacopt1
          | uu____7395 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7408 = desugar_data_pat true env p  in
           match uu____7408 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7438;
                      FStar_Syntax_Syntax.p = uu____7439;_},uu____7440)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7453;
                      FStar_Syntax_Syntax.p = uu____7454;_},uu____7455)::[]
                     -> []
                 | uu____7468 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7476  ->
    fun env  ->
      fun pat  ->
        let uu____7480 = desugar_data_pat false env pat  in
        match uu____7480 with | (env1,uu____7497,pat1) -> (env1, pat1)

and (desugar_match_pat :
  env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list)) =
  fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

and (desugar_term_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env false  in
      desugar_term_maybe_top false env1 e

and (desugar_term :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____7519 = desugar_term_aq env e  in
      match uu____7519 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_typ_aq :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun env  ->
    fun e  ->
      let env1 = FStar_Syntax_DsEnv.set_expect_typ env true  in
      desugar_term_maybe_top false env1 e

and (desugar_typ :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun e  ->
      let uu____7538 = desugar_typ_aq env e  in
      match uu____7538 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7548  ->
        fun range  ->
          match uu____7548 with
          | (signedness,width) ->
              let tnm =
                Prims.op_Hat "FStar."
                  (Prims.op_Hat
                     (match signedness with
                      | FStar_Const.Unsigned  -> "U"
                      | FStar_Const.Signed  -> "")
                     (Prims.op_Hat "Int"
                        (match width with
                         | FStar_Const.Int8  -> "8"
                         | FStar_Const.Int16  -> "16"
                         | FStar_Const.Int32  -> "32"
                         | FStar_Const.Int64  -> "64")))
                 in
              ((let uu____7570 =
                  let uu____7572 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7572  in
                if uu____7570
                then
                  let uu____7575 =
                    let uu____7581 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7581)  in
                  FStar_Errors.log_issue range uu____7575
                else ());
               (let private_intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat ".__"
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let intro_nm =
                  Prims.op_Hat tnm
                    (Prims.op_Hat "."
                       (Prims.op_Hat
                          (match signedness with
                           | FStar_Const.Unsigned  -> "u"
                           | FStar_Const.Signed  -> "") "int_to_t"))
                   in
                let lid =
                  let uu____7602 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7602 range  in
                let lid1 =
                  let uu____7606 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7606 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7616 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7616 range  in
                           let private_fv =
                             let uu____7618 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7618 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1250_7619 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1250_7619.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1250_7619.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7620 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7624 =
                        let uu____7630 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7630)
                         in
                      FStar_Errors.raise_error uu____7624 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7650 =
                  let uu____7657 =
                    let uu____7658 =
                      let uu____7675 =
                        let uu____7686 =
                          let uu____7695 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7695)  in
                        [uu____7686]  in
                      (lid1, uu____7675)  in
                    FStar_Syntax_Syntax.Tm_app uu____7658  in
                  FStar_Syntax_Syntax.mk uu____7657  in
                uu____7650 FStar_Pervasives_Native.None range))

and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let noaqs = []  in
        let join_aqs aqs = FStar_List.flatten aqs  in
        let setpos e =
          let uu___1266_7814 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1266_7814.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1266_7814.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7817 =
          let uu____7818 = unparen top  in uu____7818.FStar_Parser_AST.tm  in
        match uu____7817 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7823 ->
            let uu____7832 = desugar_formula env top  in (uu____7832, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7841 = desugar_formula env t  in (uu____7841, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7850 = desugar_formula env t  in (uu____7850, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7877 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7877, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7879 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7879, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____7886 = FStar_Ident.text_of_id id  in uu____7886 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____7892 =
                let uu____7893 =
                  let uu____7900 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7900, args)  in
                FStar_Parser_AST.Op uu____7893  in
              FStar_Parser_AST.mk_term uu____7892 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7905 =
              let uu____7906 =
                let uu____7907 =
                  let uu____7914 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7914, [e])  in
                FStar_Parser_AST.Op uu____7907  in
              FStar_Parser_AST.mk_term uu____7906 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7905
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7926 = FStar_Ident.text_of_id op_star  in
             uu____7926 = "*") &&
              (let uu____7931 = op_as_term env (Prims.of_int (2)) op_star  in
               FStar_All.pipe_right uu____7931 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____7955 = FStar_Ident.text_of_id id  in
                   uu____7955 = "*") &&
                    (let uu____7960 =
                       op_as_term env (Prims.of_int (2)) op_star  in
                     FStar_All.pipe_right uu____7960 FStar_Option.isNone)
                  ->
                  let uu____7967 = flatten t1  in
                  FStar_List.append uu____7967 [t2]
              | uu____7970 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1311_7975 = top  in
              let uu____7976 =
                let uu____7977 =
                  let uu____7988 =
                    FStar_List.map
                      (fun uu____7999  -> FStar_Util.Inr uu____7999) terms
                     in
                  (uu____7988, rhs)  in
                FStar_Parser_AST.Sum uu____7977  in
              {
                FStar_Parser_AST.tm = uu____7976;
                FStar_Parser_AST.range =
                  (uu___1311_7975.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1311_7975.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8007 =
              let uu____8008 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8008  in
            (uu____8007, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8014 =
              let uu____8020 =
                let uu____8022 =
                  let uu____8024 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8024 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8022  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8020)  in
            FStar_Errors.raise_error uu____8014 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8039 = op_as_term env (FStar_List.length args) s  in
            (match uu____8039 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8046 =
                   let uu____8052 =
                     let uu____8054 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8054
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8052)
                    in
                 FStar_Errors.raise_error uu____8046
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8069 =
                     let uu____8094 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8156 = desugar_term_aq env t  in
                               match uu____8156 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8094 FStar_List.unzip  in
                   (match uu____8069 with
                    | (args1,aqs) ->
                        let uu____8289 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8289, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8306)::[]) when
            let uu____8321 = FStar_Ident.string_of_lid n  in
            uu____8321 = "SMTPat" ->
            let uu____8325 =
              let uu___1340_8326 = top  in
              let uu____8327 =
                let uu____8328 =
                  let uu____8335 =
                    let uu___1342_8336 = top  in
                    let uu____8337 =
                      let uu____8338 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8338  in
                    {
                      FStar_Parser_AST.tm = uu____8337;
                      FStar_Parser_AST.range =
                        (uu___1342_8336.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1342_8336.FStar_Parser_AST.level)
                    }  in
                  (uu____8335, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8328  in
              {
                FStar_Parser_AST.tm = uu____8327;
                FStar_Parser_AST.range =
                  (uu___1340_8326.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1340_8326.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8325
        | FStar_Parser_AST.Construct (n,(a,uu____8341)::[]) when
            let uu____8356 = FStar_Ident.string_of_lid n  in
            uu____8356 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8363 =
                let uu___1352_8364 = top  in
                let uu____8365 =
                  let uu____8366 =
                    let uu____8373 =
                      let uu___1354_8374 = top  in
                      let uu____8375 =
                        let uu____8376 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8376  in
                      {
                        FStar_Parser_AST.tm = uu____8375;
                        FStar_Parser_AST.range =
                          (uu___1354_8374.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1354_8374.FStar_Parser_AST.level)
                      }  in
                    (uu____8373, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8366  in
                {
                  FStar_Parser_AST.tm = uu____8365;
                  FStar_Parser_AST.range =
                    (uu___1352_8364.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1352_8364.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8363))
        | FStar_Parser_AST.Construct (n,(a,uu____8379)::[]) when
            let uu____8394 = FStar_Ident.string_of_lid n  in
            uu____8394 = "SMTPatOr" ->
            let uu____8398 =
              let uu___1363_8399 = top  in
              let uu____8400 =
                let uu____8401 =
                  let uu____8408 =
                    let uu___1365_8409 = top  in
                    let uu____8410 =
                      let uu____8411 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8411  in
                    {
                      FStar_Parser_AST.tm = uu____8410;
                      FStar_Parser_AST.range =
                        (uu___1365_8409.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1365_8409.FStar_Parser_AST.level)
                    }  in
                  (uu____8408, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8401  in
              {
                FStar_Parser_AST.tm = uu____8400;
                FStar_Parser_AST.range =
                  (uu___1363_8399.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1363_8399.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8398
        | FStar_Parser_AST.Name lid when
            let uu____8413 = FStar_Ident.string_of_lid lid  in
            uu____8413 = "Type0" ->
            let uu____8417 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8417, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8419 = FStar_Ident.string_of_lid lid  in
            uu____8419 = "Type" ->
            let uu____8423 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8423, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8440 = FStar_Ident.string_of_lid lid  in
            uu____8440 = "Type" ->
            let uu____8444 =
              let uu____8445 =
                let uu____8446 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8446  in
              mk uu____8445  in
            (uu____8444, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8448 = FStar_Ident.string_of_lid lid  in
            uu____8448 = "Effect" ->
            let uu____8452 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8452, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8454 = FStar_Ident.string_of_lid lid  in
            uu____8454 = "True" ->
            let uu____8458 =
              let uu____8459 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8459
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8458, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8461 = FStar_Ident.string_of_lid lid  in
            uu____8461 = "False" ->
            let uu____8465 =
              let uu____8466 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8466
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8465, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8471 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8471) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8475 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8475 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8484 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8484, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8486 =
                   let uu____8488 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8488 txt
                    in
                 failwith uu____8486)
        | FStar_Parser_AST.Var l ->
            let uu____8496 = desugar_name mk setpos env true l  in
            (uu____8496, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8504 = desugar_name mk setpos env true l  in
            (uu____8504, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8521 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8521 with
              | FStar_Pervasives_Native.Some uu____8531 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8539 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8539 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8557 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8578 =
                   let uu____8579 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8579  in
                 (uu____8578, noaqs)
             | uu____8585 ->
                 let uu____8593 =
                   let uu____8599 =
                     let uu____8601 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8601
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8599)  in
                 FStar_Errors.raise_error uu____8593
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8610 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8610 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8617 =
                   let uu____8623 =
                     let uu____8625 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8625
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8623)
                    in
                 FStar_Errors.raise_error uu____8617
                   top.FStar_Parser_AST.range
             | uu____8633 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8637 = desugar_name mk setpos env true lid'  in
                 (uu____8637, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8658 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8658 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8677 ->
                      let uu____8684 =
                        FStar_Util.take
                          (fun uu____8708  ->
                             match uu____8708 with
                             | (uu____8714,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8684 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8759 =
                             let uu____8784 =
                               FStar_List.map
                                 (fun uu____8827  ->
                                    match uu____8827 with
                                    | (t,imp) ->
                                        let uu____8844 =
                                          desugar_term_aq env t  in
                                        (match uu____8844 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8784 FStar_List.unzip
                              in
                           (match uu____8759 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____8987 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____8987, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9006 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9006 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9014 =
                         let uu____9016 =
                           let uu____9018 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9018 " not found"  in
                         Prims.op_Hat "Constructor " uu____9016  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9014)
                   | FStar_Pervasives_Native.Some uu____9023 ->
                       let uu____9024 =
                         let uu____9026 =
                           let uu____9028 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9028
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9026  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9024)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9057  ->
                 match uu___8_9057 with
                 | FStar_Util.Inr uu____9063 -> true
                 | uu____9065 -> false) binders
            ->
            let terms =
              let uu____9074 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9091  ->
                        match uu___9_9091 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9097 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9074 [t]  in
            let uu____9099 =
              let uu____9124 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9181 = desugar_typ_aq env t1  in
                        match uu____9181 with
                        | (t',aq) ->
                            let uu____9192 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9192, aq)))
                 in
              FStar_All.pipe_right uu____9124 FStar_List.unzip  in
            (match uu____9099 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9302 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9302
                    in
                 let uu____9311 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9311, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9338 =
              let uu____9355 =
                let uu____9362 =
                  let uu____9369 =
                    FStar_All.pipe_left
                      (fun uu____9378  -> FStar_Util.Inl uu____9378)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9369]  in
                FStar_List.append binders uu____9362  in
              FStar_List.fold_left
                (fun uu____9423  ->
                   fun b  ->
                     match uu____9423 with
                     | (env1,tparams,typs) ->
                         let uu____9484 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9499 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9499)
                            in
                         (match uu____9484 with
                          | (xopt,t1) ->
                              let uu____9524 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9533 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9533)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9524 with
                               | (env2,x) ->
                                   let uu____9553 =
                                     let uu____9556 =
                                       let uu____9559 =
                                         let uu____9560 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9560
                                          in
                                       [uu____9559]  in
                                     FStar_List.append typs uu____9556  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1494_9586 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1494_9586.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1494_9586.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9553)))) (env, [], []) uu____9355
               in
            (match uu____9338 with
             | (env1,uu____9614,targs) ->
                 let tup =
                   let uu____9637 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9637
                    in
                 let uu____9638 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9638, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9657 = uncurry binders t  in
            (match uu____9657 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9701 =
                   match uu___10_9701 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9718 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9718
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9742 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9742 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9775 = aux env [] bs  in (uu____9775, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9784 = desugar_binder env b  in
            (match uu____9784 with
             | (FStar_Pervasives_Native.None ,uu____9795) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9810 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9810 with
                  | ((x,uu____9826),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9839 =
                        let uu____9840 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9840  in
                      (uu____9839, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____9918 = FStar_Util.set_is_empty i  in
                    if uu____9918
                    then
                      let uu____9923 = FStar_Util.set_union acc set  in
                      aux uu____9923 sets2
                    else
                      (let uu____9928 =
                         let uu____9929 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9929  in
                       FStar_Pervasives_Native.Some uu____9928)
                 in
              let uu____9932 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9932 sets  in
            ((let uu____9936 = check_disjoint bvss  in
              match uu____9936 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____9940 =
                    let uu____9946 =
                      let uu____9948 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____9948
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9946)
                     in
                  let uu____9952 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____9940 uu____9952);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9960 =
                FStar_List.fold_left
                  (fun uu____9980  ->
                     fun pat  ->
                       match uu____9980 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10006,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10016 =
                                  let uu____10019 = free_type_vars env1 t  in
                                  FStar_List.append uu____10019 ftvs  in
                                (env1, uu____10016)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10024,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10035 =
                                  let uu____10038 = free_type_vars env1 t  in
                                  let uu____10041 =
                                    let uu____10044 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10044 ftvs  in
                                  FStar_List.append uu____10038 uu____10041
                                   in
                                (env1, uu____10035)
                            | uu____10049 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____9960 with
              | (uu____10058,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10070 =
                      FStar_All.pipe_right ftv1
                        (FStar_List.map
                           (fun a  ->
                              FStar_Parser_AST.mk_pattern
                                (FStar_Parser_AST.PatTvar
                                   (a,
                                     (FStar_Pervasives_Native.Some
                                        FStar_Parser_AST.Implicit)))
                                top.FStar_Parser_AST.range))
                       in
                    FStar_List.append uu____10070 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10150 = desugar_term_aq env1 body  in
                        (match uu____10150 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10185 =
                                       let uu____10186 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10186
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10185
                                       body1
                                      in
                                   FStar_Syntax_Syntax.mk
                                     (FStar_Syntax_Syntax.Tm_match
                                        (sc,
                                          [(pat,
                                             FStar_Pervasives_Native.None,
                                             body2)]))
                                     FStar_Pervasives_Native.None
                                     body2.FStar_Syntax_Syntax.pos
                               | FStar_Pervasives_Native.None  -> body1  in
                             let uu____10255 =
                               let uu____10256 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10256  in
                             (uu____10255, aq))
                    | p::rest ->
                        let uu____10269 = desugar_binding_pat env1 p  in
                        (match uu____10269 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10301)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10316 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10325 =
                               match b with
                               | LetBinder uu____10366 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10435) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10489 =
                                           let uu____10498 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10498, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10489
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10560,uu____10561) ->
                                              let tup2 =
                                                let uu____10563 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10563
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10568 =
                                                  let uu____10575 =
                                                    let uu____10576 =
                                                      let uu____10593 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10596 =
                                                        let uu____10607 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10616 =
                                                          let uu____10627 =
                                                            let uu____10636 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10636
                                                             in
                                                          [uu____10627]  in
                                                        uu____10607 ::
                                                          uu____10616
                                                         in
                                                      (uu____10593,
                                                        uu____10596)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10576
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10575
                                                   in
                                                uu____10568
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10684 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10684
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10735,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10737,pats1)) ->
                                              let tupn =
                                                let uu____10782 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10782
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10795 =
                                                  let uu____10796 =
                                                    let uu____10813 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10816 =
                                                      let uu____10827 =
                                                        let uu____10838 =
                                                          let uu____10847 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10847
                                                           in
                                                        [uu____10838]  in
                                                      FStar_List.append args
                                                        uu____10827
                                                       in
                                                    (uu____10813,
                                                      uu____10816)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10796
                                                   in
                                                mk uu____10795  in
                                              let p2 =
                                                let uu____10895 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10895
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10942 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10325 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11034,uu____11035,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11057 =
                let uu____11058 = unparen e  in
                uu____11058.FStar_Parser_AST.tm  in
              match uu____11057 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11068 ->
                  let uu____11069 = desugar_term_aq env e  in
                  (match uu____11069 with
                   | (head,aq) ->
                       let uu____11082 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11082, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11089 ->
            let rec aux args aqs e =
              let uu____11166 =
                let uu____11167 = unparen e  in
                uu____11167.FStar_Parser_AST.tm  in
              match uu____11166 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11185 = desugar_term_aq env t  in
                  (match uu____11185 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11233 ->
                  let uu____11234 = desugar_term_aq env e  in
                  (match uu____11234 with
                   | (head,aq) ->
                       let uu____11255 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11255, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11308 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11308
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11315 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11315  in
            let bind =
              let uu____11320 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11320 FStar_Parser_AST.Expr
               in
            let uu____11321 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11321
        | FStar_Parser_AST.Seq (t1,t2) ->
            let t =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (FStar_Parser_AST.NoLetQualifier,
                     [(FStar_Pervasives_Native.None,
                        ((FStar_Parser_AST.mk_pattern
                            (FStar_Parser_AST.PatWild
                               FStar_Pervasives_Native.None)
                            t1.FStar_Parser_AST.range), t1))], t2))
                top.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let uu____11373 = desugar_term_aq env t  in
            (match uu____11373 with
             | (tm,s) ->
                 let uu____11384 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11384, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11390 =
              let uu____11403 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11403 then desugar_typ_aq else desugar_term_aq  in
            uu____11390 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11470 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11613  ->
                        match uu____11613 with
                        | (attr_opt,(p,def)) ->
                            let uu____11671 = is_app_pattern p  in
                            if uu____11671
                            then
                              let uu____11704 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11704, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11787 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11787, def1)
                               | uu____11832 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11870);
                                           FStar_Parser_AST.prange =
                                             uu____11871;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11920 =
                                            let uu____11941 =
                                              let uu____11946 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____11946  in
                                            (uu____11941, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11920, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12038) ->
                                        if top_level
                                        then
                                          let uu____12074 =
                                            let uu____12095 =
                                              let uu____12100 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12100  in
                                            (uu____12095, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12074, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12191 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12224 =
                FStar_List.fold_left
                  (fun uu____12313  ->
                     fun uu____12314  ->
                       match (uu____12313, uu____12314) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12444,uu____12445),uu____12446))
                           ->
                           let uu____12580 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12620 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12620 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12655 =
                                        let uu____12658 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12658 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12655, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12674 =
                                   let uu____12682 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12682
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12674 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12580 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12224 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12928 =
                    match uu____12928 with
                    | (attrs_opt,(uu____12968,args,result_t),def) ->
                        let args1 =
                          FStar_All.pipe_right args
                            (FStar_List.map replace_unit_pattern)
                           in
                        let pos = def.FStar_Parser_AST.range  in
                        let def1 =
                          match result_t with
                          | FStar_Pervasives_Native.None  -> def
                          | FStar_Pervasives_Native.Some (t,tacopt) ->
                              let t1 =
                                let uu____13060 = is_comp_type env1 t  in
                                if uu____13060
                                then
                                  ((let uu____13064 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13074 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13074))
                                       in
                                    match uu____13064 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13081 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13084 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13084))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13081
                                   then FStar_Parser_AST.ml_comp t
                                   else FStar_Parser_AST.tot_comp t)
                                 in
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Ascribed (def, t1, tacopt))
                                def.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr
                           in
                        let def2 =
                          match args1 with
                          | [] -> def1
                          | uu____13095 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13098 = desugar_term_aq env1 def2  in
                        (match uu____13098 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13120 =
                                     let uu____13121 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13121
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13120
                                in
                             let body2 =
                               if is_rec
                               then
                                 FStar_Syntax_Subst.close rec_bindings1 body1
                               else body1  in
                             let attrs =
                               match attrs_opt with
                               | FStar_Pervasives_Native.None  -> []
                               | FStar_Pervasives_Native.Some l ->
                                   FStar_List.map (desugar_term env1) l
                                in
                             ((mk_lb
                                 (attrs, lbname1, FStar_Syntax_Syntax.tun,
                                   body2, pos)), aq))
                     in
                  let uu____13162 =
                    let uu____13179 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13179 FStar_List.unzip  in
                  (match uu____13162 with
                   | (lbs1,aqss) ->
                       let uu____13321 = desugar_term_aq env' body  in
                       (match uu____13321 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13427  ->
                                    fun used_marker  ->
                                      match uu____13427 with
                                      | (_attr_opt,(f,uu____13501,uu____13502),uu____13503)
                                          ->
                                          let uu____13560 =
                                            let uu____13562 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13562  in
                                          if uu____13560
                                          then
                                            let uu____13586 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13604 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13606 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13604, "Local",
                                                    uu____13606)
                                              | FStar_Util.Inr l ->
                                                  let uu____13611 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13613 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13611, "Global",
                                                    uu____13613)
                                               in
                                            (match uu____13586 with
                                             | (nm,gl,rng) ->
                                                 let uu____13624 =
                                                   let uu____13630 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13630)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13624)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13638 =
                                let uu____13641 =
                                  let uu____13642 =
                                    let uu____13656 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13656)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13642  in
                                FStar_All.pipe_left mk uu____13641  in
                              (uu____13638,
                                (FStar_List.append aq
                                   (FStar_List.flatten aqss)))))))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let uu____13758 = desugar_term_aq env t1  in
              match uu____13758 with
              | (t11,aq0) ->
                  let uu____13779 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13779 with
                   | (env1,binder,pat1) ->
                       let uu____13809 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13851 = desugar_term_aq env1 t2  in
                             (match uu____13851 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13873 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13873
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13874 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13874, aq))
                         | LocalBinder (x,uu____13915) ->
                             let uu____13916 = desugar_term_aq env1 t2  in
                             (match uu____13916 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13938;
                                         FStar_Syntax_Syntax.p = uu____13939;_},uu____13940)::[]
                                        -> body1
                                    | uu____13953 ->
                                        let uu____13956 =
                                          let uu____13963 =
                                            let uu____13964 =
                                              let uu____13987 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____13990 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____13987, uu____13990)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____13964
                                             in
                                          FStar_Syntax_Syntax.mk uu____13963
                                           in
                                        uu____13956
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14027 =
                                    let uu____14030 =
                                      let uu____14031 =
                                        let uu____14045 =
                                          let uu____14048 =
                                            let uu____14049 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14049]  in
                                          FStar_Syntax_Subst.close
                                            uu____14048 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14045)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14031
                                       in
                                    FStar_All.pipe_left mk uu____14030  in
                                  (uu____14027, aq))
                          in
                       (match uu____13809 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14157 = FStar_List.hd lbs  in
            (match uu____14157 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14201 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14201
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool =
              let uu____14217 =
                let uu____14218 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14218  in
              mk uu____14217  in
            let uu____14219 = desugar_term_aq env t1  in
            (match uu____14219 with
             | (t1',aq1) ->
                 let uu____14230 = desugar_term_aq env t2  in
                 (match uu____14230 with
                  | (t2',aq2) ->
                      let uu____14241 = desugar_term_aq env t3  in
                      (match uu____14241 with
                       | (t3',aq3) ->
                           let uu____14252 =
                             let uu____14253 =
                               let uu____14254 =
                                 let uu____14277 =
                                   let uu____14294 =
                                     let uu____14309 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14309,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14323 =
                                     let uu____14340 =
                                       let uu____14355 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14355,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14340]  in
                                   uu____14294 :: uu____14323  in
                                 (t1', uu____14277)  in
                               FStar_Syntax_Syntax.Tm_match uu____14254  in
                             mk uu____14253  in
                           (uu____14252, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let try_with_lid = FStar_Ident.lid_of_path ["try_with"] r  in
            let try_with =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid) r
                FStar_Parser_AST.Expr
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____14551 =
              match uu____14551 with
              | (pat,wopt,b) ->
                  let uu____14573 = desugar_match_pat env pat  in
                  (match uu____14573 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14604 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14604
                          in
                       let uu____14609 = desugar_term_aq env1 b  in
                       (match uu____14609 with
                        | (b1,aq) ->
                            let uu____14622 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14622, aq)))
               in
            let uu____14627 = desugar_term_aq env e  in
            (match uu____14627 with
             | (e1,aq) ->
                 let uu____14638 =
                   let uu____14669 =
                     let uu____14702 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14702 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14669
                     (fun uu____14920  ->
                        match uu____14920 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14638 with
                  | (brs,aqs) ->
                      let uu____15139 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15139, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15173 =
              let uu____15194 = is_comp_type env t  in
              if uu____15194
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15249 = desugar_term_aq env t  in
                 match uu____15249 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15173 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15341 = desugar_term_aq env e  in
                 (match uu____15341 with
                  | (e1,aq) ->
                      let uu____15352 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15352, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15391,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15434 = FStar_List.hd fields  in
              match uu____15434 with
              | (f,uu____15446) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15494  ->
                        match uu____15494 with
                        | (g,uu____15501) ->
                            let uu____15502 = FStar_Ident.text_of_id f  in
                            let uu____15504 =
                              let uu____15506 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15506  in
                            uu____15502 = uu____15504))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15513,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15527 =
                         let uu____15533 =
                           let uu____15535 = FStar_Ident.text_of_id f  in
                           let uu____15537 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15535 uu____15537
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15533)
                          in
                       FStar_Errors.raise_error uu____15527
                         top.FStar_Parser_AST.range
                   | FStar_Pervasives_Native.Some x ->
                       (fn,
                         (FStar_Parser_AST.mk_term
                            (FStar_Parser_AST.Project (x, fn))
                            x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
               in
            let user_constrname =
              FStar_Ident.lid_of_ids
                (FStar_List.append user_ns
                   [record.FStar_Syntax_DsEnv.constrname])
               in
            let recterm =
              match eopt with
              | FStar_Pervasives_Native.None  ->
                  let uu____15548 =
                    let uu____15559 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15590  ->
                              match uu____15590 with
                              | (f,uu____15600) ->
                                  let uu____15601 =
                                    let uu____15602 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15602
                                     in
                                  (uu____15601, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15559)  in
                  FStar_Parser_AST.Construct uu____15548
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15620 =
                      let uu____15621 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15621  in
                    let uu____15622 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15620 uu____15622
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15624 =
                      let uu____15637 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15667  ->
                                match uu____15667 with
                                | (f,uu____15677) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15637)  in
                    FStar_Parser_AST.Record uu____15624  in
                  let uu____15686 =
                    let uu____15707 =
                      let uu____15722 =
                        let uu____15735 =
                          let uu____15740 =
                            let uu____15741 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15741
                             in
                          (uu____15740, e)  in
                        (FStar_Pervasives_Native.None, uu____15735)  in
                      [uu____15722]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15707,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15686
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15793 = desugar_term_aq env recterm1  in
            (match uu____15793 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15809;
                         FStar_Syntax_Syntax.vars = uu____15810;_},args)
                      ->
                      let uu____15836 =
                        let uu____15837 =
                          let uu____15838 =
                            let uu____15855 =
                              let uu____15858 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15859 =
                                let uu____15862 =
                                  let uu____15863 =
                                    let uu____15870 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15870)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15863
                                   in
                                FStar_Pervasives_Native.Some uu____15862  in
                              FStar_Syntax_Syntax.fvar uu____15858
                                FStar_Syntax_Syntax.delta_constant
                                uu____15859
                               in
                            (uu____15855, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15838  in
                        FStar_All.pipe_left mk uu____15837  in
                      (uu____15836, s)
                  | uu____15899 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____15902 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____15902 with
             | (constrname,is_rec) ->
                 let uu____15921 = desugar_term_aq env e  in
                 (match uu____15921 with
                  | (e1,s) ->
                      let projname =
                        let uu____15933 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____15933
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____15940 =
                            let uu____15941 =
                              let uu____15946 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____15946)  in
                            FStar_Syntax_Syntax.Record_projector uu____15941
                             in
                          FStar_Pervasives_Native.Some uu____15940
                        else FStar_Pervasives_Native.None  in
                      let uu____15949 =
                        let uu____15950 =
                          let uu____15951 =
                            let uu____15968 =
                              let uu____15971 =
                                let uu____15972 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____15972
                                 in
                              FStar_Syntax_Syntax.fvar uu____15971
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____15974 =
                              let uu____15985 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____15985]  in
                            (uu____15968, uu____15974)  in
                          FStar_Syntax_Syntax.Tm_app uu____15951  in
                        FStar_All.pipe_left mk uu____15950  in
                      (uu____15949, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16025 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16025
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16036 =
              let uu____16037 = FStar_Syntax_Subst.compress tm  in
              uu____16037.FStar_Syntax_Syntax.n  in
            (match uu____16036 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16045 =
                   let uu___2062_16046 =
                     let uu____16047 =
                       let uu____16049 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16049  in
                     FStar_Syntax_Util.exp_string uu____16047  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2062_16046.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2062_16046.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16045, noaqs)
             | uu____16050 ->
                 let uu____16051 =
                   let uu____16057 =
                     let uu____16059 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16059
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16057)  in
                 FStar_Errors.raise_error uu____16051
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16068 = desugar_term_aq env e  in
            (match uu____16068 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16080 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16080, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16085 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16086 =
              let uu____16087 =
                let uu____16094 = desugar_term env e  in (bv, uu____16094)
                 in
              [uu____16087]  in
            (uu____16085, uu____16086)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16119 =
              let uu____16120 =
                let uu____16121 =
                  let uu____16128 = desugar_term env e  in (uu____16128, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16121  in
              FStar_All.pipe_left mk uu____16120  in
            (uu____16119, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16157 -> false  in
              let uu____16159 =
                let uu____16160 = unparen rel1  in
                uu____16160.FStar_Parser_AST.tm  in
              match uu____16159 with
              | FStar_Parser_AST.Op (id,uu____16163) ->
                  let uu____16168 = op_as_term env (Prims.of_int (2)) id  in
                  (match uu____16168 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16176 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16176 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16187 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16187 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16193 -> false  in
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen' "x" rel1.FStar_Parser_AST.range  in
              let y = FStar_Ident.gen' "y" rel1.FStar_Parser_AST.range  in
              let xt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar x)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let yt =
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar y)
                  rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                 in
              let pats =
                [FStar_Parser_AST.mk_pattern
                   (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                   rel1.FStar_Parser_AST.range;
                FStar_Parser_AST.mk_pattern
                  (FStar_Parser_AST.PatVar (y, FStar_Pervasives_Native.None))
                  rel1.FStar_Parser_AST.range]
                 in
              let uu____16214 =
                let uu____16215 =
                  let uu____16222 =
                    let uu____16223 =
                      let uu____16224 =
                        let uu____16233 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16246 =
                          let uu____16247 =
                            let uu____16248 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16248  in
                          FStar_Parser_AST.mk_term uu____16247
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16233, uu____16246,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16224  in
                    FStar_Parser_AST.mk_term uu____16223
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16222)  in
                FStar_Parser_AST.Abs uu____16215  in
              FStar_Parser_AST.mk_term uu____16214
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let rel1 = eta_and_annot rel  in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr
               in
            let init =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_init_lid)
                init_expr.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let push_impl r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_push_impl_lid)
                r FStar_Parser_AST.Expr
               in
            let last_expr =
              let uu____16269 = FStar_List.last steps  in
              match uu____16269 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16272,uu____16273,last_expr)) -> last_expr
              | FStar_Pervasives_Native.None  -> init_expr  in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr
               in
            let finish =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range
               in
            let e =
              FStar_Parser_AST.mkApp init
                [(init_expr, FStar_Parser_AST.Nothing)]
                init_expr.FStar_Parser_AST.range
               in
            let uu____16299 =
              FStar_List.fold_left
                (fun uu____16317  ->
                   fun uu____16318  ->
                     match (uu____16317, uu____16318) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16341 = is_impl rel2  in
                           if uu____16341
                           then
                             let uu____16344 =
                               let uu____16351 =
                                 let uu____16356 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16356, FStar_Parser_AST.Nothing)  in
                               [uu____16351]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16344 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16368 =
                             let uu____16375 =
                               let uu____16382 =
                                 let uu____16389 =
                                   let uu____16396 =
                                     let uu____16401 = eta_and_annot rel2  in
                                     (uu____16401, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16402 =
                                     let uu____16409 =
                                       let uu____16416 =
                                         let uu____16421 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16421,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16422 =
                                         let uu____16429 =
                                           let uu____16434 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16434,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16429]  in
                                       uu____16416 :: uu____16422  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16409
                                      in
                                   uu____16396 :: uu____16402  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16389
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16382
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16375
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16368
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16299 with
             | (e1,uu____16472) ->
                 let e2 =
                   let uu____16474 =
                     let uu____16481 =
                       let uu____16488 =
                         let uu____16495 =
                           let uu____16500 = FStar_Parser_AST.thunk e1  in
                           (uu____16500, FStar_Parser_AST.Nothing)  in
                         [uu____16495]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16488  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16481  in
                   FStar_Parser_AST.mkApp finish uu____16474
                     top.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16517 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16518 = desugar_formula env top  in
            (uu____16518, noaqs)
        | uu____16519 ->
            let uu____16520 =
              let uu____16526 =
                let uu____16528 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16528  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16526)  in
            FStar_Errors.raise_error uu____16520 top.FStar_Parser_AST.range

and (desugar_args :
  FStar_Syntax_DsEnv.env ->
    (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier
        FStar_Pervasives_Native.option) Prims.list)
  =
  fun env  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.map
           (fun uu____16572  ->
              match uu____16572 with
              | (a,imp) ->
                  let uu____16585 = desugar_term env a  in
                  arg_withimp_e imp uu____16585))

and (desugar_comp :
  FStar_Range.range ->
    Prims.bool ->
      FStar_Syntax_DsEnv.env ->
        FStar_Parser_AST.term ->
          FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax)
  =
  fun r  ->
    fun allow_type_promotion  ->
      fun env  ->
        fun t  ->
          let fail err = FStar_Errors.raise_error err r  in
          let is_requires uu____16622 =
            match uu____16622 with
            | (t1,uu____16629) ->
                let uu____16630 =
                  let uu____16631 = unparen t1  in
                  uu____16631.FStar_Parser_AST.tm  in
                (match uu____16630 with
                 | FStar_Parser_AST.Requires uu____16633 -> true
                 | uu____16642 -> false)
             in
          let is_ensures uu____16654 =
            match uu____16654 with
            | (t1,uu____16661) ->
                let uu____16662 =
                  let uu____16663 = unparen t1  in
                  uu____16663.FStar_Parser_AST.tm  in
                (match uu____16662 with
                 | FStar_Parser_AST.Ensures uu____16665 -> true
                 | uu____16674 -> false)
             in
          let is_app head uu____16692 =
            match uu____16692 with
            | (t1,uu____16700) ->
                let uu____16701 =
                  let uu____16702 = unparen t1  in
                  uu____16702.FStar_Parser_AST.tm  in
                (match uu____16701 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16705;
                        FStar_Parser_AST.level = uu____16706;_},uu____16707,uu____16708)
                     ->
                     let uu____16709 =
                       let uu____16711 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16711  in
                     uu____16709 = head
                 | uu____16713 -> false)
             in
          let is_smt_pat uu____16725 =
            match uu____16725 with
            | (t1,uu____16732) ->
                let uu____16733 =
                  let uu____16734 = unparen t1  in
                  uu____16734.FStar_Parser_AST.tm  in
                (match uu____16733 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16738);
                              FStar_Parser_AST.range = uu____16739;
                              FStar_Parser_AST.level = uu____16740;_},uu____16741)::uu____16742::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16782 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16782 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16794;
                              FStar_Parser_AST.level = uu____16795;_},uu____16796)::uu____16797::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16825 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16825 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16833 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16868 = head_and_args t1  in
            match uu____16868 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____16926 =
                       let uu____16928 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____16928  in
                     uu____16926 = "Lemma" ->
                     let unit_tm =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing)
                        in
                     let nil_pat =
                       ((FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Name FStar_Parser_Const.nil_lid)
                           t1.FStar_Parser_AST.range FStar_Parser_AST.Expr),
                         FStar_Parser_AST.Nothing)
                        in
                     let req_true =
                       let req =
                         FStar_Parser_AST.Requires
                           ((FStar_Parser_AST.mk_term
                               (FStar_Parser_AST.Name
                                  FStar_Parser_Const.true_lid)
                               t1.FStar_Parser_AST.range
                               FStar_Parser_AST.Formula),
                             FStar_Pervasives_Native.None)
                          in
                       ((FStar_Parser_AST.mk_term req
                           t1.FStar_Parser_AST.range
                           FStar_Parser_AST.Type_level),
                         FStar_Parser_AST.Nothing)
                        in
                     let thunk_ens uu____16964 =
                       match uu____16964 with
                       | (e,i) ->
                           let uu____16975 = FStar_Parser_AST.thunk e  in
                           (uu____16975, i)
                        in
                     let fail_lemma uu____16987 =
                       let expected_one_of =
                         ["Lemma post";
                         "Lemma (ensures post)";
                         "Lemma (requires pre) (ensures post)";
                         "Lemma post [SMTPat ...]";
                         "Lemma (ensures post) [SMTPat ...]";
                         "Lemma (ensures post) (decreases d)";
                         "Lemma (ensures post) (decreases d) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d)";
                         "Lemma (requires pre) (ensures post) [SMTPat ...]";
                         "Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]"]
                          in
                       let msg = FStar_String.concat "\n\t" expected_one_of
                          in
                       FStar_Errors.raise_error
                         (FStar_Errors.Fatal_InvalidLemmaArgument,
                           (Prims.op_Hat
                              "Invalid arguments to 'Lemma'; expected one of the following:\n\t"
                              msg)) t1.FStar_Parser_AST.range
                        in
                     let args1 =
                       match args with
                       | [] -> fail_lemma ()
                       | req::[] when is_requires req -> fail_lemma ()
                       | smtpat::[] when is_smt_pat smtpat -> fail_lemma ()
                       | dec::[] when is_decreases dec -> fail_lemma ()
                       | ens::[] ->
                           let uu____17093 =
                             let uu____17100 =
                               let uu____17107 = thunk_ens ens  in
                               [uu____17107; nil_pat]  in
                             req_true :: uu____17100  in
                           unit_tm :: uu____17093
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17154 =
                             let uu____17161 =
                               let uu____17168 = thunk_ens ens  in
                               [uu____17168; nil_pat]  in
                             req :: uu____17161  in
                           unit_tm :: uu____17154
                       | ens::smtpat::[] when
                           (((let uu____17217 = is_requires ens  in
                              Prims.op_Negation uu____17217) &&
                               (let uu____17220 = is_smt_pat ens  in
                                Prims.op_Negation uu____17220))
                              &&
                              (let uu____17223 = is_decreases ens  in
                               Prims.op_Negation uu____17223))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17225 =
                             let uu____17232 =
                               let uu____17239 = thunk_ens ens  in
                               [uu____17239; smtpat]  in
                             req_true :: uu____17232  in
                           unit_tm :: uu____17225
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17286 =
                             let uu____17293 =
                               let uu____17300 = thunk_ens ens  in
                               [uu____17300; nil_pat; dec]  in
                             req_true :: uu____17293  in
                           unit_tm :: uu____17286
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17360 =
                             let uu____17367 =
                               let uu____17374 = thunk_ens ens  in
                               [uu____17374; smtpat; dec]  in
                             req_true :: uu____17367  in
                           unit_tm :: uu____17360
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17434 =
                             let uu____17441 =
                               let uu____17448 = thunk_ens ens  in
                               [uu____17448; nil_pat; dec]  in
                             req :: uu____17441  in
                           unit_tm :: uu____17434
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17508 =
                             let uu____17515 =
                               let uu____17522 = thunk_ens ens  in
                               [uu____17522; smtpat]  in
                             req :: uu____17515  in
                           unit_tm :: uu____17508
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17587 =
                             let uu____17594 =
                               let uu____17601 = thunk_ens ens  in
                               [uu____17601; dec; smtpat]  in
                             req :: uu____17594  in
                           unit_tm :: uu____17587
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17663 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17663, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17691 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17691
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17693 =
                          let uu____17695 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17695  in
                        uu____17693 = "Tot")
                     ->
                     let uu____17698 =
                       let uu____17705 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17705, [])  in
                     (uu____17698, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17723 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17723
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17725 =
                          let uu____17727 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17727  in
                        uu____17725 = "GTot")
                     ->
                     let uu____17730 =
                       let uu____17737 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17737, [])  in
                     (uu____17730, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17755 =
                         let uu____17757 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17757  in
                       uu____17755 = "Type") ||
                        (let uu____17761 =
                           let uu____17763 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17763  in
                         uu____17761 = "Type0"))
                       ||
                       (let uu____17767 =
                          let uu____17769 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17769  in
                        uu____17767 = "Effect")
                     ->
                     let uu____17772 =
                       let uu____17779 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17779, [])  in
                     (uu____17772, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17802 when allow_type_promotion ->
                     let default_effect =
                       let uu____17804 = FStar_Options.ml_ish ()  in
                       if uu____17804
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17810 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17810
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17817 =
                       let uu____17824 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17824, [])  in
                     (uu____17817, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17847 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17866 = pre_process_comp_typ t  in
          match uu____17866 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17918 =
                    let uu____17924 =
                      let uu____17926 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17926
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17924)
                     in
                  fail uu____17918)
               else ();
               (let is_universe uu____17942 =
                  match uu____17942 with
                  | (uu____17948,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17950 = FStar_Util.take is_universe args  in
                match uu____17950 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18009  ->
                           match uu____18009 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18016 =
                      let uu____18031 = FStar_List.hd args1  in
                      let uu____18040 = FStar_List.tl args1  in
                      (uu____18031, uu____18040)  in
                    (match uu____18016 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18095 =
                           let is_decrease uu____18134 =
                             match uu____18134 with
                             | (t1,uu____18145) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18156;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18157;_},uu____18158::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18197 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18095 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18314  ->
                                        match uu____18314 with
                                        | (t1,uu____18324) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18333,(arg,uu____18335)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18374 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18395 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18407 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18407
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18414 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18414
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18424 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18424
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18431 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18431
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18438 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18438
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18445 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18445
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18466 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18466
                                      then
                                        match rest2 with
                                        | req::ens::(pat,aq)::[] ->
                                            let pat1 =
                                              match pat.FStar_Syntax_Syntax.n
                                              with
                                              | FStar_Syntax_Syntax.Tm_fvar
                                                  fv when
                                                  FStar_Syntax_Syntax.fv_eq_lid
                                                    fv
                                                    FStar_Parser_Const.nil_lid
                                                  ->
                                                  let nil =
                                                    FStar_Syntax_Syntax.mk_Tm_uinst
                                                      pat
                                                      [FStar_Syntax_Syntax.U_zero]
                                                     in
                                                  let pattern =
                                                    let uu____18557 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18557
                                                      FStar_Syntax_Syntax.delta_constant
                                                      FStar_Pervasives_Native.None
                                                     in
                                                  FStar_Syntax_Syntax.mk_Tm_app
                                                    nil
                                                    [(pattern,
                                                       (FStar_Pervasives_Native.Some
                                                          FStar_Syntax_Syntax.imp_tag))]
                                                    FStar_Pervasives_Native.None
                                                    pat.FStar_Syntax_Syntax.pos
                                              | uu____18578 -> pat  in
                                            let uu____18579 =
                                              let uu____18590 =
                                                let uu____18601 =
                                                  let uu____18610 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18610, aq)  in
                                                [uu____18601]  in
                                              ens :: uu____18590  in
                                            req :: uu____18579
                                        | uu____18651 -> rest2
                                      else rest2  in
                                    FStar_Syntax_Syntax.mk_Comp
                                      {
                                        FStar_Syntax_Syntax.comp_univs =
                                          universes1;
                                        FStar_Syntax_Syntax.effect_name = eff;
                                        FStar_Syntax_Syntax.result_typ =
                                          result_typ;
                                        FStar_Syntax_Syntax.effect_args =
                                          rest3;
                                        FStar_Syntax_Syntax.flags =
                                          (FStar_List.append flags1
                                             decreases_clause)
                                      }))))))

and (desugar_formula :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun f  ->
      let mk t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2387_18686 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2387_18686.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2387_18686.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2394_18740 = b  in
             {
               FStar_Parser_AST.b = (uu___2394_18740.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2394_18740.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2394_18740.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18769 body1 =
          match uu____18769 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18815::uu____18816) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18834 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2413_18862 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18863 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2413_18862.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18863;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2413_18862.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18926 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18926))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18957 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18957 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2426_18967 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2426_18967.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2426_18967.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18973 =
                     let uu____18976 =
                       let uu____18977 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18977]  in
                     no_annot_abs uu____18976 body2  in
                   FStar_All.pipe_left setpos uu____18973  in
                 let uu____18998 =
                   let uu____18999 =
                     let uu____19016 =
                       let uu____19019 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19019
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19021 =
                       let uu____19032 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19032]  in
                     (uu____19016, uu____19021)  in
                   FStar_Syntax_Syntax.Tm_app uu____18999  in
                 FStar_All.pipe_left mk uu____18998)
        | uu____19071 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19136 = q (rest, pats, body)  in
              let uu____19139 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19136 uu____19139
                FStar_Parser_AST.Formula
               in
            let uu____19140 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19140 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19151 -> failwith "impossible"  in
      let uu____19155 =
        let uu____19156 = unparen f  in uu____19156.FStar_Parser_AST.tm  in
      match uu____19155 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19169,uu____19170) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19194,uu____19195) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19251 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19251
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19295 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19295
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19359 -> desugar_term env f

and (desugar_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term))
  =
  fun env  ->
    fun b  ->
      match b.FStar_Parser_AST.b with
      | FStar_Parser_AST.TAnnotated (x,t) ->
          let uu____19370 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19370)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19375 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19375)
      | FStar_Parser_AST.TVariable x ->
          let uu____19379 =
            let uu____19380 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19380
             in
          ((FStar_Pervasives_Native.Some x), uu____19379)
      | FStar_Parser_AST.NoName t ->
          let uu____19384 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19384)
      | FStar_Parser_AST.Variable x ->
          ((FStar_Pervasives_Native.Some x), FStar_Syntax_Syntax.tun)

and (as_binder :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      (FStar_Ident.ident FStar_Pervasives_Native.option *
        FStar_Syntax_Syntax.term) ->
        ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option) * FStar_Syntax_DsEnv.env))
  =
  fun env  ->
    fun imp  ->
      fun uu___11_19392  ->
        match uu___11_19392 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19414 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19414, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19431 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19431 with
             | (env1,a1) ->
                 let uu____19448 =
                   let uu____19455 = trans_aqual env1 imp  in
                   ((let uu___2526_19461 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2526_19461.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2526_19461.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19455)
                    in
                 (uu____19448, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19469  ->
      match uu___12_19469 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19473 =
            let uu____19474 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19474  in
          FStar_Pervasives_Native.Some uu____19473
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19502 =
        FStar_List.fold_left
          (fun uu____19535  ->
             fun b  ->
               match uu____19535 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2544_19579 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2544_19579.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2544_19579.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2544_19579.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19594 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19594 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2554_19612 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2554_19612.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2554_19612.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19613 =
                               let uu____19620 =
                                 let uu____19625 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19625)  in
                               uu____19620 :: out  in
                             (env2, uu____19613))
                    | uu____19636 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19502 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19724 =
          let uu____19725 = unparen t  in uu____19725.FStar_Parser_AST.tm  in
        match uu____19724 with
        | FStar_Parser_AST.Var lid when
            let uu____19727 = FStar_Ident.string_of_lid lid  in
            uu____19727 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19731 ->
            let uu____19732 =
              let uu____19738 =
                let uu____19740 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19740  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19738)  in
            FStar_Errors.raise_error uu____19732 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19757) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19759) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19762 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19780 = binder_ident b  in
         FStar_Common.list_of_option uu____19780) bs
  
let (mk_data_discriminators :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Ident.lident Prims.list -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun quals  ->
    fun env  ->
      fun datas  ->
        let quals1 =
          FStar_All.pipe_right quals
            (FStar_List.filter
               (fun uu___13_19817  ->
                  match uu___13_19817 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19822 -> false))
           in
        let quals2 q =
          let uu____19836 =
            (let uu____19840 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19840) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19836
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19857 = FStar_Ident.range_of_lid disc_name  in
                let uu____19858 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19857;
                  FStar_Syntax_Syntax.sigquals = uu____19858;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = [];
                  FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
                }))
  
let (mk_indexed_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_Syntax.fv_qual ->
      FStar_Syntax_DsEnv.env ->
        FStar_Ident.lident ->
          FStar_Syntax_Syntax.binder Prims.list ->
            FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun fvq  ->
      fun env  ->
        fun lid  ->
          fun fields  ->
            let p = FStar_Ident.range_of_lid lid  in
            let uu____19898 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19934  ->
                        match uu____19934 with
                        | (x,uu____19945) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____19955 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____19955)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____19957 =
                                   let uu____19959 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____19959  in
                                 FStar_Options.dont_gen_projectors
                                   uu____19957)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____19977 =
                                  FStar_List.filter
                                    (fun uu___14_19981  ->
                                       match uu___14_19981 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____19984 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____19977
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_19999  ->
                                        match uu___15_19999 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20004 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20007 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20007;
                                FStar_Syntax_Syntax.sigquals = quals1;
                                FStar_Syntax_Syntax.sigmeta =
                                  FStar_Syntax_Syntax.default_sigmeta;
                                FStar_Syntax_Syntax.sigattrs = [];
                                FStar_Syntax_Syntax.sigopts =
                                  FStar_Pervasives_Native.None
                              }  in
                            if only_decl
                            then [decl]
                            else
                              (let dd =
                                 let uu____20014 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20014
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20025 =
                                   let uu____20030 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20030  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20025;
                                   FStar_Syntax_Syntax.lbunivs = [];
                                   FStar_Syntax_Syntax.lbtyp =
                                     FStar_Syntax_Syntax.tun;
                                   FStar_Syntax_Syntax.lbeff =
                                     FStar_Parser_Const.effect_Tot_lid;
                                   FStar_Syntax_Syntax.lbdef =
                                     FStar_Syntax_Syntax.tun;
                                   FStar_Syntax_Syntax.lbattrs = [];
                                   FStar_Syntax_Syntax.lbpos =
                                     FStar_Range.dummyRange
                                 }  in
                               let impl =
                                 let uu____20034 =
                                   let uu____20035 =
                                     let uu____20042 =
                                       let uu____20045 =
                                         let uu____20046 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20046
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20045]  in
                                     ((false, [lb]), uu____20042)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20035
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20034;
                                   FStar_Syntax_Syntax.sigrng = p;
                                   FStar_Syntax_Syntax.sigquals = quals1;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 }  in
                               if no_decl then [impl] else [decl; impl])))
               in
            FStar_All.pipe_right uu____19898 FStar_List.flatten
  
let (mk_data_projector_names :
  FStar_Syntax_Syntax.qualifier Prims.list ->
    FStar_Syntax_DsEnv.env ->
      FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt Prims.list)
  =
  fun iquals  ->
    fun env  ->
      fun se  ->
        match se.FStar_Syntax_Syntax.sigel with
        | FStar_Syntax_Syntax.Sig_datacon
            (lid,uu____20095,t,uu____20097,n,uu____20099) when
            let uu____20106 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20106 ->
            let uu____20108 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20108 with
             | (formals,uu____20118) ->
                 (match formals with
                  | [] -> []
                  | uu____20131 ->
                      let filter_records uu___16_20139 =
                        match uu___16_20139 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20142,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20154 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20156 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20156 with
                        | FStar_Pervasives_Native.None  ->
                            FStar_Syntax_Syntax.Data_ctor
                        | FStar_Pervasives_Native.Some q -> q  in
                      let iquals1 =
                        if
                          (FStar_List.contains FStar_Syntax_Syntax.Abstract
                             iquals)
                            &&
                            (Prims.op_Negation
                               (FStar_List.contains
                                  FStar_Syntax_Syntax.Private iquals))
                        then FStar_Syntax_Syntax.Private :: iquals
                        else iquals  in
                      let uu____20168 = FStar_Util.first_N n formals  in
                      (match uu____20168 with
                       | (uu____20197,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20231 -> []
  
let (mk_typ_abbrev :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.univ_name Prims.list ->
          (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier
            FStar_Pervasives_Native.option) Prims.list ->
            FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
                FStar_Ident.lident Prims.list ->
                  FStar_Syntax_Syntax.qualifier Prims.list ->
                    FStar_Range.range -> FStar_Syntax_Syntax.sigelt)
  =
  fun env  ->
    fun d  ->
      fun lid  ->
        fun uvs  ->
          fun typars  ->
            fun kopt  ->
              fun t  ->
                fun lids  ->
                  fun quals  ->
                    fun rng  ->
                      let attrs =
                        FStar_List.map (desugar_term env)
                          d.FStar_Parser_AST.attrs
                         in
                      let val_attrs =
                        let uu____20325 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20325
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20349 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20349
                        then
                          let uu____20355 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20355
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20359 =
                          let uu____20364 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20364  in
                        let uu____20365 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20371 =
                              let uu____20374 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20374  in
                            FStar_Syntax_Util.arrow typars uu____20371
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20379 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20359;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20365;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20379;
                          FStar_Syntax_Syntax.lbattrs = [];
                          FStar_Syntax_Syntax.lbpos = rng
                        }  in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_let ((false, [lb]), lids));
                        FStar_Syntax_Syntax.sigrng = rng;
                        FStar_Syntax_Syntax.sigquals = quals;
                        FStar_Syntax_Syntax.sigmeta =
                          FStar_Syntax_Syntax.default_sigmeta;
                        FStar_Syntax_Syntax.sigattrs =
                          (FStar_List.append val_attrs attrs);
                        FStar_Syntax_Syntax.sigopts =
                          FStar_Pervasives_Native.None
                      }
  
let rec (desugar_tycon :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Parser_AST.tycon Prims.list ->
          (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun tcs  ->
          let rng = d.FStar_Parser_AST.drange  in
          let tycon_id uu___17_20433 =
            match uu___17_20433 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20435,uu____20436) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20446,uu____20447,uu____20448) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20458,uu____20459,uu____20460) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20482,uu____20483,uu____20484) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20522) ->
                let uu____20523 =
                  let uu____20524 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20524  in
                let uu____20525 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20523 uu____20525
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20527 =
                  let uu____20528 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20528  in
                let uu____20529 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20527 uu____20529
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20531) ->
                let uu____20532 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20532 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20534 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20534 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.NoName t -> t  in
          let tot =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.Name FStar_Parser_Const.effect_Tot_lid) rng
              FStar_Parser_AST.Expr
             in
          let with_constructor_effect t =
            FStar_Parser_AST.mk_term
              (FStar_Parser_AST.App (tot, t, FStar_Parser_AST.Nothing))
              t.FStar_Parser_AST.range t.FStar_Parser_AST.level
             in
          let apply_binders t binders =
            let imp_of_aqual b =
              match b.FStar_Parser_AST.aqual with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
                  FStar_Parser_AST.Hash
              | uu____20564 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20572 =
                     let uu____20573 =
                       let uu____20580 = binder_to_term b  in
                       (out, uu____20580, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20573  in
                   FStar_Parser_AST.mk_term uu____20572
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20592 =
            match uu___18_20592 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20624 =
                    let uu____20630 =
                      let uu____20632 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20632  in
                    let uu____20635 = FStar_Ident.range_of_id id  in
                    (uu____20630, uu____20635)  in
                  FStar_Ident.mk_ident uu____20624  in
                let mfields =
                  FStar_List.map
                    (fun uu____20648  ->
                       match uu____20648 with
                       | (x,t) ->
                           let uu____20655 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20655
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20657 =
                    let uu____20658 =
                      let uu____20659 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20659  in
                    let uu____20660 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20658 uu____20660
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20657 parms  in
                let constrTyp =
                  let uu____20662 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20662 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20668 = binder_idents parms  in id :: uu____20668
                   in
                (FStar_List.iter
                   (fun uu____20682  ->
                      match uu____20682 with
                      | (f,uu____20688) ->
                          let uu____20689 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20689
                          then
                            let uu____20694 =
                              let uu____20700 =
                                let uu____20702 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20702
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20700)
                               in
                            let uu____20706 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20694 uu____20706
                          else ()) fields;
                 (let uu____20709 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20709)))
            | uu____20763 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20803 =
            match uu___19_20803 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20827 = typars_of_binders _env binders  in
                (match uu____20827 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20863 =
                         let uu____20864 =
                           let uu____20865 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20865  in
                         let uu____20866 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20864 uu____20866
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20863 binders  in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id  in
                     let typars1 = FStar_Syntax_Subst.close_binders typars
                        in
                     let k1 = FStar_Syntax_Subst.close typars1 k  in
                     let se =
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_inductive_typ
                              (qlid, [], typars1, k1, mutuals, []));
                         FStar_Syntax_Syntax.sigrng = rng;
                         FStar_Syntax_Syntax.sigquals = quals1;
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     let uu____20875 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20875 with
                      | (_env1,uu____20892) ->
                          let uu____20899 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20899 with
                           | (_env2,uu____20916) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20923 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20966 =
              FStar_List.fold_left
                (fun uu____21000  ->
                   fun uu____21001  ->
                     match (uu____21000, uu____21001) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21070 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21070 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20966 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21161 =
                      let uu____21162 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21162  in
                    FStar_Pervasives_Native.Some uu____21161
                | uu____21163 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21171 = desugar_abstract_tc quals env [] tc  in
              (match uu____21171 with
               | (uu____21184,uu____21185,se,uu____21187) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21190,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21209 =
                                 let uu____21211 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21211  in
                               if uu____21209
                               then
                                 let uu____21214 =
                                   let uu____21220 =
                                     let uu____21222 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21222
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21220)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21214
                               else ());
                              FStar_Syntax_Syntax.Assumption
                              ::
                              FStar_Syntax_Syntax.New
                              ::
                              quals1)
                            in
                         let t =
                           match typars with
                           | [] -> k
                           | uu____21235 ->
                               let uu____21236 =
                                 let uu____21243 =
                                   let uu____21244 =
                                     let uu____21259 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21259)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21244
                                    in
                                 FStar_Syntax_Syntax.mk uu____21243  in
                               uu____21236 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2831_21272 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2831_21272.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2831_21272.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2831_21272.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2831_21272.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21273 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21288 = typars_of_binders env binders  in
              (match uu____21288 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21322 =
                           FStar_Util.for_some
                             (fun uu___20_21325  ->
                                match uu___20_21325 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21328 -> false) quals
                            in
                         if uu____21322
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21336 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21336
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21341 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21347  ->
                               match uu___21_21347 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21350 -> false))
                        in
                     if uu____21341
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21364 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21364
                     then
                       let uu____21370 =
                         let uu____21377 =
                           let uu____21378 = unparen t  in
                           uu____21378.FStar_Parser_AST.tm  in
                         match uu____21377 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21399 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21429)::args_rev ->
                                   let uu____21441 =
                                     let uu____21442 = unparen last_arg  in
                                     uu____21442.FStar_Parser_AST.tm  in
                                   (match uu____21441 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21470 -> ([], args))
                               | uu____21479 -> ([], args)  in
                             (match uu____21399 with
                              | (cattributes,args1) ->
                                  let uu____21518 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21518))
                         | uu____21529 -> (t, [])  in
                       match uu____21370 with
                       | (t1,cattributes) ->
                           let c =
                             desugar_comp t1.FStar_Parser_AST.range false
                               env' t1
                              in
                           let typars1 =
                             FStar_Syntax_Subst.close_binders typars  in
                           let c1 = FStar_Syntax_Subst.close_comp typars1 c
                              in
                           let quals2 =
                             FStar_All.pipe_right quals1
                               (FStar_List.filter
                                  (fun uu___22_21552  ->
                                     match uu___22_21552 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21555 -> true))
                              in
                           {
                             FStar_Syntax_Syntax.sigel =
                               (FStar_Syntax_Syntax.Sig_effect_abbrev
                                  (qlid, [], typars1, c1,
                                    (FStar_List.append cattributes
                                       (FStar_Syntax_Util.comp_flags c1))));
                             FStar_Syntax_Syntax.sigrng = rng;
                             FStar_Syntax_Syntax.sigquals = quals2;
                             FStar_Syntax_Syntax.sigmeta =
                               FStar_Syntax_Syntax.default_sigmeta;
                             FStar_Syntax_Syntax.sigattrs = [];
                             FStar_Syntax_Syntax.sigopts =
                               FStar_Pervasives_Native.None
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev env d qlid [] typars kopt1 t1 [qlid]
                          quals1 rng)
                      in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
                   (env1, [se]))
          | (FStar_Parser_AST.TyconRecord uu____21563)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21583 = tycon_record_as_variant trec  in
              (match uu____21583 with
               | (t,fs) ->
                   let uu____21600 =
                     let uu____21603 =
                       let uu____21604 =
                         let uu____21613 =
                           let uu____21616 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21616  in
                         (uu____21613, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21604  in
                     uu____21603 :: quals  in
                   desugar_tycon env d uu____21600 [t])
          | uu____21621::uu____21622 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21780 = et  in
                match uu____21780 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21990 ->
                         let trec = tc  in
                         let uu____22010 = tycon_record_as_variant trec  in
                         (match uu____22010 with
                          | (t,fs) ->
                              let uu____22066 =
                                let uu____22069 =
                                  let uu____22070 =
                                    let uu____22079 =
                                      let uu____22082 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22082  in
                                    (uu____22079, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22070
                                   in
                                uu____22069 :: quals1  in
                              collect_tcs uu____22066 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22160 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22160 with
                          | (env2,uu____22217,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22354 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22354 with
                          | (env2,uu____22411,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22527 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22573 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22573 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23025  ->
                             match uu___24_23025 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23079,uu____23080);
                                    FStar_Syntax_Syntax.sigrng = uu____23081;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23082;
                                    FStar_Syntax_Syntax.sigmeta = uu____23083;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23084;
                                    FStar_Syntax_Syntax.sigopts = uu____23085;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23147 =
                                     typars_of_binders env1 binders  in
                                   match uu____23147 with
                                   | (env2,tpars1) ->
                                       let uu____23174 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23174 with
                                        | (env_tps,tpars2) ->
                                            let t1 = desugar_typ env_tps t
                                               in
                                            let tpars3 =
                                              FStar_Syntax_Subst.close_binders
                                                tpars2
                                               in
                                            FStar_Syntax_Subst.close tpars3
                                              t1)
                                    in
                                 let uu____23203 =
                                   let uu____23214 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23214)  in
                                 [uu____23203]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23250);
                                    FStar_Syntax_Syntax.sigrng = uu____23251;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23253;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23254;
                                    FStar_Syntax_Syntax.sigopts = uu____23255;_},constrs,tconstr,quals1)
                                 ->
                                 let mk_tot t =
                                   let tot1 =
                                     FStar_Parser_AST.mk_term
                                       (FStar_Parser_AST.Name
                                          FStar_Parser_Const.effect_Tot_lid)
                                       t.FStar_Parser_AST.range
                                       t.FStar_Parser_AST.level
                                      in
                                   FStar_Parser_AST.mk_term
                                     (FStar_Parser_AST.App
                                        (tot1, t, FStar_Parser_AST.Nothing))
                                     t.FStar_Parser_AST.range
                                     t.FStar_Parser_AST.level
                                    in
                                 let tycon = (tname, tpars, k)  in
                                 let uu____23346 = push_tparams env1 tpars
                                    in
                                 (match uu____23346 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23405  ->
                                             match uu____23405 with
                                             | (x,uu____23417) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let attrs =
                                        FStar_List.map (desugar_term env1)
                                          d.FStar_Parser_AST.attrs
                                         in
                                      let val_attrs =
                                        let uu____23428 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23428
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23451 =
                                        let uu____23470 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23547  ->
                                                  match uu____23547 with
                                                  | (id,topt,of_notation) ->
                                                      let t =
                                                        if of_notation
                                                        then
                                                          match topt with
                                                          | FStar_Pervasives_Native.Some
                                                              t ->
                                                              FStar_Parser_AST.mk_term
                                                                (FStar_Parser_AST.Product
                                                                   ([
                                                                    FStar_Parser_AST.mk_binder
                                                                    (FStar_Parser_AST.NoName
                                                                    t)
                                                                    t.FStar_Parser_AST.range
                                                                    t.FStar_Parser_AST.level
                                                                    FStar_Pervasives_Native.None],
                                                                    tot_tconstr))
                                                                t.FStar_Parser_AST.range
                                                                t.FStar_Parser_AST.level
                                                          | FStar_Pervasives_Native.None
                                                               -> tconstr
                                                        else
                                                          (match topt with
                                                           | FStar_Pervasives_Native.None
                                                                ->
                                                               failwith
                                                                 "Impossible"
                                                           | FStar_Pervasives_Native.Some
                                                               t -> t)
                                                         in
                                                      let t1 =
                                                        let uu____23590 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23590
                                                         in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___23_23601
                                                                 ->
                                                                match uu___23_23601
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23613
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23621 =
                                                        let uu____23632 =
                                                          let uu____23633 =
                                                            let uu____23634 =
                                                              let uu____23650
                                                                =
                                                                let uu____23651
                                                                  =
                                                                  let uu____23654
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23654
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23651
                                                                 in
                                                              (name, univs,
                                                                uu____23650,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23634
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23633;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              =
                                                              (FStar_List.append
                                                                 val_attrs
                                                                 attrs);
                                                            FStar_Syntax_Syntax.sigopts
                                                              =
                                                              FStar_Pervasives_Native.None
                                                          }  in
                                                        (tps, uu____23632)
                                                         in
                                                      (name, uu____23621)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23470
                                         in
                                      (match uu____23451 with
                                       | (constrNames,constrs1) ->
                                           ([],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs, tpars, k,
                                                      mutuals1, constrNames));
                                               FStar_Syntax_Syntax.sigrng =
                                                 rng;
                                               FStar_Syntax_Syntax.sigquals =
                                                 tname_quals;
                                               FStar_Syntax_Syntax.sigmeta =
                                                 FStar_Syntax_Syntax.default_sigmeta;
                                               FStar_Syntax_Syntax.sigattrs =
                                                 (FStar_List.append val_attrs
                                                    attrs);
                                               FStar_Syntax_Syntax.sigopts =
                                                 FStar_Pervasives_Native.None
                                             })
                                           :: constrs1))
                             | uu____23786 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23867  ->
                             match uu____23867 with | (uu____23878,se) -> se))
                      in
                   let uu____23892 =
                     let uu____23899 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23899 rng
                      in
                   (match uu____23892 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right tps_sigelts
                            (FStar_List.collect
                               (fun uu____23944  ->
                                  match uu____23944 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23992,tps,k,uu____23995,constrs)
                                      ->
                                      let quals1 =
                                        se.FStar_Syntax_Syntax.sigquals  in
                                      let quals2 =
                                        if
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract
                                             quals1)
                                            &&
                                            (Prims.op_Negation
                                               (FStar_List.contains
                                                  FStar_Syntax_Syntax.Private
                                                  quals1))
                                        then FStar_Syntax_Syntax.Private ::
                                          quals1
                                        else quals1  in
                                      let uu____24016 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24031 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24048,uu____24049,uu____24050,uu____24051,uu____24052)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24059
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24031
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24063 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24070  ->
                                                          match uu___25_24070
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24072 ->
                                                              true
                                                          | uu____24082 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24063))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24016
                                  | uu____24084 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        (env4,
                          (FStar_List.append [bundle]
                             (FStar_List.append abbrevs ops)))))
          | [] -> failwith "impossible"
  
let (desugar_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option)
        Prims.list))
  =
  fun env  ->
    fun binders  ->
      let uu____24121 =
        FStar_List.fold_left
          (fun uu____24156  ->
             fun b  ->
               match uu____24156 with
               | (env1,binders1) ->
                   let uu____24200 = desugar_binder env1 b  in
                   (match uu____24200 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24223 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24223 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24276 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24121 with
      | (env1,binders1) -> (env1, (FStar_List.rev binders1))
  
let (push_reflect_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Ident.lid -> FStar_Range.range -> FStar_Syntax_DsEnv.env)
  =
  fun env  ->
    fun quals  ->
      fun effect_name  ->
        fun range  ->
          let uu____24380 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24387  ->
                    match uu___26_24387 with
                    | FStar_Syntax_Syntax.Reflectable uu____24389 -> true
                    | uu____24391 -> false))
             in
          if uu____24380
          then
            let monad_env =
              let uu____24395 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24395  in
            let reflect_lid =
              let uu____24397 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24397
                (FStar_Syntax_DsEnv.qualify monad_env)
               in
            let quals1 =
              [FStar_Syntax_Syntax.Assumption;
              FStar_Syntax_Syntax.Reflectable effect_name]  in
            let refl_decl =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_declare_typ
                     (reflect_lid, [], FStar_Syntax_Syntax.tun));
                FStar_Syntax_Syntax.sigrng = range;
                FStar_Syntax_Syntax.sigquals = quals1;
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            FStar_Syntax_DsEnv.push_sigelt env refl_decl
          else env
  
let (parse_attr_with_list :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident ->
        (Prims.int Prims.list FStar_Pervasives_Native.option * Prims.bool))
  =
  fun warn  ->
    fun at  ->
      fun head  ->
        let warn1 uu____24448 =
          if warn
          then
            let uu____24450 =
              let uu____24456 =
                let uu____24458 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24458
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24456)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24450
          else ()  in
        let uu____24464 = FStar_Syntax_Util.head_and_args at  in
        match uu____24464 with
        | (hd,args) ->
            let uu____24517 =
              let uu____24518 = FStar_Syntax_Subst.compress hd  in
              uu____24518.FStar_Syntax_Syntax.n  in
            (match uu____24517 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24562)::[] ->
                      let uu____24587 =
                        let uu____24592 =
                          let uu____24601 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24601 a1  in
                        uu____24592 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24587 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24624 =
                             let uu____24630 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24630  in
                           (uu____24624, true)
                       | uu____24645 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24661 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24683 -> (FStar_Pervasives_Native.None, false))
  
let (get_fail_attr1 :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at  ->
      let rebind res b =
        match res with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some l ->
            FStar_Pervasives_Native.Some (l, b)
         in
      let uu____24800 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24800 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24849 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24849 with | (res1,uu____24871) -> rebind res1 true)
  
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term Prims.list ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun ats  ->
      let comb f1 f2 =
        match (f1, f2) with
        | (FStar_Pervasives_Native.Some (e1,l1),FStar_Pervasives_Native.Some
           (e2,l2)) ->
            FStar_Pervasives_Native.Some
              ((FStar_List.append e1 e2), (l1 || l2))
        | (FStar_Pervasives_Native.Some (e,l),FStar_Pervasives_Native.None )
            -> FStar_Pervasives_Native.Some (e, l)
        | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some (e,l))
            -> FStar_Pervasives_Native.Some (e, l)
        | uu____25198 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25256 = get_fail_attr1 warn at  in
             comb uu____25256 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25291 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25291 with
        | FStar_Pervasives_Native.None  ->
            let uu____25294 =
              let uu____25300 =
                let uu____25302 =
                  let uu____25304 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25304 " not found"  in
                Prims.op_Hat "Effect name " uu____25302  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25300)  in
            FStar_Errors.raise_error uu____25294 r
        | FStar_Pervasives_Native.Some l1 -> l1
  
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
        Prims.bool ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                FStar_Parser_AST.decl Prims.list ->
                  FStar_Parser_AST.term Prims.list ->
                    (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                      Prims.list))
  =
  fun env  ->
    fun d  ->
      fun quals  ->
        fun is_layered  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun eff_typ  ->
                fun eff_decls  ->
                  fun attrs  ->
                    let env0 = env  in
                    let monad_env =
                      FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                    let uu____25460 = desugar_binders monad_env eff_binders
                       in
                    match uu____25460 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25499 =
                            let uu____25508 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25508  in
                          FStar_List.length uu____25499  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25526 =
                              let uu____25532 =
                                let uu____25534 =
                                  let uu____25536 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25536
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25534  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25532)
                               in
                            FStar_Errors.raise_error uu____25526
                              d.FStar_Parser_AST.drange)
                         else ();
                         (let for_free = num_indices = Prims.int_one  in
                          let mandatory_members =
                            let rr_members = ["repr"; "return"; "bind"]  in
                            if for_free
                            then rr_members
                            else
                              if is_layered
                              then
                                FStar_List.append rr_members
                                  ["subcomp"; "if_then_else"]
                              else
                                FStar_List.append rr_members
                                  ["return_wp";
                                  "bind_wp";
                                  "if_then_else";
                                  "ite_wp";
                                  "stronger";
                                  "close_wp";
                                  "trivial"]
                             in
                          let name_of_eff_decl decl =
                            match decl.FStar_Parser_AST.d with
                            | FStar_Parser_AST.Tycon
                                (uu____25604,uu____25605,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25607,uu____25608,uu____25609))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25624 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25627 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25639 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25639 mandatory_members)
                              eff_decls
                             in
                          match uu____25627 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25658 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25687  ->
                                        fun decl  ->
                                          match uu____25687 with
                                          | (env2,out) ->
                                              let uu____25707 =
                                                desugar_decl env2 decl  in
                                              (match uu____25707 with
                                               | (env3,ses) ->
                                                   let uu____25720 =
                                                     let uu____25723 =
                                                       FStar_List.hd ses  in
                                                     uu____25723 :: out  in
                                                   (env3, uu____25720)))
                                     (env1, []))
                                 in
                              (match uu____25658 with
                               | (env2,decls) ->
                                   let binders1 =
                                     FStar_Syntax_Subst.close_binders binders
                                      in
                                   let actions1 =
                                     FStar_All.pipe_right actions
                                       (FStar_List.map
                                          (fun d1  ->
                                             match d1.FStar_Parser_AST.d with
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25769,uu____25770,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25773,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25774,(def,uu____25776)::
                                                        (cps_type,uu____25778)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25779;
                                                     FStar_Parser_AST.level =
                                                       uu____25780;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25813 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25813 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25845 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25846 =
                                                        let uu____25847 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25847
                                                         in
                                                      let uu____25854 =
                                                        let uu____25855 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25855
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25845;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25846;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25854
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25862,uu____25863,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25866,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____25882 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25882 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25914 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25915 =
                                                        let uu____25916 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25916
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25914;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25915;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25923 ->
                                                 FStar_Errors.raise_error
                                                   (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                     "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                   d1.FStar_Parser_AST.drange))
                                      in
                                   let eff_t1 =
                                     FStar_Syntax_Subst.close binders1 eff_t
                                      in
                                   let lookup s =
                                     let l =
                                       let uu____25942 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25942
                                        in
                                     let uu____25944 =
                                       let uu____25945 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25945
                                        in
                                     ([], uu____25944)  in
                                   let mname =
                                     FStar_Syntax_DsEnv.qualify env0 eff_name
                                      in
                                   let qualifiers =
                                     FStar_List.map
                                       (trans_qual d.FStar_Parser_AST.drange
                                          (FStar_Pervasives_Native.Some mname))
                                       quals
                                      in
                                   let dummy_tscheme =
                                     ([], FStar_Syntax_Syntax.tun)  in
                                   let combinators =
                                     if for_free
                                     then
                                       let uu____25967 =
                                         let uu____25968 =
                                           let uu____25971 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25971
                                            in
                                         let uu____25973 =
                                           let uu____25976 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25976
                                            in
                                         let uu____25978 =
                                           let uu____25981 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25981
                                            in
                                         {
                                           FStar_Syntax_Syntax.ret_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.bind_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.stronger =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.if_then_else =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.ite_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.close_wp =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.trivial =
                                             dummy_tscheme;
                                           FStar_Syntax_Syntax.repr =
                                             uu____25968;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25973;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25978
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25967
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26015 =
                                            match uu____26015 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26062 =
                                            let uu____26063 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26065 =
                                              let uu____26070 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26070 to_comb
                                               in
                                            let uu____26088 =
                                              let uu____26093 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26093 to_comb
                                               in
                                            let uu____26111 =
                                              let uu____26116 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26116 to_comb
                                               in
                                            let uu____26134 =
                                              let uu____26139 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26139 to_comb
                                               in
                                            let uu____26157 =
                                              let uu____26162 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26162 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26063;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26065;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26088;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26111;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26134;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26157
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26062)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26185  ->
                                                 match uu___27_26185 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26188 -> true
                                                 | uu____26190 -> false)
                                              qualifiers
                                             in
                                          let uu____26192 =
                                            let uu____26193 =
                                              lookup "return_wp"  in
                                            let uu____26195 =
                                              lookup "bind_wp"  in
                                            let uu____26197 =
                                              lookup "stronger"  in
                                            let uu____26199 =
                                              lookup "if_then_else"  in
                                            let uu____26201 = lookup "ite_wp"
                                               in
                                            let uu____26203 =
                                              lookup "close_wp"  in
                                            let uu____26205 =
                                              lookup "trivial"  in
                                            let uu____26207 =
                                              if rr
                                              then
                                                let uu____26213 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26213
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26217 =
                                              if rr
                                              then
                                                let uu____26223 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26223
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26227 =
                                              if rr
                                              then
                                                let uu____26233 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26233
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26193;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26195;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26197;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26199;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26201;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26203;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26205;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26207;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26217;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26227
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26192)
                                      in
                                   let sigel =
                                     let uu____26238 =
                                       let uu____26239 =
                                         FStar_List.map (desugar_term env2)
                                           attrs
                                          in
                                       {
                                         FStar_Syntax_Syntax.mname = mname;
                                         FStar_Syntax_Syntax.cattributes = [];
                                         FStar_Syntax_Syntax.univs = [];
                                         FStar_Syntax_Syntax.binders =
                                           binders1;
                                         FStar_Syntax_Syntax.signature =
                                           ([], eff_t1);
                                         FStar_Syntax_Syntax.combinators =
                                           combinators;
                                         FStar_Syntax_Syntax.actions =
                                           actions1;
                                         FStar_Syntax_Syntax.eff_attrs =
                                           uu____26239
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26238
                                      in
                                   let se =
                                     {
                                       FStar_Syntax_Syntax.sigel = sigel;
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals =
                                         qualifiers;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = [];
                                       FStar_Syntax_Syntax.sigopts =
                                         FStar_Pervasives_Native.None
                                     }  in
                                   let env3 =
                                     FStar_Syntax_DsEnv.push_sigelt env0 se
                                      in
                                   let env4 =
                                     FStar_All.pipe_right actions1
                                       (FStar_List.fold_left
                                          (fun env4  ->
                                             fun a  ->
                                               let uu____26256 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26256) env3)
                                      in
                                   let env5 =
                                     push_reflect_effect env4 qualifiers
                                       mname d.FStar_Parser_AST.drange
                                      in
                                   (env5, [se]))))

and (desugar_redefine_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      (FStar_Ident.lident FStar_Pervasives_Native.option ->
         FStar_Parser_AST.qualifier -> FStar_Syntax_Syntax.qualifier)
        ->
        FStar_Parser_AST.qualifier Prims.list ->
          FStar_Ident.ident ->
            FStar_Parser_AST.binder Prims.list ->
              FStar_Parser_AST.term ->
                (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt
                  Prims.list))
  =
  fun env  ->
    fun d  ->
      fun trans_qual1  ->
        fun quals  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun defn  ->
                let env0 = env  in
                let env1 = FStar_Syntax_DsEnv.enter_monad_scope env eff_name
                   in
                let uu____26279 = desugar_binders env1 eff_binders  in
                match uu____26279 with
                | (env2,binders) ->
                    let uu____26316 =
                      let uu____26327 = head_and_args defn  in
                      match uu____26327 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26364 ->
                                let uu____26365 =
                                  let uu____26371 =
                                    let uu____26373 =
                                      let uu____26375 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26375 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26373  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26371)
                                   in
                                FStar_Errors.raise_error uu____26365
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26381 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26411)::args_rev ->
                                let uu____26423 =
                                  let uu____26424 = unparen last_arg  in
                                  uu____26424.FStar_Parser_AST.tm  in
                                (match uu____26423 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26452 -> ([], args))
                            | uu____26461 -> ([], args)  in
                          (match uu____26381 with
                           | (cattributes,args1) ->
                               let uu____26504 = desugar_args env2 args1  in
                               let uu____26505 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26504, uu____26505))
                       in
                    (match uu____26316 with
                     | (ed_lid,ed,args,cattributes) ->
                         let binders1 =
                           FStar_Syntax_Subst.close_binders binders  in
                         (if
                            (FStar_List.length args) <>
                              (FStar_List.length
                                 ed.FStar_Syntax_Syntax.binders)
                          then
                            FStar_Errors.raise_error
                              (FStar_Errors.Fatal_ArgumentLengthMismatch,
                                "Unexpected number of arguments to effect constructor")
                              defn.FStar_Parser_AST.range
                          else ();
                          (let uu____26545 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26545 with
                           | (ed_binders,uu____26559,ed_binders_opening) ->
                               let sub' shift_n uu____26578 =
                                 match uu____26578 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26593 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26593 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26597 =
                                       let uu____26598 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26598)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26597
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26619 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26620 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26621 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26637 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26638 =
                                          let uu____26639 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26639
                                           in
                                        let uu____26654 =
                                          let uu____26655 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26655
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26637;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26638;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26654
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____26619;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26620;
                                   FStar_Syntax_Syntax.actions = uu____26621;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26671 =
                                   let uu____26674 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26674 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26671;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = [];
                                   FStar_Syntax_Syntax.sigopts =
                                     FStar_Pervasives_Native.None
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_Syntax_DsEnv.push_sigelt env0 se  in
                               let env4 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env4  ->
                                         fun a  ->
                                           let uu____26689 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26689) env3)
                                  in
                               let env5 =
                                 let uu____26691 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26691
                                 then
                                   let reflect_lid =
                                     let uu____26698 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26698
                                       (FStar_Syntax_DsEnv.qualify monad_env)
                                      in
                                   let quals1 =
                                     [FStar_Syntax_Syntax.Assumption;
                                     FStar_Syntax_Syntax.Reflectable mname]
                                      in
                                   let refl_decl =
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         (FStar_Syntax_Syntax.Sig_declare_typ
                                            (reflect_lid, [],
                                              FStar_Syntax_Syntax.tun));
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals = quals1;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = [];
                                       FStar_Syntax_Syntax.sigopts =
                                         FStar_Pervasives_Native.None
                                     }  in
                                   FStar_Syntax_DsEnv.push_sigelt env4
                                     refl_decl
                                 else env4  in
                               (env5, [se]))))

and (desugar_decl_aux :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      let no_fail_attrs ats =
        FStar_List.filter
          (fun at  ->
             let uu____26731 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26731) ats
         in
      let env0 =
        let uu____26752 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26752 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26767 =
        let uu____26774 = get_fail_attr false attrs  in
        match uu____26774 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3386_26811 = d  in
              {
                FStar_Parser_AST.d = (uu___3386_26811.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3386_26811.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3386_26811.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26812 =
              FStar_Errors.catch_errors
                (fun uu____26830  ->
                   FStar_Options.with_saved_options
                     (fun uu____26836  -> desugar_decl_noattrs env d1))
               in
            (match uu____26812 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3401_26896 = se  in
                             let uu____26897 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3401_26896.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3401_26896.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3401_26896.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3401_26896.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____26897;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3401_26896.FStar_Syntax_Syntax.sigopts)
                             }) ses
                         in
                      let se =
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_fail
                               (expected_errs, lax, ses1));
                          FStar_Syntax_Syntax.sigrng =
                            (d1.FStar_Parser_AST.drange);
                          FStar_Syntax_Syntax.sigquals = [];
                          FStar_Syntax_Syntax.sigmeta =
                            FStar_Syntax_Syntax.default_sigmeta;
                          FStar_Syntax_Syntax.sigattrs = [];
                          FStar_Syntax_Syntax.sigopts =
                            FStar_Pervasives_Native.None
                        }  in
                      (env0, [se])
                  | (errs1,ropt) ->
                      let errnos =
                        FStar_List.concatMap
                          (fun i  ->
                             FStar_Common.list_of_option
                               i.FStar_Errors.issue_number) errs1
                         in
                      if expected_errs = []
                      then (env0, [])
                      else
                        (let uu____26950 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____26950 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____26999 =
                                 let uu____27005 =
                                   let uu____27007 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27010 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27013 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27015 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27017 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27007 uu____27010 uu____27013
                                     uu____27015 uu____27017
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27005)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____26999);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26767 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27055;
                FStar_Syntax_Syntax.sigrng = uu____27056;
                FStar_Syntax_Syntax.sigquals = uu____27057;
                FStar_Syntax_Syntax.sigmeta = uu____27058;
                FStar_Syntax_Syntax.sigattrs = uu____27059;
                FStar_Syntax_Syntax.sigopts = uu____27060;_}::[] ->
                let uu____27073 =
                  let uu____27076 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27076  in
                FStar_All.pipe_right uu____27073
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27084 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27084))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27097;
                FStar_Syntax_Syntax.sigrng = uu____27098;
                FStar_Syntax_Syntax.sigquals = uu____27099;
                FStar_Syntax_Syntax.sigmeta = uu____27100;
                FStar_Syntax_Syntax.sigattrs = uu____27101;
                FStar_Syntax_Syntax.sigopts = uu____27102;_}::uu____27103 ->
                let uu____27128 =
                  let uu____27131 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27131  in
                FStar_All.pipe_right uu____27128
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27139 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27139))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27155;
                FStar_Syntax_Syntax.sigquals = uu____27156;
                FStar_Syntax_Syntax.sigmeta = uu____27157;
                FStar_Syntax_Syntax.sigattrs = uu____27158;
                FStar_Syntax_Syntax.sigopts = uu____27159;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27180 -> []  in
          let attrs1 =
            let uu____27186 = val_attrs sigelts  in
            FStar_List.append attrs uu____27186  in
          let uu____27189 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3461_27193 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3461_27193.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3461_27193.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3461_27193.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3461_27193.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3461_27193.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27189)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27200 = desugar_decl_aux env d  in
      match uu____27200 with
      | (env1,ses) ->
          let uu____27211 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27211)

and (desugar_decl_noattrs :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      let trans_qual1 = trans_qual d.FStar_Parser_AST.drange  in
      match d.FStar_Parser_AST.d with
      | FStar_Parser_AST.Pragma p ->
          let p1 = trans_pragma p  in
          (FStar_Syntax_Util.process_pragma p1 d.FStar_Parser_AST.drange;
           (let se =
              {
                FStar_Syntax_Syntax.sigel =
                  (FStar_Syntax_Syntax.Sig_pragma p1);
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            (env, [se])))
      | FStar_Parser_AST.TopLevelModule id -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____27243 = FStar_Syntax_DsEnv.iface env  in
          if uu____27243
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27258 =
               let uu____27260 =
                 let uu____27262 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27263 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27262
                   uu____27263
                  in
               Prims.op_Negation uu____27260  in
             if uu____27258
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27277 =
                  let uu____27279 =
                    let uu____27281 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27281 lid  in
                  Prims.op_Negation uu____27279  in
                if uu____27277
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27295 =
                     let uu____27297 =
                       let uu____27299 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27299
                         lid
                        in
                     Prims.op_Negation uu____27297  in
                   if uu____27295
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27317 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27317, [])
      | FStar_Parser_AST.Tycon (is_effect,typeclass,tcs) ->
          let quals = d.FStar_Parser_AST.quals  in
          let quals1 =
            if is_effect
            then FStar_Parser_AST.Effect_qual :: quals
            else quals  in
          let quals2 =
            if typeclass
            then
              match tcs with
              | (FStar_Parser_AST.TyconRecord uu____27346)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27365 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27374 =
            let uu____27379 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27379 tcs  in
          (match uu____27374 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27396 =
                   let uu____27397 =
                     let uu____27404 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27404  in
                   [uu____27397]  in
                 let uu____27417 =
                   let uu____27420 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27423 =
                     let uu____27434 =
                       let uu____27443 =
                         let uu____27444 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27444  in
                       FStar_Syntax_Syntax.as_arg uu____27443  in
                     [uu____27434]  in
                   FStar_Syntax_Util.mk_app uu____27420 uu____27423  in
                 FStar_Syntax_Util.abs uu____27396 uu____27417
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27484,id))::uu____27486 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27489::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27493 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27493 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27499 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27499]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27520) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27530,uu____27531,uu____27532,uu____27533,uu____27534)
                     ->
                     let uu____27543 =
                       let uu____27544 =
                         let uu____27545 =
                           let uu____27552 = mkclass lid  in
                           (meths, uu____27552)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27545  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27544;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27543]
                 | uu____27555 -> []  in
               let extra =
                 if typeclass
                 then
                   let meths = FStar_List.concatMap get_meths ses  in
                   FStar_List.concatMap (splice_decl meths) ses
                 else []  in
               let env2 =
                 FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
                   extra
                  in
               (env2, (FStar_List.append ses extra)))
      | FStar_Parser_AST.TopLevelLet (isrec,lets) ->
          let quals = d.FStar_Parser_AST.quals  in
          let expand_toplevel_pattern =
            (isrec = FStar_Parser_AST.NoLetQualifier) &&
              (match lets with
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27589;
                    FStar_Parser_AST.prange = uu____27590;_},uu____27591)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27601;
                    FStar_Parser_AST.prange = uu____27602;_},uu____27603)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27619;
                         FStar_Parser_AST.prange = uu____27620;_},uu____27621);
                    FStar_Parser_AST.prange = uu____27622;_},uu____27623)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27645;
                         FStar_Parser_AST.prange = uu____27646;_},uu____27647);
                    FStar_Parser_AST.prange = uu____27648;_},uu____27649)::[]
                   -> false
               | (p,uu____27678)::[] ->
                   let uu____27687 = is_app_pattern p  in
                   Prims.op_Negation uu____27687
               | uu____27689 -> false)
             in
          if Prims.op_Negation expand_toplevel_pattern
          then
            let lets1 =
              FStar_List.map (fun x  -> (FStar_Pervasives_Native.None, x))
                lets
               in
            let as_inner_let =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Let
                   (isrec, lets1,
                     (FStar_Parser_AST.mk_term
                        (FStar_Parser_AST.Const FStar_Const.Const_unit)
                        d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))
                d.FStar_Parser_AST.drange FStar_Parser_AST.Expr
               in
            let uu____27764 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27764 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27777 =
                     let uu____27778 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27778.FStar_Syntax_Syntax.n  in
                   match uu____27777 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27788) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27819 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27844  ->
                                match uu____27844 with
                                | (qs,ats) ->
                                    let uu____27871 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27871 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27819 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27925::uu____27926 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27929 -> val_quals  in
                            let quals2 =
                              let uu____27933 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27966  ->
                                        match uu____27966 with
                                        | (uu____27980,(uu____27981,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27933
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28001 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28001
                              then
                                let uu____28007 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3638_28022 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3640_28024 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3640_28024.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3640_28024.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3638_28022.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3638_28022.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3638_28022.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3638_28022.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3638_28022.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3638_28022.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28007)
                              else lbs  in
                            let names =
                              FStar_All.pipe_right fvs
                                (FStar_List.map
                                   (fun fv  ->
                                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
                               in
                            let attrs =
                              FStar_List.map (desugar_term env)
                                d.FStar_Parser_AST.attrs
                               in
                            let s =
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_let (lbs1, names));
                                FStar_Syntax_Syntax.sigrng =
                                  (d.FStar_Parser_AST.drange);
                                FStar_Syntax_Syntax.sigquals = quals2;
                                FStar_Syntax_Syntax.sigmeta =
                                  FStar_Syntax_Syntax.default_sigmeta;
                                FStar_Syntax_Syntax.sigattrs =
                                  (FStar_List.append val_attrs attrs);
                                FStar_Syntax_Syntax.sigopts =
                                  FStar_Pervasives_Native.None
                              }  in
                            let env1 = FStar_Syntax_DsEnv.push_sigelt env s
                               in
                            (env1, [s]))
                   | uu____28049 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28057 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28076 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28057 with
             | (pat,body) ->
                 let fresh_toplevel_name =
                   FStar_Ident.gen FStar_Range.dummyRange  in
                 let fresh_pat =
                   let var_pat =
                     FStar_Parser_AST.mk_pattern
                       (FStar_Parser_AST.PatVar
                          (fresh_toplevel_name, FStar_Pervasives_Native.None))
                       FStar_Range.dummyRange
                      in
                   match pat.FStar_Parser_AST.pat with
                   | FStar_Parser_AST.PatAscribed (pat1,ty) ->
                       let uu___3663_28113 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3663_28113.FStar_Parser_AST.prange)
                       }
                   | uu____28120 -> var_pat  in
                 let main_let =
                   let quals1 =
                     if
                       FStar_List.mem FStar_Parser_AST.Private
                         d.FStar_Parser_AST.quals
                     then d.FStar_Parser_AST.quals
                     else FStar_Parser_AST.Private ::
                       (d.FStar_Parser_AST.quals)
                      in
                   desugar_decl env
                     (let uu___3669_28131 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3669_28131.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3669_28131.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28147 =
                     let uu____28148 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28148  in
                   FStar_Parser_AST.mk_term uu____28147
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28172 id_opt =
                   match uu____28172 with
                   | (env1,ses) ->
                       let uu____28194 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28206 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28206
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28208 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28208
                                in
                             (bv_pat, branch)
                         | FStar_Pervasives_Native.None  ->
                             let id = FStar_Ident.gen FStar_Range.dummyRange
                                in
                             let branch =
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Const
                                    FStar_Const.Const_unit)
                                 FStar_Range.dummyRange FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28214 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28214
                                in
                             let bv_pat1 =
                               let uu____28218 =
                                 let uu____28219 =
                                   let uu____28230 =
                                     let uu____28237 =
                                       let uu____28238 =
                                         FStar_Ident.range_of_id id  in
                                       unit_ty uu____28238  in
                                     (uu____28237,
                                       FStar_Pervasives_Native.None)
                                      in
                                   (bv_pat, uu____28230)  in
                                 FStar_Parser_AST.PatAscribed uu____28219  in
                               let uu____28247 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern uu____28218
                                 uu____28247
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28194 with
                        | (bv_pat,branch) ->
                            let body1 =
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Match
                                   (main,
                                     [(pat, FStar_Pervasives_Native.None,
                                        branch)]))
                                main.FStar_Parser_AST.range
                                FStar_Parser_AST.Expr
                               in
                            let id_decl =
                              FStar_Parser_AST.mk_decl
                                (FStar_Parser_AST.TopLevelLet
                                   (FStar_Parser_AST.NoLetQualifier,
                                     [(bv_pat, body1)]))
                                FStar_Range.dummyRange []
                               in
                            let id_decl1 =
                              let uu___3693_28301 = id_decl  in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3693_28301.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3693_28301.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3693_28301.FStar_Parser_AST.attrs)
                              }  in
                            let uu____28302 = desugar_decl env1 id_decl1  in
                            (match uu____28302 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28338 id =
                   match uu____28338 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28377 =
                   match uu____28377 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28401 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28401 FStar_Util.set_elements
                    in
                 let uu____28408 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28411 = is_var_pattern pat  in
                      Prims.op_Negation uu____28411)
                    in
                 if uu____28408
                 then build_coverage_check main_let
                 else FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Assume (id,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          (env,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = [];
               FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
             }])
      | FStar_Parser_AST.Val (id,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____28434 = close_fun env t  in
            desugar_term env uu____28434  in
          let quals1 =
            let uu____28438 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28438
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28450 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28450;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])
      | FStar_Parser_AST.Exception (id,t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term  in
                let uu____28463 =
                  let uu____28472 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28472]  in
                let uu____28491 =
                  let uu____28494 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28494
                   in
                FStar_Syntax_Util.arrow uu____28463 uu____28491
             in
          let l = FStar_Syntax_DsEnv.qualify env id  in
          let qual = [FStar_Syntax_Syntax.ExceptionConstructor]  in
          let se =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_datacon
                   (l, [], t, FStar_Parser_Const.exn_lid, Prims.int_zero,
                     [FStar_Parser_Const.exn_lid]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
          let data_ops = mk_data_projector_names [] env1 se  in
          let discs = mk_data_discriminators [] env1 [l]  in
          let env2 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1
              (FStar_List.append discs data_ops)
             in
          (env2, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals false eff_name eff_binders eff_typ
            eff_decls attrs
      | FStar_Parser_AST.LayeredEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals true eff_name eff_binders eff_typ
            eff_decls attrs
      | FStar_Parser_AST.LayeredEffect (FStar_Parser_AST.RedefineEffect
          uu____28557) ->
          failwith
            "Impossible: LayeredEffect (RedefineEffect _) (should not be parseable)"
      | FStar_Parser_AST.SubEffect l ->
          let src_ed =
            lookup_effect_lid env l.FStar_Parser_AST.msource
              d.FStar_Parser_AST.drange
             in
          let dst_ed =
            lookup_effect_lid env l.FStar_Parser_AST.mdest
              d.FStar_Parser_AST.drange
             in
          let uu____28574 =
            let uu____28576 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28576  in
          if uu____28574
          then
            let uu____28583 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28601 =
                    let uu____28604 =
                      let uu____28605 = desugar_term env t  in
                      ([], uu____28605)  in
                    FStar_Pervasives_Native.Some uu____28604  in
                  (uu____28601, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28618 =
                    let uu____28621 =
                      let uu____28622 = desugar_term env wp  in
                      ([], uu____28622)  in
                    FStar_Pervasives_Native.Some uu____28621  in
                  let uu____28629 =
                    let uu____28632 =
                      let uu____28633 = desugar_term env t  in
                      ([], uu____28633)  in
                    FStar_Pervasives_Native.Some uu____28632  in
                  (uu____28618, uu____28629)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28645 =
                    let uu____28648 =
                      let uu____28649 = desugar_term env t  in
                      ([], uu____28649)  in
                    FStar_Pervasives_Native.Some uu____28648  in
                  (FStar_Pervasives_Native.None, uu____28645)
               in
            (match uu____28583 with
             | (lift_wp,lift) ->
                 let se =
                   {
                     FStar_Syntax_Syntax.sigel =
                       (FStar_Syntax_Syntax.Sig_sub_effect
                          {
                            FStar_Syntax_Syntax.source =
                              (src_ed.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.target =
                              (dst_ed.FStar_Syntax_Syntax.mname);
                            FStar_Syntax_Syntax.lift_wp = lift_wp;
                            FStar_Syntax_Syntax.lift = lift
                          });
                     FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                     FStar_Syntax_Syntax.sigquals = [];
                     FStar_Syntax_Syntax.sigmeta =
                       FStar_Syntax_Syntax.default_sigmeta;
                     FStar_Syntax_Syntax.sigattrs = [];
                     FStar_Syntax_Syntax.sigopts =
                       FStar_Pervasives_Native.None
                   }  in
                 (env, [se]))
          else
            (match l.FStar_Parser_AST.lift_op with
             | FStar_Parser_AST.NonReifiableLift t ->
                 let sub_eff =
                   let uu____28683 =
                     let uu____28686 =
                       let uu____28687 = desugar_term env t  in
                       ([], uu____28687)  in
                     FStar_Pervasives_Native.Some uu____28686  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28683
                   }  in
                 (env,
                   [{
                      FStar_Syntax_Syntax.sigel =
                        (FStar_Syntax_Syntax.Sig_sub_effect sub_eff);
                      FStar_Syntax_Syntax.sigrng =
                        (d.FStar_Parser_AST.drange);
                      FStar_Syntax_Syntax.sigquals = [];
                      FStar_Syntax_Syntax.sigmeta =
                        FStar_Syntax_Syntax.default_sigmeta;
                      FStar_Syntax_Syntax.sigattrs = [];
                      FStar_Syntax_Syntax.sigopts =
                        FStar_Pervasives_Native.None
                    }])
             | uu____28694 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28707 =
            let uu____28708 =
              let uu____28709 =
                let uu____28710 =
                  let uu____28721 =
                    let uu____28722 = desugar_term env bind  in
                    ([], uu____28722)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28721,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28710  in
              {
                FStar_Syntax_Syntax.sigel = uu____28709;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28708]  in
          (env, uu____28707)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28741 =
              let uu____28742 =
                let uu____28749 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28749, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28742  in
            {
              FStar_Syntax_Syntax.sigel = uu____28741;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____28776 =
        FStar_List.fold_left
          (fun uu____28796  ->
             fun d  ->
               match uu____28796 with
               | (env1,sigelts) ->
                   let uu____28816 = desugar_decl env1 d  in
                   (match uu____28816 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28776 with | (env1,sigelts) -> (env1, sigelts)
  
let (open_prims_all :
  (FStar_Parser_AST.decoration Prims.list -> FStar_Parser_AST.decl)
    Prims.list)
  =
  [FStar_Parser_AST.mk_decl
     (FStar_Parser_AST.Open FStar_Parser_Const.prims_lid)
     FStar_Range.dummyRange;
  FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open FStar_Parser_Const.all_lid)
    FStar_Range.dummyRange]
  
let (desugar_modul_common :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.modul ->
        (env_t * FStar_Syntax_Syntax.modul * Prims.bool))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let env1 =
          match (curmod, m) with
          | (FStar_Pervasives_Native.None ,uu____28907) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28911;
               FStar_Syntax_Syntax.exports = uu____28912;
               FStar_Syntax_Syntax.is_interface = uu____28913;_},FStar_Parser_AST.Module
             (current_lid,uu____28915)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28924) ->
              let uu____28927 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28927
           in
        let uu____28932 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28974 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28974, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28996 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28996, mname, decls, false)
           in
        match uu____28932 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29038 = desugar_decls env2 decls  in
            (match uu____29038 with
             | (env3,sigelts) ->
                 let modul =
                   {
                     FStar_Syntax_Syntax.name = mname;
                     FStar_Syntax_Syntax.declarations = sigelts;
                     FStar_Syntax_Syntax.exports = [];
                     FStar_Syntax_Syntax.is_interface = intf
                   }  in
                 (env3, modul, pop_when_done))
  
let (as_interface : FStar_Parser_AST.modul -> FStar_Parser_AST.modul) =
  fun m  ->
    match m with
    | FStar_Parser_AST.Module (mname,decls) ->
        FStar_Parser_AST.Interface (mname, decls, true)
    | i -> i
  
let (desugar_partial_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    env_t -> FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun curmod  ->
    fun env  ->
      fun m  ->
        let m1 =
          let uu____29106 =
            (FStar_Options.interactive ()) &&
              (let uu____29109 =
                 let uu____29111 =
                   let uu____29113 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29113  in
                 FStar_Util.get_file_extension uu____29111  in
               FStar_List.mem uu____29109 ["fsti"; "fsi"])
             in
          if uu____29106 then as_interface m else m  in
        let uu____29127 = desugar_modul_common curmod env m1  in
        match uu____29127 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29149 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29149, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29171 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29171 with
      | (env1,modul,pop_when_done) ->
          let uu____29188 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29188 with
           | (env2,modul1) ->
               ((let uu____29200 =
                   let uu____29202 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29202  in
                 if uu____29200
                 then
                   let uu____29205 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29205
                 else ());
                (let uu____29210 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29210, modul1))))
  
let with_options : 'a . (unit -> 'a) -> 'a =
  fun f  ->
    FStar_Options.push ();
    (let res = f ()  in
     let light = FStar_Options.ml_ish ()  in
     FStar_Options.pop ();
     if light then FStar_Options.set_ml_ish () else ();
     res)
  
let (ast_modul_to_modul :
  FStar_Parser_AST.modul ->
    FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun env  ->
      with_options
        (fun uu____29260  ->
           let uu____29261 = desugar_modul env modul  in
           match uu____29261 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29299  ->
           let uu____29300 = desugar_decls env decls  in
           match uu____29300 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29351  ->
             let uu____29352 = desugar_partial_modul modul env a_modul  in
             match uu____29352 with | (env1,modul1) -> (modul1, env1))
  
let (add_modul_to_env :
  FStar_Syntax_Syntax.modul ->
    FStar_Syntax_DsEnv.module_inclusion_info ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        unit FStar_Syntax_DsEnv.withenv)
  =
  fun m  ->
    fun mii  ->
      fun erase_univs  ->
        fun en  ->
          let erase_univs_ed ed =
            let erase_binders bs =
              match bs with
              | [] -> []
              | uu____29447 ->
                  let t =
                    let uu____29457 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29457  in
                  let uu____29470 =
                    let uu____29471 = FStar_Syntax_Subst.compress t  in
                    uu____29471.FStar_Syntax_Syntax.n  in
                  (match uu____29470 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29483,uu____29484)
                       -> bs1
                   | uu____29509 -> failwith "Impossible")
               in
            let uu____29519 =
              let uu____29526 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29526
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29519 with
            | (binders,uu____29528,binders_opening) ->
                let erase_term t =
                  let uu____29536 =
                    let uu____29537 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29537  in
                  FStar_Syntax_Subst.close binders uu____29536  in
                let erase_tscheme uu____29555 =
                  match uu____29555 with
                  | (us,t) ->
                      let t1 =
                        let uu____29575 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29575 t  in
                      let uu____29578 =
                        let uu____29579 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29579  in
                      ([], uu____29578)
                   in
                let erase_action action =
                  let opening =
                    FStar_Syntax_Subst.shift_subst
                      (FStar_List.length
                         action.FStar_Syntax_Syntax.action_univs)
                      binders_opening
                     in
                  let erased_action_params =
                    match action.FStar_Syntax_Syntax.action_params with
                    | [] -> []
                    | uu____29602 ->
                        let bs =
                          let uu____29612 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29612  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29652 =
                          let uu____29653 =
                            let uu____29656 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29656  in
                          uu____29653.FStar_Syntax_Syntax.n  in
                        (match uu____29652 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29658,uu____29659) -> bs1
                         | uu____29684 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29692 =
                      let uu____29693 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29693  in
                    FStar_Syntax_Subst.close binders uu____29692  in
                  let uu___3964_29694 = action  in
                  let uu____29695 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29696 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3964_29694.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3964_29694.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29695;
                    FStar_Syntax_Syntax.action_typ = uu____29696
                  }  in
                let uu___3966_29697 = ed  in
                let uu____29698 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29699 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29700 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29701 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3966_29697.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3966_29697.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29698;
                  FStar_Syntax_Syntax.signature = uu____29699;
                  FStar_Syntax_Syntax.combinators = uu____29700;
                  FStar_Syntax_Syntax.actions = uu____29701;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3966_29697.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3973_29717 = se  in
                  let uu____29718 =
                    let uu____29719 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29719  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29718;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3973_29717.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3973_29717.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3973_29717.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3973_29717.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3973_29717.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29721 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29722 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29722 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29739 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29739
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29741 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29741)
  