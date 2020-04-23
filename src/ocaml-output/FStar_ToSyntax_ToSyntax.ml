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
    | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____3457 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3466 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3473 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3481  ->
    match uu___4_3481 with
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
    | uu____3530 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3551 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3551)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3577 =
      let uu____3578 = unparen t  in uu____3578.FStar_Parser_AST.tm  in
    match uu____3577 with
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3588)) ->
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
             let uu____3679 = sum_to_universe u n  in
             FStar_Util.Inr uu____3679
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3696 = sum_to_universe u n  in
             FStar_Util.Inr uu____3696
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3712 =
               let uu____3718 =
                 let uu____3720 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3720
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3718)
                in
             FStar_Errors.raise_error uu____3712 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3729 ->
        let rec aux t1 univargs =
          let uu____3766 =
            let uu____3767 = unparen t1  in uu____3767.FStar_Parser_AST.tm
             in
          match uu____3766 with
          | FStar_Parser_AST.App (t2,targ,uu____3775) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3802  ->
                     match uu___5_3802 with
                     | FStar_Util.Inr uu____3809 -> true
                     | uu____3812 -> false) univargs
              then
                let uu____3820 =
                  let uu____3821 =
                    FStar_List.map
                      (fun uu___6_3831  ->
                         match uu___6_3831 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3821  in
                FStar_Util.Inr uu____3820
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3857  ->
                        match uu___7_3857 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3867 -> failwith "impossible")
                     univargs
                    in
                 let uu____3871 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3871)
          | uu____3887 ->
              let uu____3888 =
                let uu____3894 =
                  let uu____3896 =
                    let uu____3898 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3898 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3896  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3894)  in
              FStar_Errors.raise_error uu____3888 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3913 ->
        let uu____3914 =
          let uu____3920 =
            let uu____3922 =
              let uu____3924 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3924 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3922  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3920)  in
        FStar_Errors.raise_error uu____3914 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3965;_});
            FStar_Syntax_Syntax.pos = uu____3966;
            FStar_Syntax_Syntax.vars = uu____3967;_})::uu____3968
        ->
        let uu____3999 =
          let uu____4005 =
            let uu____4007 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4007
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4005)  in
        FStar_Errors.raise_error uu____3999 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4013 ->
        let uu____4032 =
          let uu____4038 =
            let uu____4040 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4040
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4038)  in
        FStar_Errors.raise_error uu____4032 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4053 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4053) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4081 = FStar_List.hd fields  in
        match uu____4081 with
        | (f,uu____4091) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4102 =
              match uu____4102 with
              | (f',uu____4108) ->
                  let uu____4109 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4109
                  then ()
                  else
                    (let msg =
                       let uu____4116 = FStar_Ident.string_of_lid f  in
                       let uu____4118 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4120 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4116 uu____4118 uu____4120
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4125 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4125);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4173 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4180 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4181 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4183,pats1) ->
            let aux out uu____4224 =
              match uu____4224 with
              | (p1,uu____4237) ->
                  let intersection =
                    let uu____4247 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4247 out  in
                  let uu____4250 = FStar_Util.set_is_empty intersection  in
                  if uu____4250
                  then
                    let uu____4255 = pat_vars p1  in
                    FStar_Util.set_union out uu____4255
                  else
                    (let duplicate_bv =
                       let uu____4261 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4261  in
                     let uu____4264 =
                       let uu____4270 =
                         let uu____4272 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4272
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4270)
                        in
                     FStar_Errors.raise_error uu____4264 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4296 = pat_vars p  in
          FStar_All.pipe_right uu____4296 (fun uu____4301  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4325 =
              let uu____4327 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4327  in
            if uu____4325
            then ()
            else
              (let nonlinear_vars =
                 let uu____4336 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4336  in
               let first_nonlinear_var =
                 let uu____4340 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4340  in
               let uu____4343 =
                 let uu____4349 =
                   let uu____4351 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4351
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4349)  in
               FStar_Errors.raise_error uu____4343 r)
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
          let uu____4678 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4685 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4687 = FStar_Ident.text_of_id x  in
                 uu____4685 = uu____4687) l
             in
          match uu____4678 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4701 ->
              let uu____4704 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4704 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4845 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4867 =
                  let uu____4873 =
                    let uu____4875 = FStar_Ident.text_of_id op  in
                    let uu____4877 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4875
                      uu____4877
                     in
                  let uu____4879 = FStar_Ident.range_of_id op  in
                  (uu____4873, uu____4879)  in
                FStar_Ident.mk_ident uu____4867  in
              let p2 =
                let uu___909_4882 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___909_4882.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4899 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4902 = aux loc env1 p2  in
                match uu____4902 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____4958 =
                      match binder with
                      | LetBinder uu____4979 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5004 = close_fun env1 t  in
                            desugar_term env1 uu____5004  in
                          let x1 =
                            let uu___935_5006 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___935_5006.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___935_5006.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____4958 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5052 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5053 -> ()
                           | uu____5054 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5055 ->
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
              let uu____5073 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5073, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5086 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5086, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5104 = resolvex loc env1 x  in
              (match uu____5104 with
               | (loc1,env2,xbv) ->
                   let uu____5136 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5136, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5154 = resolvex loc env1 x  in
              (match uu____5154 with
               | (loc1,env2,xbv) ->
                   let uu____5186 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5186, []))
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
              let uu____5200 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5200, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5228;_},args)
              ->
              let uu____5234 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5295  ->
                       match uu____5295 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5376 = aux loc1 env2 arg  in
                           (match uu____5376 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5234 with
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
                   let uu____5548 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5548, annots))
          | FStar_Parser_AST.PatApp uu____5564 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5592 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5642  ->
                       match uu____5642 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5703 = aux loc1 env2 pat  in
                           (match uu____5703 with
                            | (loc2,env3,uu____5742,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5592 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5836 =
                       let uu____5839 =
                         let uu____5846 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5846  in
                       let uu____5847 =
                         let uu____5848 =
                           let uu____5862 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5862, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5848  in
                       FStar_All.pipe_left uu____5839 uu____5847  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____5896 =
                              let uu____5897 =
                                let uu____5911 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5911, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____5897  in
                            FStar_All.pipe_left (pos_r r) uu____5896) pats1
                       uu____5836
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
              let uu____5967 =
                FStar_List.fold_left
                  (fun uu____6026  ->
                     fun p2  ->
                       match uu____6026 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6108 = aux loc1 env2 p2  in
                           (match uu____6108 with
                            | (loc2,env3,uu____6152,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____5967 with
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
                     | uu____6315 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6318 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6318, annots))
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
                     (fun uu____6395  ->
                        match uu____6395 with
                        | (f,p2) ->
                            let uu____6406 = FStar_Ident.ident_of_lid f  in
                            (uu____6406, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6426  ->
                        match uu____6426 with
                        | (f,uu____6432) ->
                            let uu____6433 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6461  ->
                                      match uu____6461 with
                                      | (g,uu____6468) ->
                                          let uu____6469 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6471 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6469 = uu____6471))
                               in
                            (match uu____6433 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6478,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6485 =
                  let uu____6486 =
                    let uu____6493 =
                      let uu____6494 =
                        let uu____6495 =
                          let uu____6496 =
                            let uu____6497 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6497
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6496  in
                        FStar_Parser_AST.PatName uu____6495  in
                      FStar_Parser_AST.mk_pattern uu____6494
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6493, args)  in
                  FStar_Parser_AST.PatApp uu____6486  in
                FStar_Parser_AST.mk_pattern uu____6485
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6502 = aux loc env1 app  in
              (match uu____6502 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6579 =
                           let uu____6580 =
                             let uu____6594 =
                               let uu___1085_6595 = fv  in
                               let uu____6596 =
                                 let uu____6599 =
                                   let uu____6600 =
                                     let uu____6607 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6607)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6600
                                    in
                                 FStar_Pervasives_Native.Some uu____6599  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1085_6595.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1085_6595.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6596
                               }  in
                             (uu____6594, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6580  in
                         FStar_All.pipe_left pos uu____6579
                     | uu____6633 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6717 = aux' true loc env1 p2  in
              (match uu____6717 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6770 =
                     FStar_List.fold_left
                       (fun uu____6818  ->
                          fun p4  ->
                            match uu____6818 with
                            | (loc2,env3,ps1) ->
                                let uu____6883 = aux' true loc2 env3 p4  in
                                (match uu____6883 with
                                 | (loc3,env4,uu____6921,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6770 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7082 ->
              let uu____7083 = aux' true loc env1 p1  in
              (match uu____7083 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7174 = aux_maybe_or env p  in
        match uu____7174 with
        | (env1,b,pats) ->
            ((let uu____7229 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7229
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
            let uu____7303 =
              let uu____7304 =
                let uu____7315 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7315, (ty, tacopt))  in
              LetBinder uu____7304  in
            (env, uu____7303, [])  in
          let op_to_ident x =
            let uu____7332 =
              let uu____7338 =
                let uu____7340 = FStar_Ident.text_of_id x  in
                let uu____7342 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7340
                  uu____7342
                 in
              let uu____7344 = FStar_Ident.range_of_id x  in
              (uu____7338, uu____7344)  in
            FStar_Ident.mk_ident uu____7332  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7355 = op_to_ident x  in
              mklet uu____7355 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7357) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7363;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7379 = op_to_ident x  in
              let uu____7380 = desugar_term env t  in
              mklet uu____7379 uu____7380 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7382);
                 FStar_Parser_AST.prange = uu____7383;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7403 = desugar_term env t  in
              mklet x uu____7403 tacopt1
          | uu____7404 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7417 = desugar_data_pat true env p  in
           match uu____7417 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7447;
                      FStar_Syntax_Syntax.p = uu____7448;_},uu____7449)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7462;
                      FStar_Syntax_Syntax.p = uu____7463;_},uu____7464)::[]
                     -> []
                 | uu____7477 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7485  ->
    fun env  ->
      fun pat  ->
        let uu____7489 = desugar_data_pat false env pat  in
        match uu____7489 with | (env1,uu____7506,pat1) -> (env1, pat1)

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
      let uu____7528 = desugar_term_aq env e  in
      match uu____7528 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7547 = desugar_typ_aq env e  in
      match uu____7547 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7557  ->
        fun range  ->
          match uu____7557 with
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
              ((let uu____7579 =
                  let uu____7581 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7581  in
                if uu____7579
                then
                  let uu____7584 =
                    let uu____7590 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7590)  in
                  FStar_Errors.log_issue range uu____7584
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
                  let uu____7611 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7611 range  in
                let lid1 =
                  let uu____7615 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7615 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7625 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7625 range  in
                           let private_fv =
                             let uu____7627 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7627 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1252_7628 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1252_7628.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1252_7628.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7629 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7633 =
                        let uu____7639 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7639)
                         in
                      FStar_Errors.raise_error uu____7633 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7659 =
                  let uu____7666 =
                    let uu____7667 =
                      let uu____7684 =
                        let uu____7695 =
                          let uu____7704 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7704)  in
                        [uu____7695]  in
                      (lid1, uu____7684)  in
                    FStar_Syntax_Syntax.Tm_app uu____7667  in
                  FStar_Syntax_Syntax.mk uu____7666  in
                uu____7659 FStar_Pervasives_Native.None range))

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
          let uu___1268_7823 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1268_7823.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1268_7823.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7826 =
          let uu____7827 = unparen top  in uu____7827.FStar_Parser_AST.tm  in
        match uu____7826 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7832 ->
            let uu____7841 = desugar_formula env top  in (uu____7841, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7850 = desugar_formula env t  in (uu____7850, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7859 = desugar_formula env t  in (uu____7859, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7886 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7886, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7888 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7888, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____7895 = FStar_Ident.text_of_id id  in uu____7895 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____7901 =
                let uu____7902 =
                  let uu____7909 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7909, args)  in
                FStar_Parser_AST.Op uu____7902  in
              FStar_Parser_AST.mk_term uu____7901 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7914 =
              let uu____7915 =
                let uu____7916 =
                  let uu____7923 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7923, [e])  in
                FStar_Parser_AST.Op uu____7916  in
              FStar_Parser_AST.mk_term uu____7915 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7914
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7935 = FStar_Ident.text_of_id op_star  in
             uu____7935 = "*") &&
              (let uu____7940 = op_as_term env (Prims.of_int (2)) op_star  in
               FStar_All.pipe_right uu____7940 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____7964 = FStar_Ident.text_of_id id  in
                   uu____7964 = "*") &&
                    (let uu____7969 =
                       op_as_term env (Prims.of_int (2)) op_star  in
                     FStar_All.pipe_right uu____7969 FStar_Option.isNone)
                  ->
                  let uu____7976 = flatten t1  in
                  FStar_List.append uu____7976 [t2]
              | uu____7979 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1313_7984 = top  in
              let uu____7985 =
                let uu____7986 =
                  let uu____7997 =
                    FStar_List.map
                      (fun uu____8008  -> FStar_Util.Inr uu____8008) terms
                     in
                  (uu____7997, rhs)  in
                FStar_Parser_AST.Sum uu____7986  in
              {
                FStar_Parser_AST.tm = uu____7985;
                FStar_Parser_AST.range =
                  (uu___1313_7984.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1313_7984.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8016 =
              let uu____8017 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8017  in
            (uu____8016, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8023 =
              let uu____8029 =
                let uu____8031 =
                  let uu____8033 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8033 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8031  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8029)  in
            FStar_Errors.raise_error uu____8023 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8048 = op_as_term env (FStar_List.length args) s  in
            (match uu____8048 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8055 =
                   let uu____8061 =
                     let uu____8063 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8063
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8061)
                    in
                 FStar_Errors.raise_error uu____8055
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8078 =
                     let uu____8103 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8165 = desugar_term_aq env t  in
                               match uu____8165 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8103 FStar_List.unzip  in
                   (match uu____8078 with
                    | (args1,aqs) ->
                        let uu____8298 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8298, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8315)::[]) when
            let uu____8330 = FStar_Ident.string_of_lid n  in
            uu____8330 = "SMTPat" ->
            let uu____8334 =
              let uu___1342_8335 = top  in
              let uu____8336 =
                let uu____8337 =
                  let uu____8344 =
                    let uu___1344_8345 = top  in
                    let uu____8346 =
                      let uu____8347 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8347  in
                    {
                      FStar_Parser_AST.tm = uu____8346;
                      FStar_Parser_AST.range =
                        (uu___1344_8345.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1344_8345.FStar_Parser_AST.level)
                    }  in
                  (uu____8344, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8337  in
              {
                FStar_Parser_AST.tm = uu____8336;
                FStar_Parser_AST.range =
                  (uu___1342_8335.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1342_8335.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8334
        | FStar_Parser_AST.Construct (n,(a,uu____8350)::[]) when
            let uu____8365 = FStar_Ident.string_of_lid n  in
            uu____8365 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8372 =
                let uu___1354_8373 = top  in
                let uu____8374 =
                  let uu____8375 =
                    let uu____8382 =
                      let uu___1356_8383 = top  in
                      let uu____8384 =
                        let uu____8385 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8385  in
                      {
                        FStar_Parser_AST.tm = uu____8384;
                        FStar_Parser_AST.range =
                          (uu___1356_8383.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1356_8383.FStar_Parser_AST.level)
                      }  in
                    (uu____8382, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8375  in
                {
                  FStar_Parser_AST.tm = uu____8374;
                  FStar_Parser_AST.range =
                    (uu___1354_8373.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1354_8373.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8372))
        | FStar_Parser_AST.Construct (n,(a,uu____8388)::[]) when
            let uu____8403 = FStar_Ident.string_of_lid n  in
            uu____8403 = "SMTPatOr" ->
            let uu____8407 =
              let uu___1365_8408 = top  in
              let uu____8409 =
                let uu____8410 =
                  let uu____8417 =
                    let uu___1367_8418 = top  in
                    let uu____8419 =
                      let uu____8420 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8420  in
                    {
                      FStar_Parser_AST.tm = uu____8419;
                      FStar_Parser_AST.range =
                        (uu___1367_8418.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1367_8418.FStar_Parser_AST.level)
                    }  in
                  (uu____8417, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8410  in
              {
                FStar_Parser_AST.tm = uu____8409;
                FStar_Parser_AST.range =
                  (uu___1365_8408.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1365_8408.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8407
        | FStar_Parser_AST.Name lid when
            let uu____8422 = FStar_Ident.string_of_lid lid  in
            uu____8422 = "Type0" ->
            let uu____8426 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8426, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8428 = FStar_Ident.string_of_lid lid  in
            uu____8428 = "Type" ->
            let uu____8432 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8432, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8449 = FStar_Ident.string_of_lid lid  in
            uu____8449 = "Type" ->
            let uu____8453 =
              let uu____8454 =
                let uu____8455 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8455  in
              mk uu____8454  in
            (uu____8453, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8457 = FStar_Ident.string_of_lid lid  in
            uu____8457 = "Effect" ->
            let uu____8461 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8461, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8463 = FStar_Ident.string_of_lid lid  in
            uu____8463 = "True" ->
            let uu____8467 =
              let uu____8468 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8468
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8467, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8470 = FStar_Ident.string_of_lid lid  in
            uu____8470 = "False" ->
            let uu____8474 =
              let uu____8475 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8475
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8474, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8480 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8480) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8484 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8484 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8493 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8493, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8495 =
                   let uu____8497 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8497 txt
                    in
                 failwith uu____8495)
        | FStar_Parser_AST.Var l ->
            let uu____8505 = desugar_name mk setpos env true l  in
            (uu____8505, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8513 = desugar_name mk setpos env true l  in
            (uu____8513, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8530 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8530 with
              | FStar_Pervasives_Native.Some uu____8540 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8548 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8548 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8566 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8587 =
                   let uu____8588 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8588  in
                 (uu____8587, noaqs)
             | uu____8594 ->
                 let uu____8602 =
                   let uu____8608 =
                     let uu____8610 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8610
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8608)  in
                 FStar_Errors.raise_error uu____8602
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8619 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8619 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8626 =
                   let uu____8632 =
                     let uu____8634 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8634
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8632)
                    in
                 FStar_Errors.raise_error uu____8626
                   top.FStar_Parser_AST.range
             | uu____8642 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8646 = desugar_name mk setpos env true lid'  in
                 (uu____8646, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8667 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8667 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8686 ->
                      let uu____8693 =
                        FStar_Util.take
                          (fun uu____8717  ->
                             match uu____8717 with
                             | (uu____8723,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8693 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8768 =
                             let uu____8793 =
                               FStar_List.map
                                 (fun uu____8836  ->
                                    match uu____8836 with
                                    | (t,imp) ->
                                        let uu____8853 =
                                          desugar_term_aq env t  in
                                        (match uu____8853 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8793 FStar_List.unzip
                              in
                           (match uu____8768 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____8996 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____8996, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9015 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9015 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9023 =
                         let uu____9025 =
                           let uu____9027 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9027 " not found"  in
                         Prims.op_Hat "Constructor " uu____9025  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9023)
                   | FStar_Pervasives_Native.Some uu____9032 ->
                       let uu____9033 =
                         let uu____9035 =
                           let uu____9037 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9037
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9035  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9033)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9066  ->
                 match uu___8_9066 with
                 | FStar_Util.Inr uu____9072 -> true
                 | uu____9074 -> false) binders
            ->
            let terms =
              let uu____9083 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9100  ->
                        match uu___9_9100 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9106 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9083 [t]  in
            let uu____9108 =
              let uu____9133 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9190 = desugar_typ_aq env t1  in
                        match uu____9190 with
                        | (t',aq) ->
                            let uu____9201 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9201, aq)))
                 in
              FStar_All.pipe_right uu____9133 FStar_List.unzip  in
            (match uu____9108 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9311 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9311
                    in
                 let uu____9320 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9320, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9347 =
              let uu____9364 =
                let uu____9371 =
                  let uu____9378 =
                    FStar_All.pipe_left
                      (fun uu____9387  -> FStar_Util.Inl uu____9387)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9378]  in
                FStar_List.append binders uu____9371  in
              FStar_List.fold_left
                (fun uu____9432  ->
                   fun b  ->
                     match uu____9432 with
                     | (env1,tparams,typs) ->
                         let uu____9493 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9508 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9508)
                            in
                         (match uu____9493 with
                          | (xopt,t1) ->
                              let uu____9533 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9542 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9542)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9533 with
                               | (env2,x) ->
                                   let uu____9562 =
                                     let uu____9565 =
                                       let uu____9568 =
                                         let uu____9569 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9569
                                          in
                                       [uu____9568]  in
                                     FStar_List.append typs uu____9565  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1496_9595 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1496_9595.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1496_9595.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9562)))) (env, [], []) uu____9364
               in
            (match uu____9347 with
             | (env1,uu____9623,targs) ->
                 let tup =
                   let uu____9646 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9646
                    in
                 let uu____9647 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9647, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9666 = uncurry binders t  in
            (match uu____9666 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9710 =
                   match uu___10_9710 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9727 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9727
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9751 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9751 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9784 = aux env [] bs  in (uu____9784, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9793 = desugar_binder env b  in
            (match uu____9793 with
             | (FStar_Pervasives_Native.None ,uu____9804) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9819 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9819 with
                  | ((x,uu____9835),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9848 =
                        let uu____9849 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9849  in
                      (uu____9848, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____9927 = FStar_Util.set_is_empty i  in
                    if uu____9927
                    then
                      let uu____9932 = FStar_Util.set_union acc set  in
                      aux uu____9932 sets2
                    else
                      (let uu____9937 =
                         let uu____9938 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9938  in
                       FStar_Pervasives_Native.Some uu____9937)
                 in
              let uu____9941 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9941 sets  in
            ((let uu____9945 = check_disjoint bvss  in
              match uu____9945 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____9949 =
                    let uu____9955 =
                      let uu____9957 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____9957
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9955)
                     in
                  let uu____9961 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____9949 uu____9961);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9969 =
                FStar_List.fold_left
                  (fun uu____9989  ->
                     fun pat  ->
                       match uu____9989 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10015,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10025 =
                                  let uu____10028 = free_type_vars env1 t  in
                                  FStar_List.append uu____10028 ftvs  in
                                (env1, uu____10025)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10033,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10044 =
                                  let uu____10047 = free_type_vars env1 t  in
                                  let uu____10050 =
                                    let uu____10053 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10053 ftvs  in
                                  FStar_List.append uu____10047 uu____10050
                                   in
                                (env1, uu____10044)
                            | uu____10058 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____9969 with
              | (uu____10067,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10079 =
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
                    FStar_List.append uu____10079 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10159 = desugar_term_aq env1 body  in
                        (match uu____10159 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10194 =
                                       let uu____10195 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10195
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10194
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
                             let uu____10264 =
                               let uu____10265 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10265  in
                             (uu____10264, aq))
                    | p::rest ->
                        let uu____10278 = desugar_binding_pat env1 p  in
                        (match uu____10278 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10310)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10325 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10334 =
                               match b with
                               | LetBinder uu____10375 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10444) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10498 =
                                           let uu____10507 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10507, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10498
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10569,uu____10570) ->
                                              let tup2 =
                                                let uu____10572 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10572
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10577 =
                                                  let uu____10584 =
                                                    let uu____10585 =
                                                      let uu____10602 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10605 =
                                                        let uu____10616 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10625 =
                                                          let uu____10636 =
                                                            let uu____10645 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10645
                                                             in
                                                          [uu____10636]  in
                                                        uu____10616 ::
                                                          uu____10625
                                                         in
                                                      (uu____10602,
                                                        uu____10605)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10585
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10584
                                                   in
                                                uu____10577
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10693 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10693
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10744,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10746,pats1)) ->
                                              let tupn =
                                                let uu____10791 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10791
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10804 =
                                                  let uu____10805 =
                                                    let uu____10822 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10825 =
                                                      let uu____10836 =
                                                        let uu____10847 =
                                                          let uu____10856 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10856
                                                           in
                                                        [uu____10847]  in
                                                      FStar_List.append args
                                                        uu____10836
                                                       in
                                                    (uu____10822,
                                                      uu____10825)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10805
                                                   in
                                                mk uu____10804  in
                                              let p2 =
                                                let uu____10904 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10904
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10951 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10334 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11043,uu____11044,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11066 =
                let uu____11067 = unparen e  in
                uu____11067.FStar_Parser_AST.tm  in
              match uu____11066 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11077 ->
                  let uu____11078 = desugar_term_aq env e  in
                  (match uu____11078 with
                   | (head,aq) ->
                       let uu____11091 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11091, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11098 ->
            let rec aux args aqs e =
              let uu____11175 =
                let uu____11176 = unparen e  in
                uu____11176.FStar_Parser_AST.tm  in
              match uu____11175 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11194 = desugar_term_aq env t  in
                  (match uu____11194 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11242 ->
                  let uu____11243 = desugar_term_aq env e  in
                  (match uu____11243 with
                   | (head,aq) ->
                       let uu____11264 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11264, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11317 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11317
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11324 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11324  in
            let bind =
              let uu____11329 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11329 FStar_Parser_AST.Expr
               in
            let uu____11330 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11330
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
            let uu____11382 = desugar_term_aq env t  in
            (match uu____11382 with
             | (tm,s) ->
                 let uu____11393 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11393, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11399 =
              let uu____11412 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11412 then desugar_typ_aq else desugar_term_aq  in
            uu____11399 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11479 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11622  ->
                        match uu____11622 with
                        | (attr_opt,(p,def)) ->
                            let uu____11680 = is_app_pattern p  in
                            if uu____11680
                            then
                              let uu____11713 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11713, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11796 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11796, def1)
                               | uu____11841 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11879);
                                           FStar_Parser_AST.prange =
                                             uu____11880;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11929 =
                                            let uu____11950 =
                                              let uu____11955 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____11955  in
                                            (uu____11950, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11929, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12047) ->
                                        if top_level
                                        then
                                          let uu____12083 =
                                            let uu____12104 =
                                              let uu____12109 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12109  in
                                            (uu____12104, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12083, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12200 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12233 =
                FStar_List.fold_left
                  (fun uu____12322  ->
                     fun uu____12323  ->
                       match (uu____12322, uu____12323) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12453,uu____12454),uu____12455))
                           ->
                           let uu____12589 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12629 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12629 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12664 =
                                        let uu____12667 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12667 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12664, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12683 =
                                   let uu____12691 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12691
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12683 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12589 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12233 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12937 =
                    match uu____12937 with
                    | (attrs_opt,(uu____12977,args,result_t),def) ->
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
                                let uu____13069 = is_comp_type env1 t  in
                                if uu____13069
                                then
                                  ((let uu____13073 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13083 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13083))
                                       in
                                    match uu____13073 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13090 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13093 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13093))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13090
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
                          | uu____13104 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13107 = desugar_term_aq env1 def2  in
                        (match uu____13107 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13129 =
                                     let uu____13130 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13130
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13129
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
                  let uu____13171 =
                    let uu____13188 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13188 FStar_List.unzip  in
                  (match uu____13171 with
                   | (lbs1,aqss) ->
                       let uu____13330 = desugar_term_aq env' body  in
                       (match uu____13330 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13436  ->
                                    fun used_marker  ->
                                      match uu____13436 with
                                      | (_attr_opt,(f,uu____13510,uu____13511),uu____13512)
                                          ->
                                          let uu____13569 =
                                            let uu____13571 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13571  in
                                          if uu____13569
                                          then
                                            let uu____13595 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13613 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13615 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13613, "Local",
                                                    uu____13615)
                                              | FStar_Util.Inr l ->
                                                  let uu____13620 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13622 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13620, "Global",
                                                    uu____13622)
                                               in
                                            (match uu____13595 with
                                             | (nm,gl,rng) ->
                                                 let uu____13633 =
                                                   let uu____13639 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13639)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13633)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13647 =
                                let uu____13650 =
                                  let uu____13651 =
                                    let uu____13665 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13665)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13651  in
                                FStar_All.pipe_left mk uu____13650  in
                              (uu____13647,
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
              let uu____13767 = desugar_term_aq env t1  in
              match uu____13767 with
              | (t11,aq0) ->
                  let uu____13788 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13788 with
                   | (env1,binder,pat1) ->
                       let uu____13818 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13860 = desugar_term_aq env1 t2  in
                             (match uu____13860 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13882 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13882
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13883 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13883, aq))
                         | LocalBinder (x,uu____13924) ->
                             let uu____13925 = desugar_term_aq env1 t2  in
                             (match uu____13925 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13947;
                                         FStar_Syntax_Syntax.p = uu____13948;_},uu____13949)::[]
                                        -> body1
                                    | uu____13962 ->
                                        let uu____13965 =
                                          let uu____13972 =
                                            let uu____13973 =
                                              let uu____13996 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____13999 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____13996, uu____13999)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____13973
                                             in
                                          FStar_Syntax_Syntax.mk uu____13972
                                           in
                                        uu____13965
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14036 =
                                    let uu____14039 =
                                      let uu____14040 =
                                        let uu____14054 =
                                          let uu____14057 =
                                            let uu____14058 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14058]  in
                                          FStar_Syntax_Subst.close
                                            uu____14057 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14054)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14040
                                       in
                                    FStar_All.pipe_left mk uu____14039  in
                                  (uu____14036, aq))
                          in
                       (match uu____13818 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14166 = FStar_List.hd lbs  in
            (match uu____14166 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14210 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14210
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool =
              let uu____14226 =
                let uu____14227 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14227  in
              mk uu____14226  in
            let uu____14228 = desugar_term_aq env t1  in
            (match uu____14228 with
             | (t1',aq1) ->
                 let uu____14239 = desugar_term_aq env t2  in
                 (match uu____14239 with
                  | (t2',aq2) ->
                      let uu____14250 = desugar_term_aq env t3  in
                      (match uu____14250 with
                       | (t3',aq3) ->
                           let uu____14261 =
                             let uu____14262 =
                               let uu____14263 =
                                 let uu____14286 =
                                   let uu____14303 =
                                     let uu____14318 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14318,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14332 =
                                     let uu____14349 =
                                       let uu____14364 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14364,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14349]  in
                                   uu____14303 :: uu____14332  in
                                 (t1', uu____14286)  in
                               FStar_Syntax_Syntax.Tm_match uu____14263  in
                             mk uu____14262  in
                           (uu____14261, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14560 =
              match uu____14560 with
              | (pat,wopt,b) ->
                  let uu____14582 = desugar_match_pat env pat  in
                  (match uu____14582 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14613 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14613
                          in
                       let uu____14618 = desugar_term_aq env1 b  in
                       (match uu____14618 with
                        | (b1,aq) ->
                            let uu____14631 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14631, aq)))
               in
            let uu____14636 = desugar_term_aq env e  in
            (match uu____14636 with
             | (e1,aq) ->
                 let uu____14647 =
                   let uu____14678 =
                     let uu____14711 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14711 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14678
                     (fun uu____14929  ->
                        match uu____14929 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14647 with
                  | (brs,aqs) ->
                      let uu____15148 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15148, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15182 =
              let uu____15203 = is_comp_type env t  in
              if uu____15203
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15258 = desugar_term_aq env t  in
                 match uu____15258 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15182 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15350 = desugar_term_aq env e  in
                 (match uu____15350 with
                  | (e1,aq) ->
                      let uu____15361 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15361, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15400,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15443 = FStar_List.hd fields  in
              match uu____15443 with
              | (f,uu____15455) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15503  ->
                        match uu____15503 with
                        | (g,uu____15510) ->
                            let uu____15511 = FStar_Ident.text_of_id f  in
                            let uu____15513 =
                              let uu____15515 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15515  in
                            uu____15511 = uu____15513))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15522,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15536 =
                         let uu____15542 =
                           let uu____15544 = FStar_Ident.text_of_id f  in
                           let uu____15546 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15544 uu____15546
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15542)
                          in
                       FStar_Errors.raise_error uu____15536
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
                  let uu____15557 =
                    let uu____15568 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15599  ->
                              match uu____15599 with
                              | (f,uu____15609) ->
                                  let uu____15610 =
                                    let uu____15611 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15611
                                     in
                                  (uu____15610, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15568)  in
                  FStar_Parser_AST.Construct uu____15557
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15629 =
                      let uu____15630 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15630  in
                    let uu____15631 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15629 uu____15631
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15633 =
                      let uu____15646 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15676  ->
                                match uu____15676 with
                                | (f,uu____15686) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15646)  in
                    FStar_Parser_AST.Record uu____15633  in
                  let uu____15695 =
                    let uu____15716 =
                      let uu____15731 =
                        let uu____15744 =
                          let uu____15749 =
                            let uu____15750 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15750
                             in
                          (uu____15749, e)  in
                        (FStar_Pervasives_Native.None, uu____15744)  in
                      [uu____15731]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15716,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15695
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15802 = desugar_term_aq env recterm1  in
            (match uu____15802 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15818;
                         FStar_Syntax_Syntax.vars = uu____15819;_},args)
                      ->
                      let uu____15845 =
                        let uu____15846 =
                          let uu____15847 =
                            let uu____15864 =
                              let uu____15867 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15868 =
                                let uu____15871 =
                                  let uu____15872 =
                                    let uu____15879 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15879)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15872
                                   in
                                FStar_Pervasives_Native.Some uu____15871  in
                              FStar_Syntax_Syntax.fvar uu____15867
                                FStar_Syntax_Syntax.delta_constant
                                uu____15868
                               in
                            (uu____15864, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15847  in
                        FStar_All.pipe_left mk uu____15846  in
                      (uu____15845, s)
                  | uu____15908 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____15911 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____15911 with
             | (constrname,is_rec) ->
                 let uu____15930 = desugar_term_aq env e  in
                 (match uu____15930 with
                  | (e1,s) ->
                      let projname =
                        let uu____15942 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____15942
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____15949 =
                            let uu____15950 =
                              let uu____15955 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____15955)  in
                            FStar_Syntax_Syntax.Record_projector uu____15950
                             in
                          FStar_Pervasives_Native.Some uu____15949
                        else FStar_Pervasives_Native.None  in
                      let uu____15958 =
                        let uu____15959 =
                          let uu____15960 =
                            let uu____15977 =
                              let uu____15980 =
                                let uu____15981 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____15981
                                 in
                              FStar_Syntax_Syntax.fvar uu____15980
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____15983 =
                              let uu____15994 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____15994]  in
                            (uu____15977, uu____15983)  in
                          FStar_Syntax_Syntax.Tm_app uu____15960  in
                        FStar_All.pipe_left mk uu____15959  in
                      (uu____15958, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16034 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16034
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16045 =
              let uu____16046 = FStar_Syntax_Subst.compress tm  in
              uu____16046.FStar_Syntax_Syntax.n  in
            (match uu____16045 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16054 =
                   let uu___2064_16055 =
                     let uu____16056 =
                       let uu____16058 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16058  in
                     FStar_Syntax_Util.exp_string uu____16056  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2064_16055.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2064_16055.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16054, noaqs)
             | uu____16059 ->
                 let uu____16060 =
                   let uu____16066 =
                     let uu____16068 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16068
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16066)  in
                 FStar_Errors.raise_error uu____16060
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16077 = desugar_term_aq env e  in
            (match uu____16077 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16089 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16089, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16094 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16095 =
              let uu____16096 =
                let uu____16103 = desugar_term env e  in (bv, uu____16103)
                 in
              [uu____16096]  in
            (uu____16094, uu____16095)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16128 =
              let uu____16129 =
                let uu____16130 =
                  let uu____16137 = desugar_term env e  in (uu____16137, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16130  in
              FStar_All.pipe_left mk uu____16129  in
            (uu____16128, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16166 -> false  in
              let uu____16168 =
                let uu____16169 = unparen rel1  in
                uu____16169.FStar_Parser_AST.tm  in
              match uu____16168 with
              | FStar_Parser_AST.Op (id,uu____16172) ->
                  let uu____16177 = op_as_term env (Prims.of_int (2)) id  in
                  (match uu____16177 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16185 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16185 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16196 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16196 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16202 -> false  in
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
              let uu____16223 =
                let uu____16224 =
                  let uu____16231 =
                    let uu____16232 =
                      let uu____16233 =
                        let uu____16242 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16255 =
                          let uu____16256 =
                            let uu____16257 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16257  in
                          FStar_Parser_AST.mk_term uu____16256
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16242, uu____16255,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16233  in
                    FStar_Parser_AST.mk_term uu____16232
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16231)  in
                FStar_Parser_AST.Abs uu____16224  in
              FStar_Parser_AST.mk_term uu____16223
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
              let uu____16278 = FStar_List.last steps  in
              match uu____16278 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16281,uu____16282,last_expr)) -> last_expr
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
            let uu____16308 =
              FStar_List.fold_left
                (fun uu____16326  ->
                   fun uu____16327  ->
                     match (uu____16326, uu____16327) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16350 = is_impl rel2  in
                           if uu____16350
                           then
                             let uu____16353 =
                               let uu____16360 =
                                 let uu____16365 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16365, FStar_Parser_AST.Nothing)  in
                               [uu____16360]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16353 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16377 =
                             let uu____16384 =
                               let uu____16391 =
                                 let uu____16398 =
                                   let uu____16405 =
                                     let uu____16410 = eta_and_annot rel2  in
                                     (uu____16410, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16411 =
                                     let uu____16418 =
                                       let uu____16425 =
                                         let uu____16430 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16430,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16431 =
                                         let uu____16438 =
                                           let uu____16443 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16443,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16438]  in
                                       uu____16425 :: uu____16431  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16418
                                      in
                                   uu____16405 :: uu____16411  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16398
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16391
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16384
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16377
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16308 with
             | (e1,uu____16481) ->
                 let e2 =
                   let uu____16483 =
                     let uu____16490 =
                       let uu____16497 =
                         let uu____16504 =
                           let uu____16509 = FStar_Parser_AST.thunk e1  in
                           (uu____16509, FStar_Parser_AST.Nothing)  in
                         [uu____16504]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16497  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16490  in
                   FStar_Parser_AST.mkApp finish uu____16483
                     top.FStar_Parser_AST.range
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16526 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16527 = desugar_formula env top  in
            (uu____16527, noaqs)
        | uu____16528 ->
            let uu____16529 =
              let uu____16535 =
                let uu____16537 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16537  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16535)  in
            FStar_Errors.raise_error uu____16529 top.FStar_Parser_AST.range

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
           (fun uu____16581  ->
              match uu____16581 with
              | (a,imp) ->
                  let uu____16594 = desugar_term env a  in
                  arg_withimp_e imp uu____16594))

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
          let is_requires uu____16631 =
            match uu____16631 with
            | (t1,uu____16638) ->
                let uu____16639 =
                  let uu____16640 = unparen t1  in
                  uu____16640.FStar_Parser_AST.tm  in
                (match uu____16639 with
                 | FStar_Parser_AST.Requires uu____16642 -> true
                 | uu____16651 -> false)
             in
          let is_ensures uu____16663 =
            match uu____16663 with
            | (t1,uu____16670) ->
                let uu____16671 =
                  let uu____16672 = unparen t1  in
                  uu____16672.FStar_Parser_AST.tm  in
                (match uu____16671 with
                 | FStar_Parser_AST.Ensures uu____16674 -> true
                 | uu____16683 -> false)
             in
          let is_app head uu____16701 =
            match uu____16701 with
            | (t1,uu____16709) ->
                let uu____16710 =
                  let uu____16711 = unparen t1  in
                  uu____16711.FStar_Parser_AST.tm  in
                (match uu____16710 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16714;
                        FStar_Parser_AST.level = uu____16715;_},uu____16716,uu____16717)
                     ->
                     let uu____16718 =
                       let uu____16720 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16720  in
                     uu____16718 = head
                 | uu____16722 -> false)
             in
          let is_smt_pat uu____16734 =
            match uu____16734 with
            | (t1,uu____16741) ->
                let uu____16742 =
                  let uu____16743 = unparen t1  in
                  uu____16743.FStar_Parser_AST.tm  in
                (match uu____16742 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16747);
                              FStar_Parser_AST.range = uu____16748;
                              FStar_Parser_AST.level = uu____16749;_},uu____16750)::uu____16751::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16791 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16791 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16803;
                              FStar_Parser_AST.level = uu____16804;_},uu____16805)::uu____16806::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16834 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16834 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16842 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16877 = head_and_args t1  in
            match uu____16877 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____16935 =
                       let uu____16937 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____16937  in
                     uu____16935 = "Lemma" ->
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
                     let thunk_ens uu____16973 =
                       match uu____16973 with
                       | (e,i) ->
                           let uu____16984 = FStar_Parser_AST.thunk e  in
                           (uu____16984, i)
                        in
                     let fail_lemma uu____16996 =
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
                           let uu____17102 =
                             let uu____17109 =
                               let uu____17116 = thunk_ens ens  in
                               [uu____17116; nil_pat]  in
                             req_true :: uu____17109  in
                           unit_tm :: uu____17102
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17163 =
                             let uu____17170 =
                               let uu____17177 = thunk_ens ens  in
                               [uu____17177; nil_pat]  in
                             req :: uu____17170  in
                           unit_tm :: uu____17163
                       | ens::smtpat::[] when
                           (((let uu____17226 = is_requires ens  in
                              Prims.op_Negation uu____17226) &&
                               (let uu____17229 = is_smt_pat ens  in
                                Prims.op_Negation uu____17229))
                              &&
                              (let uu____17232 = is_decreases ens  in
                               Prims.op_Negation uu____17232))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17234 =
                             let uu____17241 =
                               let uu____17248 = thunk_ens ens  in
                               [uu____17248; smtpat]  in
                             req_true :: uu____17241  in
                           unit_tm :: uu____17234
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17295 =
                             let uu____17302 =
                               let uu____17309 = thunk_ens ens  in
                               [uu____17309; nil_pat; dec]  in
                             req_true :: uu____17302  in
                           unit_tm :: uu____17295
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17369 =
                             let uu____17376 =
                               let uu____17383 = thunk_ens ens  in
                               [uu____17383; smtpat; dec]  in
                             req_true :: uu____17376  in
                           unit_tm :: uu____17369
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17443 =
                             let uu____17450 =
                               let uu____17457 = thunk_ens ens  in
                               [uu____17457; nil_pat; dec]  in
                             req :: uu____17450  in
                           unit_tm :: uu____17443
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17517 =
                             let uu____17524 =
                               let uu____17531 = thunk_ens ens  in
                               [uu____17531; smtpat]  in
                             req :: uu____17524  in
                           unit_tm :: uu____17517
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17596 =
                             let uu____17603 =
                               let uu____17610 = thunk_ens ens  in
                               [uu____17610; dec; smtpat]  in
                             req :: uu____17603  in
                           unit_tm :: uu____17596
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17672 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17672, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17700 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17700
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17702 =
                          let uu____17704 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17704  in
                        uu____17702 = "Tot")
                     ->
                     let uu____17707 =
                       let uu____17714 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17714, [])  in
                     (uu____17707, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17732 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17732
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17734 =
                          let uu____17736 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17736  in
                        uu____17734 = "GTot")
                     ->
                     let uu____17739 =
                       let uu____17746 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17746, [])  in
                     (uu____17739, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17764 =
                         let uu____17766 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17766  in
                       uu____17764 = "Type") ||
                        (let uu____17770 =
                           let uu____17772 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17772  in
                         uu____17770 = "Type0"))
                       ||
                       (let uu____17776 =
                          let uu____17778 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17778  in
                        uu____17776 = "Effect")
                     ->
                     let uu____17781 =
                       let uu____17788 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17788, [])  in
                     (uu____17781, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17811 when allow_type_promotion ->
                     let default_effect =
                       let uu____17813 = FStar_Options.ml_ish ()  in
                       if uu____17813
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17819 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17819
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17826 =
                       let uu____17833 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17833, [])  in
                     (uu____17826, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17856 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17875 = pre_process_comp_typ t  in
          match uu____17875 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17927 =
                    let uu____17933 =
                      let uu____17935 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17935
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17933)
                     in
                  fail uu____17927)
               else ();
               (let is_universe uu____17951 =
                  match uu____17951 with
                  | (uu____17957,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17959 = FStar_Util.take is_universe args  in
                match uu____17959 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18018  ->
                           match uu____18018 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18025 =
                      let uu____18040 = FStar_List.hd args1  in
                      let uu____18049 = FStar_List.tl args1  in
                      (uu____18040, uu____18049)  in
                    (match uu____18025 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18104 =
                           let is_decrease uu____18143 =
                             match uu____18143 with
                             | (t1,uu____18154) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18165;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18166;_},uu____18167::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18206 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18104 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18323  ->
                                        match uu____18323 with
                                        | (t1,uu____18333) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18342,(arg,uu____18344)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18383 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18404 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18416 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18416
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18423 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18423
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18433 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18433
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18440 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18440
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18447 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18447
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18454 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18454
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18475 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18475
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
                                                    let uu____18566 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18566
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
                                              | uu____18587 -> pat  in
                                            let uu____18588 =
                                              let uu____18599 =
                                                let uu____18610 =
                                                  let uu____18619 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18619, aq)  in
                                                [uu____18610]  in
                                              ens :: uu____18599  in
                                            req :: uu____18588
                                        | uu____18660 -> rest2
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
        let uu___2389_18695 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2389_18695.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2389_18695.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2396_18749 = b  in
             {
               FStar_Parser_AST.b = (uu___2396_18749.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2396_18749.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2396_18749.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18778 body1 =
          match uu____18778 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18824::uu____18825) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18843 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2415_18871 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18872 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2415_18871.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18872;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2415_18871.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18935 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18935))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18966 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18966 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2428_18976 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2428_18976.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2428_18976.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18982 =
                     let uu____18985 =
                       let uu____18986 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18986]  in
                     no_annot_abs uu____18985 body2  in
                   FStar_All.pipe_left setpos uu____18982  in
                 let uu____19007 =
                   let uu____19008 =
                     let uu____19025 =
                       let uu____19028 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19028
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19030 =
                       let uu____19041 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19041]  in
                     (uu____19025, uu____19030)  in
                   FStar_Syntax_Syntax.Tm_app uu____19008  in
                 FStar_All.pipe_left mk uu____19007)
        | uu____19080 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19145 = q (rest, pats, body)  in
              let uu____19148 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19145 uu____19148
                FStar_Parser_AST.Formula
               in
            let uu____19149 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19149 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19160 -> failwith "impossible"  in
      let uu____19164 =
        let uu____19165 = unparen f  in uu____19165.FStar_Parser_AST.tm  in
      match uu____19164 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19178,uu____19179) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19203,uu____19204) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19260 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19260
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19304 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19304
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19368 -> desugar_term env f

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
          let uu____19379 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19379)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19384 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19384)
      | FStar_Parser_AST.TVariable x ->
          let uu____19388 =
            let uu____19389 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19389
             in
          ((FStar_Pervasives_Native.Some x), uu____19388)
      | FStar_Parser_AST.NoName t ->
          let uu____19393 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19393)
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
      fun uu___11_19401  ->
        match uu___11_19401 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19423 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19423, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19440 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19440 with
             | (env1,a1) ->
                 let uu____19457 =
                   let uu____19464 = trans_aqual env1 imp  in
                   ((let uu___2528_19470 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2528_19470.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2528_19470.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19464)
                    in
                 (uu____19457, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19478  ->
      match uu___12_19478 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19482 =
            let uu____19483 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19483  in
          FStar_Pervasives_Native.Some uu____19482
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19511 =
        FStar_List.fold_left
          (fun uu____19544  ->
             fun b  ->
               match uu____19544 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2546_19588 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2546_19588.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2546_19588.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2546_19588.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19603 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19603 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2556_19621 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2556_19621.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2556_19621.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19622 =
                               let uu____19629 =
                                 let uu____19634 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19634)  in
                               uu____19629 :: out  in
                             (env2, uu____19622))
                    | uu____19645 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19511 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19733 =
          let uu____19734 = unparen t  in uu____19734.FStar_Parser_AST.tm  in
        match uu____19733 with
        | FStar_Parser_AST.Var lid when
            let uu____19736 = FStar_Ident.string_of_lid lid  in
            uu____19736 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19740 ->
            let uu____19741 =
              let uu____19747 =
                let uu____19749 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19749  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19747)  in
            FStar_Errors.raise_error uu____19741 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19766) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19768) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19771 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19789 = binder_ident b  in
         FStar_Common.list_of_option uu____19789) bs
  
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
               (fun uu___13_19826  ->
                  match uu___13_19826 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19831 -> false))
           in
        let quals2 q =
          let uu____19845 =
            (let uu____19849 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19849) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19845
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19866 = FStar_Ident.range_of_lid disc_name  in
                let uu____19867 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19866;
                  FStar_Syntax_Syntax.sigquals = uu____19867;
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
            let uu____19907 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19943  ->
                        match uu____19943 with
                        | (x,uu____19954) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____19964 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____19964)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____19966 =
                                   let uu____19968 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____19968  in
                                 FStar_Options.dont_gen_projectors
                                   uu____19966)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____19986 =
                                  FStar_List.filter
                                    (fun uu___14_19990  ->
                                       match uu___14_19990 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____19993 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____19986
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20008  ->
                                        match uu___15_20008 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20013 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20016 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20016;
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
                                 let uu____20023 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20023
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20034 =
                                   let uu____20039 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20039  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20034;
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
                                 let uu____20043 =
                                   let uu____20044 =
                                     let uu____20051 =
                                       let uu____20054 =
                                         let uu____20055 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20055
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20054]  in
                                     ((false, [lb]), uu____20051)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20044
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20043;
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
            FStar_All.pipe_right uu____19907 FStar_List.flatten
  
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
            (lid,uu____20104,t,uu____20106,n,uu____20108) when
            let uu____20115 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20115 ->
            let uu____20117 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20117 with
             | (formals,uu____20127) ->
                 (match formals with
                  | [] -> []
                  | uu____20140 ->
                      let filter_records uu___16_20148 =
                        match uu___16_20148 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20151,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20163 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20165 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20165 with
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
                      let uu____20177 = FStar_Util.first_N n formals  in
                      (match uu____20177 with
                       | (uu____20206,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20240 -> []
  
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
                        let uu____20334 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20334
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20358 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20358
                        then
                          let uu____20364 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20364
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20368 =
                          let uu____20373 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20373  in
                        let uu____20374 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20380 =
                              let uu____20383 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20383  in
                            FStar_Syntax_Util.arrow typars uu____20380
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20388 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20368;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20374;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20388;
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
          let tycon_id uu___17_20442 =
            match uu___17_20442 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20444,uu____20445) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20455,uu____20456,uu____20457) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20467,uu____20468,uu____20469) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20491,uu____20492,uu____20493) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20531) ->
                let uu____20532 =
                  let uu____20533 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20533  in
                let uu____20534 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20532 uu____20534
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20536 =
                  let uu____20537 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20537  in
                let uu____20538 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20536 uu____20538
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20540) ->
                let uu____20541 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20541 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20543 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20543 FStar_Parser_AST.Type_level
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
              | uu____20573 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20581 =
                     let uu____20582 =
                       let uu____20589 = binder_to_term b  in
                       (out, uu____20589, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20582  in
                   FStar_Parser_AST.mk_term uu____20581
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20601 =
            match uu___18_20601 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20633 =
                    let uu____20639 =
                      let uu____20641 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20641  in
                    let uu____20644 = FStar_Ident.range_of_id id  in
                    (uu____20639, uu____20644)  in
                  FStar_Ident.mk_ident uu____20633  in
                let mfields =
                  FStar_List.map
                    (fun uu____20657  ->
                       match uu____20657 with
                       | (x,t) ->
                           let uu____20664 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20664
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20666 =
                    let uu____20667 =
                      let uu____20668 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20668  in
                    let uu____20669 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20667 uu____20669
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20666 parms  in
                let constrTyp =
                  let uu____20671 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20671 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20677 = binder_idents parms  in id :: uu____20677
                   in
                (FStar_List.iter
                   (fun uu____20691  ->
                      match uu____20691 with
                      | (f,uu____20697) ->
                          let uu____20698 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20698
                          then
                            let uu____20703 =
                              let uu____20709 =
                                let uu____20711 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20711
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20709)
                               in
                            let uu____20715 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20703 uu____20715
                          else ()) fields;
                 (let uu____20718 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20718)))
            | uu____20772 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20812 =
            match uu___19_20812 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20836 = typars_of_binders _env binders  in
                (match uu____20836 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20872 =
                         let uu____20873 =
                           let uu____20874 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20874  in
                         let uu____20875 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20873 uu____20875
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20872 binders  in
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
                     let uu____20884 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20884 with
                      | (_env1,uu____20901) ->
                          let uu____20908 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20908 with
                           | (_env2,uu____20925) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20932 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20975 =
              FStar_List.fold_left
                (fun uu____21009  ->
                   fun uu____21010  ->
                     match (uu____21009, uu____21010) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21079 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21079 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20975 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21170 =
                      let uu____21171 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21171  in
                    FStar_Pervasives_Native.Some uu____21170
                | uu____21172 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21180 = desugar_abstract_tc quals env [] tc  in
              (match uu____21180 with
               | (uu____21193,uu____21194,se,uu____21196) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21199,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21218 =
                                 let uu____21220 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21220  in
                               if uu____21218
                               then
                                 let uu____21223 =
                                   let uu____21229 =
                                     let uu____21231 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21231
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21229)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21223
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
                           | uu____21244 ->
                               let uu____21245 =
                                 let uu____21252 =
                                   let uu____21253 =
                                     let uu____21268 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21268)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21253
                                    in
                                 FStar_Syntax_Syntax.mk uu____21252  in
                               uu____21245 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2833_21281 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2833_21281.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2833_21281.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2833_21281.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2833_21281.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21282 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21297 = typars_of_binders env binders  in
              (match uu____21297 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21331 =
                           FStar_Util.for_some
                             (fun uu___20_21334  ->
                                match uu___20_21334 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21337 -> false) quals
                            in
                         if uu____21331
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21345 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21345
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21350 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21356  ->
                               match uu___21_21356 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21359 -> false))
                        in
                     if uu____21350
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21373 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21373
                     then
                       let uu____21379 =
                         let uu____21386 =
                           let uu____21387 = unparen t  in
                           uu____21387.FStar_Parser_AST.tm  in
                         match uu____21386 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21408 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21438)::args_rev ->
                                   let uu____21450 =
                                     let uu____21451 = unparen last_arg  in
                                     uu____21451.FStar_Parser_AST.tm  in
                                   (match uu____21450 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21479 -> ([], args))
                               | uu____21488 -> ([], args)  in
                             (match uu____21408 with
                              | (cattributes,args1) ->
                                  let uu____21527 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21527))
                         | uu____21538 -> (t, [])  in
                       match uu____21379 with
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
                                  (fun uu___22_21561  ->
                                     match uu___22_21561 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21564 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21572)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21592 = tycon_record_as_variant trec  in
              (match uu____21592 with
               | (t,fs) ->
                   let uu____21609 =
                     let uu____21612 =
                       let uu____21613 =
                         let uu____21622 =
                           let uu____21625 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21625  in
                         (uu____21622, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21613  in
                     uu____21612 :: quals  in
                   desugar_tycon env d uu____21609 [t])
          | uu____21630::uu____21631 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21789 = et  in
                match uu____21789 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21999 ->
                         let trec = tc  in
                         let uu____22019 = tycon_record_as_variant trec  in
                         (match uu____22019 with
                          | (t,fs) ->
                              let uu____22075 =
                                let uu____22078 =
                                  let uu____22079 =
                                    let uu____22088 =
                                      let uu____22091 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22091  in
                                    (uu____22088, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22079
                                   in
                                uu____22078 :: quals1  in
                              collect_tcs uu____22075 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22169 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22169 with
                          | (env2,uu____22226,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22363 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22363 with
                          | (env2,uu____22420,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22536 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22582 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22582 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23034  ->
                             match uu___24_23034 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23088,uu____23089);
                                    FStar_Syntax_Syntax.sigrng = uu____23090;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23091;
                                    FStar_Syntax_Syntax.sigmeta = uu____23092;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23093;
                                    FStar_Syntax_Syntax.sigopts = uu____23094;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23156 =
                                     typars_of_binders env1 binders  in
                                   match uu____23156 with
                                   | (env2,tpars1) ->
                                       let uu____23183 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23183 with
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
                                 let uu____23212 =
                                   let uu____23223 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23223)  in
                                 [uu____23212]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23259);
                                    FStar_Syntax_Syntax.sigrng = uu____23260;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23262;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23263;
                                    FStar_Syntax_Syntax.sigopts = uu____23264;_},constrs,tconstr,quals1)
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
                                 let uu____23355 = push_tparams env1 tpars
                                    in
                                 (match uu____23355 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23414  ->
                                             match uu____23414 with
                                             | (x,uu____23426) ->
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
                                        let uu____23437 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23437
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23460 =
                                        let uu____23479 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23556  ->
                                                  match uu____23556 with
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
                                                        let uu____23599 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23599
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
                                                                uu___23_23610
                                                                 ->
                                                                match uu___23_23610
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23622
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23630 =
                                                        let uu____23641 =
                                                          let uu____23642 =
                                                            let uu____23643 =
                                                              let uu____23659
                                                                =
                                                                let uu____23660
                                                                  =
                                                                  let uu____23663
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23663
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23660
                                                                 in
                                                              (name, univs,
                                                                uu____23659,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23643
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23642;
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
                                                        (tps, uu____23641)
                                                         in
                                                      (name, uu____23630)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23479
                                         in
                                      (match uu____23460 with
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
                             | uu____23795 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23876  ->
                             match uu____23876 with | (uu____23887,se) -> se))
                      in
                   let uu____23901 =
                     let uu____23908 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23908 rng
                      in
                   (match uu____23901 with
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
                               (fun uu____23953  ->
                                  match uu____23953 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24001,tps,k,uu____24004,constrs)
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
                                      let uu____24025 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24040 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24057,uu____24058,uu____24059,uu____24060,uu____24061)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24068
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24040
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24072 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24079  ->
                                                          match uu___25_24079
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24081 ->
                                                              true
                                                          | uu____24091 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24072))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24025
                                  | uu____24093 -> []))
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
      let uu____24130 =
        FStar_List.fold_left
          (fun uu____24165  ->
             fun b  ->
               match uu____24165 with
               | (env1,binders1) ->
                   let uu____24209 = desugar_binder env1 b  in
                   (match uu____24209 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24232 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24232 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24285 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24130 with
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
          let uu____24389 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24396  ->
                    match uu___26_24396 with
                    | FStar_Syntax_Syntax.Reflectable uu____24398 -> true
                    | uu____24400 -> false))
             in
          if uu____24389
          then
            let monad_env =
              let uu____24404 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24404  in
            let reflect_lid =
              let uu____24406 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24406
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
        let warn1 uu____24457 =
          if warn
          then
            let uu____24459 =
              let uu____24465 =
                let uu____24467 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24467
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24465)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24459
          else ()  in
        let uu____24473 = FStar_Syntax_Util.head_and_args at  in
        match uu____24473 with
        | (hd,args) ->
            let uu____24526 =
              let uu____24527 = FStar_Syntax_Subst.compress hd  in
              uu____24527.FStar_Syntax_Syntax.n  in
            (match uu____24526 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24571)::[] ->
                      let uu____24596 =
                        let uu____24601 =
                          let uu____24610 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24610 a1  in
                        uu____24601 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24596 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24633 =
                             let uu____24639 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24639  in
                           (uu____24633, true)
                       | uu____24654 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24670 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24692 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24809 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24809 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24858 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24858 with | (res1,uu____24880) -> rebind res1 true)
  
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
        | uu____25207 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25265 = get_fail_attr1 warn at  in
             comb uu____25265 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25300 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25300 with
        | FStar_Pervasives_Native.None  ->
            let uu____25303 =
              let uu____25309 =
                let uu____25311 =
                  let uu____25313 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25313 " not found"  in
                Prims.op_Hat "Effect name " uu____25311  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25309)  in
            FStar_Errors.raise_error uu____25303 r
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
                    let uu____25469 = desugar_binders monad_env eff_binders
                       in
                    match uu____25469 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25508 =
                            let uu____25517 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25517  in
                          FStar_List.length uu____25508  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25535 =
                              let uu____25541 =
                                let uu____25543 =
                                  let uu____25545 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25545
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25543  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25541)
                               in
                            FStar_Errors.raise_error uu____25535
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
                                (uu____25613,uu____25614,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25616,uu____25617,uu____25618))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25633 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25636 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25648 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25648 mandatory_members)
                              eff_decls
                             in
                          match uu____25636 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25667 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25696  ->
                                        fun decl  ->
                                          match uu____25696 with
                                          | (env2,out) ->
                                              let uu____25716 =
                                                desugar_decl env2 decl  in
                                              (match uu____25716 with
                                               | (env3,ses) ->
                                                   let uu____25729 =
                                                     let uu____25732 =
                                                       FStar_List.hd ses  in
                                                     uu____25732 :: out  in
                                                   (env3, uu____25729)))
                                     (env1, []))
                                 in
                              (match uu____25667 with
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
                                                 (uu____25778,uu____25779,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25782,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25783,(def,uu____25785)::
                                                        (cps_type,uu____25787)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25788;
                                                     FStar_Parser_AST.level =
                                                       uu____25789;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25822 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25822 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25854 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25855 =
                                                        let uu____25856 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25856
                                                         in
                                                      let uu____25863 =
                                                        let uu____25864 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25864
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25854;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25855;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25863
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25871,uu____25872,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25875,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____25891 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25891 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25923 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25924 =
                                                        let uu____25925 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25925
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25923;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25924;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25932 ->
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
                                       let uu____25951 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25951
                                        in
                                     let uu____25953 =
                                       let uu____25954 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25954
                                        in
                                     ([], uu____25953)  in
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
                                       let uu____25976 =
                                         let uu____25977 =
                                           let uu____25980 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25980
                                            in
                                         let uu____25982 =
                                           let uu____25985 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25985
                                            in
                                         let uu____25987 =
                                           let uu____25990 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25990
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
                                             uu____25977;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25982;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25987
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25976
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26024 =
                                            match uu____26024 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26071 =
                                            let uu____26072 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26074 =
                                              let uu____26079 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26079 to_comb
                                               in
                                            let uu____26097 =
                                              let uu____26102 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26102 to_comb
                                               in
                                            let uu____26120 =
                                              let uu____26125 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26125 to_comb
                                               in
                                            let uu____26143 =
                                              let uu____26148 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26148 to_comb
                                               in
                                            let uu____26166 =
                                              let uu____26171 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26171 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26072;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26074;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26097;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26120;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26143;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26166
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26071)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26194  ->
                                                 match uu___27_26194 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26197 -> true
                                                 | uu____26199 -> false)
                                              qualifiers
                                             in
                                          let uu____26201 =
                                            let uu____26202 =
                                              lookup "return_wp"  in
                                            let uu____26204 =
                                              lookup "bind_wp"  in
                                            let uu____26206 =
                                              lookup "stronger"  in
                                            let uu____26208 =
                                              lookup "if_then_else"  in
                                            let uu____26210 = lookup "ite_wp"
                                               in
                                            let uu____26212 =
                                              lookup "close_wp"  in
                                            let uu____26214 =
                                              lookup "trivial"  in
                                            let uu____26216 =
                                              if rr
                                              then
                                                let uu____26222 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26222
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26226 =
                                              if rr
                                              then
                                                let uu____26232 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26232
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26236 =
                                              if rr
                                              then
                                                let uu____26242 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26242
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26202;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26204;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26206;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26208;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26210;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26212;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26214;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26216;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26226;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26236
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26201)
                                      in
                                   let sigel =
                                     let uu____26247 =
                                       let uu____26248 =
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
                                           uu____26248
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26247
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
                                               let uu____26265 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26265) env3)
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
                let uu____26288 = desugar_binders env1 eff_binders  in
                match uu____26288 with
                | (env2,binders) ->
                    let uu____26325 =
                      let uu____26336 = head_and_args defn  in
                      match uu____26336 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26373 ->
                                let uu____26374 =
                                  let uu____26380 =
                                    let uu____26382 =
                                      let uu____26384 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26384 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26382  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26380)
                                   in
                                FStar_Errors.raise_error uu____26374
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26390 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26420)::args_rev ->
                                let uu____26432 =
                                  let uu____26433 = unparen last_arg  in
                                  uu____26433.FStar_Parser_AST.tm  in
                                (match uu____26432 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26461 -> ([], args))
                            | uu____26470 -> ([], args)  in
                          (match uu____26390 with
                           | (cattributes,args1) ->
                               let uu____26513 = desugar_args env2 args1  in
                               let uu____26514 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26513, uu____26514))
                       in
                    (match uu____26325 with
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
                          (let uu____26554 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26554 with
                           | (ed_binders,uu____26568,ed_binders_opening) ->
                               let sub' shift_n uu____26587 =
                                 match uu____26587 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26602 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26602 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26606 =
                                       let uu____26607 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26607)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26606
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26628 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26629 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26630 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26646 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26647 =
                                          let uu____26648 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26648
                                           in
                                        let uu____26663 =
                                          let uu____26664 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26664
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26646;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26647;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26663
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
                                     uu____26628;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26629;
                                   FStar_Syntax_Syntax.actions = uu____26630;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26680 =
                                   let uu____26683 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26683 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26680;
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
                                           let uu____26698 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26698) env3)
                                  in
                               let env5 =
                                 let uu____26700 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26700
                                 then
                                   let reflect_lid =
                                     let uu____26707 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26707
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
             let uu____26740 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26740) ats
         in
      let env0 =
        let uu____26761 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26761 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26776 =
        let uu____26783 = get_fail_attr false attrs  in
        match uu____26783 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3388_26820 = d  in
              {
                FStar_Parser_AST.d = (uu___3388_26820.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3388_26820.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3388_26820.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26821 =
              FStar_Errors.catch_errors
                (fun uu____26839  ->
                   FStar_Options.with_saved_options
                     (fun uu____26845  -> desugar_decl_noattrs env d1))
               in
            (match uu____26821 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3403_26905 = se  in
                             let uu____26906 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3403_26905.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3403_26905.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3403_26905.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3403_26905.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____26906;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3403_26905.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____26959 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____26959 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27008 =
                                 let uu____27014 =
                                   let uu____27016 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27019 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27022 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27024 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27026 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27016 uu____27019 uu____27022
                                     uu____27024 uu____27026
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27014)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27008);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26776 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27064;
                FStar_Syntax_Syntax.sigrng = uu____27065;
                FStar_Syntax_Syntax.sigquals = uu____27066;
                FStar_Syntax_Syntax.sigmeta = uu____27067;
                FStar_Syntax_Syntax.sigattrs = uu____27068;
                FStar_Syntax_Syntax.sigopts = uu____27069;_}::[] ->
                let uu____27082 =
                  let uu____27085 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27085  in
                FStar_All.pipe_right uu____27082
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27093 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27093))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27106;
                FStar_Syntax_Syntax.sigrng = uu____27107;
                FStar_Syntax_Syntax.sigquals = uu____27108;
                FStar_Syntax_Syntax.sigmeta = uu____27109;
                FStar_Syntax_Syntax.sigattrs = uu____27110;
                FStar_Syntax_Syntax.sigopts = uu____27111;_}::uu____27112 ->
                let uu____27137 =
                  let uu____27140 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27140  in
                FStar_All.pipe_right uu____27137
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27148 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27148))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27164;
                FStar_Syntax_Syntax.sigquals = uu____27165;
                FStar_Syntax_Syntax.sigmeta = uu____27166;
                FStar_Syntax_Syntax.sigattrs = uu____27167;
                FStar_Syntax_Syntax.sigopts = uu____27168;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27189 -> []  in
          let attrs1 =
            let uu____27195 = val_attrs sigelts  in
            FStar_List.append attrs uu____27195  in
          let uu____27198 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3463_27202 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3463_27202.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3463_27202.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3463_27202.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3463_27202.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3463_27202.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27198)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27209 = desugar_decl_aux env d  in
      match uu____27209 with
      | (env1,ses) ->
          let uu____27220 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27220)

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
          let uu____27252 = FStar_Syntax_DsEnv.iface env  in
          if uu____27252
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27267 =
               let uu____27269 =
                 let uu____27271 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27272 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27271
                   uu____27272
                  in
               Prims.op_Negation uu____27269  in
             if uu____27267
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27286 =
                  let uu____27288 =
                    let uu____27290 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27290 lid  in
                  Prims.op_Negation uu____27288  in
                if uu____27286
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27304 =
                     let uu____27306 =
                       let uu____27308 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27308
                         lid
                        in
                     Prims.op_Negation uu____27306  in
                   if uu____27304
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27326 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27326, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27355)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27374 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27383 =
            let uu____27388 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27388 tcs  in
          (match uu____27383 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27405 =
                   let uu____27406 =
                     let uu____27413 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27413  in
                   [uu____27406]  in
                 let uu____27426 =
                   let uu____27429 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27432 =
                     let uu____27443 =
                       let uu____27452 =
                         let uu____27453 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27453  in
                       FStar_Syntax_Syntax.as_arg uu____27452  in
                     [uu____27443]  in
                   FStar_Syntax_Util.mk_app uu____27429 uu____27432  in
                 FStar_Syntax_Util.abs uu____27405 uu____27426
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27493,id))::uu____27495 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27498::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27502 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27502 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27508 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27508]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27529) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27539,uu____27540,uu____27541,uu____27542,uu____27543)
                     ->
                     let uu____27552 =
                       let uu____27553 =
                         let uu____27554 =
                           let uu____27561 = mkclass lid  in
                           (meths, uu____27561)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27554  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27553;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27552]
                 | uu____27564 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27598;
                    FStar_Parser_AST.prange = uu____27599;_},uu____27600)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27610;
                    FStar_Parser_AST.prange = uu____27611;_},uu____27612)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27628;
                         FStar_Parser_AST.prange = uu____27629;_},uu____27630);
                    FStar_Parser_AST.prange = uu____27631;_},uu____27632)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27654;
                         FStar_Parser_AST.prange = uu____27655;_},uu____27656);
                    FStar_Parser_AST.prange = uu____27657;_},uu____27658)::[]
                   -> false
               | (p,uu____27687)::[] ->
                   let uu____27696 = is_app_pattern p  in
                   Prims.op_Negation uu____27696
               | uu____27698 -> false)
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
            let uu____27773 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27773 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27786 =
                     let uu____27787 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27787.FStar_Syntax_Syntax.n  in
                   match uu____27786 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27797) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27828 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27853  ->
                                match uu____27853 with
                                | (qs,ats) ->
                                    let uu____27880 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27880 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27828 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27934::uu____27935 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27938 -> val_quals  in
                            let quals2 =
                              let uu____27942 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27975  ->
                                        match uu____27975 with
                                        | (uu____27989,(uu____27990,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27942
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28010 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28010
                              then
                                let uu____28016 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3640_28031 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3642_28033 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3642_28033.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3642_28033.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3640_28031.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3640_28031.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3640_28031.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3640_28031.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3640_28031.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3640_28031.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28016)
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
                   | uu____28058 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28066 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28085 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28066 with
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
                       let uu___3665_28122 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3665_28122.FStar_Parser_AST.prange)
                       }
                   | uu____28129 -> var_pat  in
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
                     (let uu___3671_28140 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3671_28140.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = quals1;
                        FStar_Parser_AST.attrs =
                          (uu___3671_28140.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28156 =
                     let uu____28157 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28157  in
                   FStar_Parser_AST.mk_term uu____28156
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28181 id_opt =
                   match uu____28181 with
                   | (env1,ses) ->
                       let uu____28203 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28215 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28215
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28217 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28217
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
                               let uu____28223 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28223
                                in
                             let bv_pat1 =
                               let uu____28227 =
                                 let uu____28228 =
                                   let uu____28239 =
                                     let uu____28246 =
                                       let uu____28247 =
                                         FStar_Ident.range_of_id id  in
                                       unit_ty uu____28247  in
                                     (uu____28246,
                                       FStar_Pervasives_Native.None)
                                      in
                                   (bv_pat, uu____28239)  in
                                 FStar_Parser_AST.PatAscribed uu____28228  in
                               let uu____28256 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern uu____28227
                                 uu____28256
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28203 with
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
                              let uu___3695_28310 = id_decl  in
                              {
                                FStar_Parser_AST.d =
                                  (uu___3695_28310.FStar_Parser_AST.d);
                                FStar_Parser_AST.drange =
                                  (uu___3695_28310.FStar_Parser_AST.drange);
                                FStar_Parser_AST.quals =
                                  (d.FStar_Parser_AST.quals);
                                FStar_Parser_AST.attrs =
                                  (uu___3695_28310.FStar_Parser_AST.attrs)
                              }  in
                            let uu____28311 = desugar_decl env1 id_decl1  in
                            (match uu____28311 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28347 id =
                   match uu____28347 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28386 =
                   match uu____28386 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28410 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28410 FStar_Util.set_elements
                    in
                 let uu____28417 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28420 = is_var_pattern pat  in
                      Prims.op_Negation uu____28420)
                    in
                 if uu____28417
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
            let uu____28443 = close_fun env t  in
            desugar_term env uu____28443  in
          let quals1 =
            let uu____28447 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28447
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28459 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28459;
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
                let uu____28472 =
                  let uu____28481 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28481]  in
                let uu____28500 =
                  let uu____28503 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28503
                   in
                FStar_Syntax_Util.arrow uu____28472 uu____28500
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
          uu____28566) ->
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
          let uu____28583 =
            let uu____28585 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28585  in
          if uu____28583
          then
            let uu____28592 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28610 =
                    let uu____28613 =
                      let uu____28614 = desugar_term env t  in
                      ([], uu____28614)  in
                    FStar_Pervasives_Native.Some uu____28613  in
                  (uu____28610, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28627 =
                    let uu____28630 =
                      let uu____28631 = desugar_term env wp  in
                      ([], uu____28631)  in
                    FStar_Pervasives_Native.Some uu____28630  in
                  let uu____28638 =
                    let uu____28641 =
                      let uu____28642 = desugar_term env t  in
                      ([], uu____28642)  in
                    FStar_Pervasives_Native.Some uu____28641  in
                  (uu____28627, uu____28638)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28654 =
                    let uu____28657 =
                      let uu____28658 = desugar_term env t  in
                      ([], uu____28658)  in
                    FStar_Pervasives_Native.Some uu____28657  in
                  (FStar_Pervasives_Native.None, uu____28654)
               in
            (match uu____28592 with
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
                   let uu____28692 =
                     let uu____28695 =
                       let uu____28696 = desugar_term env t  in
                       ([], uu____28696)  in
                     FStar_Pervasives_Native.Some uu____28695  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28692
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
             | uu____28703 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28716 =
            let uu____28717 =
              let uu____28718 =
                let uu____28719 =
                  let uu____28730 =
                    let uu____28731 = desugar_term env bind  in
                    ([], uu____28731)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28730,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28719  in
              {
                FStar_Syntax_Syntax.sigel = uu____28718;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28717]  in
          (env, uu____28716)
      | FStar_Parser_AST.Polymonadic_subcomp (m_eff,n_eff,subcomp) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let uu____28747 =
            let uu____28748 =
              let uu____28749 =
                let uu____28750 =
                  let uu____28759 =
                    let uu____28760 = desugar_term env subcomp  in
                    ([], uu____28760)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname), uu____28759,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____28750  in
              {
                FStar_Syntax_Syntax.sigel = uu____28749;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28748]  in
          (env, uu____28747)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28779 =
              let uu____28780 =
                let uu____28787 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28787, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28780  in
            {
              FStar_Syntax_Syntax.sigel = uu____28779;
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
      let uu____28814 =
        FStar_List.fold_left
          (fun uu____28834  ->
             fun d  ->
               match uu____28834 with
               | (env1,sigelts) ->
                   let uu____28854 = desugar_decl env1 d  in
                   (match uu____28854 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28814 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28945) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28949;
               FStar_Syntax_Syntax.exports = uu____28950;
               FStar_Syntax_Syntax.is_interface = uu____28951;_},FStar_Parser_AST.Module
             (current_lid,uu____28953)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28962) ->
              let uu____28965 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28965
           in
        let uu____28970 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____29012 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29012, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____29034 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____29034, mname, decls, false)
           in
        match uu____28970 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29076 = desugar_decls env2 decls  in
            (match uu____29076 with
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
          let uu____29144 =
            (FStar_Options.interactive ()) &&
              (let uu____29147 =
                 let uu____29149 =
                   let uu____29151 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29151  in
                 FStar_Util.get_file_extension uu____29149  in
               FStar_List.mem uu____29147 ["fsti"; "fsi"])
             in
          if uu____29144 then as_interface m else m  in
        let uu____29165 = desugar_modul_common curmod env m1  in
        match uu____29165 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29187 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29187, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29209 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29209 with
      | (env1,modul,pop_when_done) ->
          let uu____29226 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29226 with
           | (env2,modul1) ->
               ((let uu____29238 =
                   let uu____29240 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29240  in
                 if uu____29238
                 then
                   let uu____29243 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29243
                 else ());
                (let uu____29248 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29248, modul1))))
  
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
        (fun uu____29298  ->
           let uu____29299 = desugar_modul env modul  in
           match uu____29299 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29337  ->
           let uu____29338 = desugar_decls env decls  in
           match uu____29338 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29389  ->
             let uu____29390 = desugar_partial_modul modul env a_modul  in
             match uu____29390 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29485 ->
                  let t =
                    let uu____29495 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29495  in
                  let uu____29508 =
                    let uu____29509 = FStar_Syntax_Subst.compress t  in
                    uu____29509.FStar_Syntax_Syntax.n  in
                  (match uu____29508 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29521,uu____29522)
                       -> bs1
                   | uu____29547 -> failwith "Impossible")
               in
            let uu____29557 =
              let uu____29564 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29564
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29557 with
            | (binders,uu____29566,binders_opening) ->
                let erase_term t =
                  let uu____29574 =
                    let uu____29575 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29575  in
                  FStar_Syntax_Subst.close binders uu____29574  in
                let erase_tscheme uu____29593 =
                  match uu____29593 with
                  | (us,t) ->
                      let t1 =
                        let uu____29613 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29613 t  in
                      let uu____29616 =
                        let uu____29617 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29617  in
                      ([], uu____29616)
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
                    | uu____29640 ->
                        let bs =
                          let uu____29650 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29650  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29690 =
                          let uu____29691 =
                            let uu____29694 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29694  in
                          uu____29691.FStar_Syntax_Syntax.n  in
                        (match uu____29690 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29696,uu____29697) -> bs1
                         | uu____29722 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29730 =
                      let uu____29731 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29731  in
                    FStar_Syntax_Subst.close binders uu____29730  in
                  let uu___3973_29732 = action  in
                  let uu____29733 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29734 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3973_29732.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3973_29732.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29733;
                    FStar_Syntax_Syntax.action_typ = uu____29734
                  }  in
                let uu___3975_29735 = ed  in
                let uu____29736 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29737 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29738 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29739 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3975_29735.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3975_29735.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29736;
                  FStar_Syntax_Syntax.signature = uu____29737;
                  FStar_Syntax_Syntax.combinators = uu____29738;
                  FStar_Syntax_Syntax.actions = uu____29739;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3975_29735.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3982_29755 = se  in
                  let uu____29756 =
                    let uu____29757 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29757  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29756;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3982_29755.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3982_29755.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3982_29755.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3982_29755.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3982_29755.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29759 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29760 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29760 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29777 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29777
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29779 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29779)
  