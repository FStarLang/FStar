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
  
let (unit_ty : FStar_Parser_AST.term) =
  FStar_Parser_AST.mk_term
    (FStar_Parser_AST.Name FStar_Parser_Const.unit_lid)
    FStar_Range.dummyRange FStar_Parser_AST.Type_level
  
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
  'uuuuuu541 .
    'uuuuuu541 ->
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
        let uu____594 =
          let uu____595 =
            let uu____596 =
              let uu____602 = FStar_Parser_AST.compile_op n s r  in
              (uu____602, r)  in
            FStar_Ident.mk_ident uu____596  in
          [uu____595]  in
        FStar_All.pipe_right uu____594 FStar_Ident.lid_of_ids
  
let op_as_term :
  'uuuuuu616 .
    env_t ->
      Prims.int ->
        'uuuuuu616 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____654 =
              let uu____655 =
                let uu____656 =
                  let uu____657 = FStar_Ident.range_of_id op  in
                  FStar_Ident.set_lid_range l uu____657  in
                FStar_Syntax_Syntax.lid_as_fv uu____656 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____655 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____654  in
          let fallback uu____665 =
            let uu____666 = FStar_Ident.text_of_id op  in
            match uu____666 with
            | "=" ->
                r FStar_Parser_Const.op_Eq
                  FStar_Syntax_Syntax.delta_equational
            | ":=" ->
                r FStar_Parser_Const.write_lid
                  FStar_Syntax_Syntax.delta_equational
            | "<" ->
                r FStar_Parser_Const.op_LT
                  FStar_Syntax_Syntax.delta_equational
            | "<=" ->
                r FStar_Parser_Const.op_LTE
                  FStar_Syntax_Syntax.delta_equational
            | ">" ->
                r FStar_Parser_Const.op_GT
                  FStar_Syntax_Syntax.delta_equational
            | ">=" ->
                r FStar_Parser_Const.op_GTE
                  FStar_Syntax_Syntax.delta_equational
            | "&&" ->
                r FStar_Parser_Const.op_And
                  FStar_Syntax_Syntax.delta_equational
            | "||" ->
                r FStar_Parser_Const.op_Or
                  FStar_Syntax_Syntax.delta_equational
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
                let uu____687 = FStar_Options.ml_ish ()  in
                if uu____687
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
            | uu____712 -> FStar_Pervasives_Native.None  in
          let uu____714 =
            let uu____717 =
              let uu____718 = FStar_Ident.text_of_id op  in
              let uu____720 = FStar_Ident.range_of_id op  in
              compile_op_lid arity uu____718 uu____720  in
            desugar_name'
              (fun t  ->
                 let uu___177_728 = t  in
                 let uu____729 = FStar_Ident.range_of_id op  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___177_728.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = uu____729;
                   FStar_Syntax_Syntax.vars =
                     (uu___177_728.FStar_Syntax_Syntax.vars)
                 }) env true uu____717
             in
          match uu____714 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____734 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____749 =
      FStar_Util.remove_dups
        (fun x  ->
           fun y  ->
             let uu____758 = FStar_Ident.text_of_id x  in
             let uu____760 = FStar_Ident.text_of_id y  in
             uu____758 = uu____760) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              let uu____773 = FStar_Ident.text_of_id x  in
              let uu____775 = FStar_Ident.text_of_id y  in
              FStar_String.compare uu____773 uu____775)) uu____749
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____810 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____814 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____814 with | (env1,uu____826) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____829,term) ->
          let uu____831 = free_type_vars env term  in (env, uu____831)
      | FStar_Parser_AST.TAnnotated (id,uu____837) ->
          let uu____838 = FStar_Syntax_DsEnv.push_bv env id  in
          (match uu____838 with | (env1,uu____850) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____854 = free_type_vars env t  in (env, uu____854)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____861 =
        let uu____862 = unparen t  in uu____862.FStar_Parser_AST.tm  in
      match uu____861 with
      | FStar_Parser_AST.Labeled uu____865 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____878 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____878 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____883 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____886 -> []
      | FStar_Parser_AST.Uvar uu____887 -> []
      | FStar_Parser_AST.Var uu____888 -> []
      | FStar_Parser_AST.Projector uu____889 -> []
      | FStar_Parser_AST.Discrim uu____894 -> []
      | FStar_Parser_AST.Name uu____895 -> []
      | FStar_Parser_AST.Requires (t1,uu____897) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____905) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____912,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____931,ts) ->
          FStar_List.collect
            (fun uu____952  ->
               match uu____952 with | (t1,uu____960) -> free_type_vars env t1)
            ts
      | FStar_Parser_AST.Op (uu____961,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____969) ->
          let uu____970 = free_type_vars env t1  in
          let uu____973 = free_type_vars env t2  in
          FStar_List.append uu____970 uu____973
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____978 = free_type_vars_b env b  in
          (match uu____978 with
           | (env1,f) ->
               let uu____993 = free_type_vars env1 t1  in
               FStar_List.append f uu____993)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1010 =
            FStar_List.fold_left
              (fun uu____1034  ->
                 fun bt  ->
                   match uu____1034 with
                   | (env1,free) ->
                       let uu____1058 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1073 = free_type_vars env1 body  in
                             (env1, uu____1073)
                          in
                       (match uu____1058 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1010 with
           | (env1,free) ->
               let uu____1102 = free_type_vars env1 body  in
               FStar_List.append free uu____1102)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1111 =
            FStar_List.fold_left
              (fun uu____1131  ->
                 fun binder  ->
                   match uu____1131 with
                   | (env1,free) ->
                       let uu____1151 = free_type_vars_b env1 binder  in
                       (match uu____1151 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1111 with
           | (env1,free) ->
               let uu____1182 = free_type_vars env1 body  in
               FStar_List.append free uu____1182)
      | FStar_Parser_AST.Project (t1,uu____1186) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init,steps) ->
          let uu____1197 = free_type_vars env rel  in
          let uu____1200 =
            let uu____1203 = free_type_vars env init  in
            let uu____1206 =
              FStar_List.collect
                (fun uu____1215  ->
                   match uu____1215 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1221 = free_type_vars env rel1  in
                       let uu____1224 =
                         let uu____1227 = free_type_vars env just  in
                         let uu____1230 = free_type_vars env next  in
                         FStar_List.append uu____1227 uu____1230  in
                       FStar_List.append uu____1221 uu____1224) steps
               in
            FStar_List.append uu____1203 uu____1206  in
          FStar_List.append uu____1197 uu____1200
      | FStar_Parser_AST.Abs uu____1233 -> []
      | FStar_Parser_AST.Let uu____1240 -> []
      | FStar_Parser_AST.LetOpen uu____1261 -> []
      | FStar_Parser_AST.If uu____1266 -> []
      | FStar_Parser_AST.QForall uu____1273 -> []
      | FStar_Parser_AST.QExists uu____1292 -> []
      | FStar_Parser_AST.Record uu____1311 -> []
      | FStar_Parser_AST.Match uu____1324 -> []
      | FStar_Parser_AST.TryWith uu____1339 -> []
      | FStar_Parser_AST.Bind uu____1354 -> []
      | FStar_Parser_AST.Quote uu____1361 -> []
      | FStar_Parser_AST.VQuote uu____1366 -> []
      | FStar_Parser_AST.Antiquote uu____1367 -> []
      | FStar_Parser_AST.Seq uu____1368 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1422 =
        let uu____1423 = unparen t1  in uu____1423.FStar_Parser_AST.tm  in
      match uu____1422 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1465 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1490 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1490  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1513 =
                     let uu____1514 =
                       let uu____1519 =
                         let uu____1520 = FStar_Ident.range_of_id x  in
                         tm_type uu____1520  in
                       (x, uu____1519)  in
                     FStar_Parser_AST.TAnnotated uu____1514  in
                   let uu____1521 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1513 uu____1521
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
        let uu____1539 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1539  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1562 =
                     let uu____1563 =
                       let uu____1568 =
                         let uu____1569 = FStar_Ident.range_of_id x  in
                         tm_type uu____1569  in
                       (x, uu____1568)  in
                     FStar_Parser_AST.TAnnotated uu____1563  in
                   let uu____1570 = FStar_Ident.range_of_id x  in
                   FStar_Parser_AST.mk_binder uu____1562 uu____1570
                     FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1572 =
             let uu____1573 = unparen t  in uu____1573.FStar_Parser_AST.tm
              in
           match uu____1572 with
           | FStar_Parser_AST.Product uu____1574 -> t
           | uu____1581 ->
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
      | uu____1618 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1629 -> true
    | FStar_Parser_AST.PatTvar (uu____1633,uu____1634) -> true
    | FStar_Parser_AST.PatVar (uu____1640,uu____1641) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1648) -> is_var_pattern p1
    | uu____1661 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1672) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1685;
           FStar_Parser_AST.prange = uu____1686;_},uu____1687)
        -> true
    | uu____1699 -> false
  
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
               (unit_ty, FStar_Pervasives_Native.None)))
          p.FStar_Parser_AST.prange
    | uu____1715 -> p
  
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
            let uu____1788 = destruct_app_pattern env is_top_level p1  in
            (match uu____1788 with
             | (name,args,uu____1831) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1881);
               FStar_Parser_AST.prange = uu____1882;_},args)
            when is_top_level ->
            let uu____1892 =
              let uu____1897 = FStar_Syntax_DsEnv.qualify env id  in
              FStar_Util.Inr uu____1897  in
            (uu____1892, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id,uu____1919);
               FStar_Parser_AST.prange = uu____1920;_},args)
            -> ((FStar_Util.Inl id), args, FStar_Pervasives_Native.None)
        | uu____1950 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____2002 -> acc
      | FStar_Parser_AST.PatConst uu____2005 -> acc
      | FStar_Parser_AST.PatName uu____2006 -> acc
      | FStar_Parser_AST.PatOp uu____2007 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x,uu____2015) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x,uu____2021) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____2030) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____2047 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____2047
      | FStar_Parser_AST.PatAscribed (pat,uu____2055) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           let uu____2083 =
             let uu____2085 = FStar_Ident.text_of_id id1  in
             let uu____2087 = FStar_Ident.text_of_id id2  in
             uu____2085 = uu____2087  in
           if uu____2083 then Prims.int_zero else Prims.int_one)
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2135 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2176 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (is_implicit : bnd -> Prims.bool) =
  fun b  ->
    match b with
    | LocalBinder
        (uu____2224,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2225))
        -> true
    | uu____2228 -> false
  
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2239  ->
    match uu___3_2239 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2246 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2279  ->
    match uu____2279 with
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
      let uu____2361 =
        let uu____2378 =
          let uu____2381 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2381  in
        let uu____2382 =
          let uu____2393 =
            let uu____2402 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2402)  in
          [uu____2393]  in
        (uu____2378, uu____2382)  in
      FStar_Syntax_Syntax.Tm_app uu____2361  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2451 =
        let uu____2468 =
          let uu____2471 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2471  in
        let uu____2472 =
          let uu____2483 =
            let uu____2492 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2492)  in
          [uu____2483]  in
        (uu____2468, uu____2472)  in
      FStar_Syntax_Syntax.Tm_app uu____2451  in
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
          let uu____2555 =
            let uu____2572 =
              let uu____2575 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2575  in
            let uu____2576 =
              let uu____2587 =
                let uu____2596 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2596)  in
              let uu____2604 =
                let uu____2615 =
                  let uu____2624 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2624)  in
                [uu____2615]  in
              uu____2587 :: uu____2604  in
            (uu____2572, uu____2576)  in
          FStar_Syntax_Syntax.Tm_app uu____2555  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2684 =
        let uu____2699 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2718  ->
               match uu____2718 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2729;
                    FStar_Syntax_Syntax.index = uu____2730;
                    FStar_Syntax_Syntax.sort = t;_},uu____2732)
                   ->
                   let uu____2740 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2740) uu____2699
         in
      FStar_All.pipe_right bs uu____2684  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2756 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2774 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2802 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2823,uu____2824,bs,t,uu____2827,uu____2828)
                            ->
                            let uu____2837 = bs_univnames bs  in
                            let uu____2840 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2837 uu____2840
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2843,uu____2844,t,uu____2846,uu____2847,uu____2848)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2855 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2802 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___564_2864 = s  in
        let uu____2865 =
          let uu____2866 =
            let uu____2875 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2893,bs,t,lids1,lids2) ->
                          let uu___575_2906 = se  in
                          let uu____2907 =
                            let uu____2908 =
                              let uu____2925 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____2926 =
                                let uu____2927 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____2927 t  in
                              (lid, uvs, uu____2925, uu____2926, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2908
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2907;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___575_2906.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___575_2906.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___575_2906.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___575_2906.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___575_2906.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____2941,t,tlid,n,lids1) ->
                          let uu___585_2952 = se  in
                          let uu____2953 =
                            let uu____2954 =
                              let uu____2970 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____2970, tlid, n, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____2954  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2953;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___585_2952.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___585_2952.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___585_2952.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___585_2952.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___585_2952.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____2974 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2875, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2866  in
        {
          FStar_Syntax_Syntax.sigel = uu____2865;
          FStar_Syntax_Syntax.sigrng =
            (uu___564_2864.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___564_2864.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___564_2864.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___564_2864.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___564_2864.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2981,t) ->
        let uvs =
          let uu____2984 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____2984 FStar_Util.set_elements  in
        let uu___594_2989 = s  in
        let uu____2990 =
          let uu____2991 =
            let uu____2998 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____2998)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____2991  in
        {
          FStar_Syntax_Syntax.sigel = uu____2990;
          FStar_Syntax_Syntax.sigrng =
            (uu___594_2989.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___594_2989.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___594_2989.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___594_2989.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___594_2989.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3022 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3025 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3032) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3065,(FStar_Util.Inl t,uu____3067),uu____3068)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3115,(FStar_Util.Inr c,uu____3117),uu____3118)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3165 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3167) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3188,(FStar_Util.Inl t,uu____3190),uu____3191) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3238,(FStar_Util.Inr c,uu____3240),uu____3241) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3288 -> empty_set  in
          FStar_Util.set_union uu____3022 uu____3025  in
        let all_lb_univs =
          let uu____3292 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3308 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3308) empty_set)
             in
          FStar_All.pipe_right uu____3292 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___653_3318 = s  in
        let uu____3319 =
          let uu____3320 =
            let uu____3327 =
              let uu____3328 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___656_3340 = lb  in
                        let uu____3341 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3344 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___656_3340.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3341;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___656_3340.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3344;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___656_3340.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___656_3340.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3328)  in
            (uu____3327, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3320  in
        {
          FStar_Syntax_Syntax.sigel = uu____3319;
          FStar_Syntax_Syntax.sigrng =
            (uu___653_3318.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___653_3318.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___653_3318.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___653_3318.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___653_3318.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3353,fml) ->
        let uvs =
          let uu____3356 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3356 FStar_Util.set_elements  in
        let uu___664_3361 = s  in
        let uu____3362 =
          let uu____3363 =
            let uu____3370 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3370)  in
          FStar_Syntax_Syntax.Sig_assume uu____3363  in
        {
          FStar_Syntax_Syntax.sigel = uu____3362;
          FStar_Syntax_Syntax.sigrng =
            (uu___664_3361.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___664_3361.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___664_3361.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___664_3361.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___664_3361.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3372,bs,c,flags) ->
        let uvs =
          let uu____3381 =
            let uu____3384 = bs_univnames bs  in
            let uu____3387 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3384 uu____3387  in
          FStar_All.pipe_right uu____3381 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___675_3395 = s  in
        let uu____3396 =
          let uu____3397 =
            let uu____3410 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3411 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3410, uu____3411, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3397  in
        {
          FStar_Syntax_Syntax.sigel = uu____3396;
          FStar_Syntax_Syntax.sigrng =
            (uu___675_3395.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___675_3395.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___675_3395.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___675_3395.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___675_3395.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs,lax,ses) ->
        let uu___682_3429 = s  in
        let uu____3430 =
          let uu____3431 =
            let uu____3444 = FStar_List.map generalize_annotated_univs ses
               in
            (errs, lax, uu____3444)  in
          FStar_Syntax_Syntax.Sig_fail uu____3431  in
        {
          FStar_Syntax_Syntax.sigel = uu____3430;
          FStar_Syntax_Syntax.sigrng =
            (uu___682_3429.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___682_3429.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___682_3429.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___682_3429.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___682_3429.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3453 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3454 -> s
    | FStar_Syntax_Syntax.Sig_main uu____3455 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3456 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3467 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3474 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3482  ->
    match uu___4_3482 with
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
    | uu____3531 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n  ->
      if n = Prims.int_zero
      then u
      else
        (let uu____3552 = sum_to_universe u (n - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3552)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n  -> sum_to_universe FStar_Syntax_Syntax.U_zero n 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3578 =
      let uu____3579 = unparen t  in uu____3579.FStar_Parser_AST.tm  in
    match uu____3578 with
    | FStar_Parser_AST.Wild  -> FStar_Util.Inr FStar_Syntax_Syntax.U_unknown
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3589)) ->
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
             let uu____3680 = sum_to_universe u n  in
             FStar_Util.Inr uu____3680
         | (FStar_Util.Inr u,FStar_Util.Inl n) ->
             let uu____3697 = sum_to_universe u n  in
             FStar_Util.Inr uu____3697
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3713 =
               let uu____3719 =
                 let uu____3721 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3721
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3719)
                in
             FStar_Errors.raise_error uu____3713 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3730 ->
        let rec aux t1 univargs =
          let uu____3767 =
            let uu____3768 = unparen t1  in uu____3768.FStar_Parser_AST.tm
             in
          match uu____3767 with
          | FStar_Parser_AST.App (t2,targ,uu____3776) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid ->
              if
                FStar_List.existsb
                  (fun uu___5_3803  ->
                     match uu___5_3803 with
                     | FStar_Util.Inr uu____3810 -> true
                     | uu____3813 -> false) univargs
              then
                let uu____3821 =
                  let uu____3822 =
                    FStar_List.map
                      (fun uu___6_3832  ->
                         match uu___6_3832 with
                         | FStar_Util.Inl n -> int_to_universe n
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3822  in
                FStar_Util.Inr uu____3821
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3858  ->
                        match uu___7_3858 with
                        | FStar_Util.Inl n -> n
                        | FStar_Util.Inr uu____3868 -> failwith "impossible")
                     univargs
                    in
                 let uu____3872 =
                   FStar_List.fold_left
                     (fun m  -> fun n  -> if m > n then m else n)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3872)
          | uu____3888 ->
              let uu____3889 =
                let uu____3895 =
                  let uu____3897 =
                    let uu____3899 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3899 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3897  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3895)  in
              FStar_Errors.raise_error uu____3889 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3914 ->
        let uu____3915 =
          let uu____3921 =
            let uu____3923 =
              let uu____3925 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3925 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3923  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3921)  in
        FStar_Errors.raise_error uu____3915 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3966;_});
            FStar_Syntax_Syntax.pos = uu____3967;
            FStar_Syntax_Syntax.vars = uu____3968;_})::uu____3969
        ->
        let uu____4000 =
          let uu____4006 =
            let uu____4008 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4008
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4006)  in
        FStar_Errors.raise_error uu____4000 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4014 ->
        let uu____4033 =
          let uu____4039 =
            let uu____4041 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4041
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4039)  in
        FStar_Errors.raise_error uu____4033 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'uuuuuu4054 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'uuuuuu4054) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4082 = FStar_List.hd fields  in
        match uu____4082 with
        | (f,uu____4092) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4103 =
              match uu____4103 with
              | (f',uu____4109) ->
                  let uu____4110 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4110
                  then ()
                  else
                    (let msg =
                       let uu____4117 = FStar_Ident.string_of_lid f  in
                       let uu____4119 =
                         FStar_Ident.string_of_lid
                           record.FStar_Syntax_DsEnv.typename
                          in
                       let uu____4121 = FStar_Ident.string_of_lid f'  in
                       FStar_Util.format3
                         "Field %s belongs to record type %s, whereas field %s does not"
                         uu____4117 uu____4119 uu____4121
                        in
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                         msg) rg)
               in
            ((let uu____4126 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4126);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4174 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4181 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4182 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4184,pats1) ->
            let aux out uu____4225 =
              match uu____4225 with
              | (p1,uu____4238) ->
                  let intersection =
                    let uu____4248 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4248 out  in
                  let uu____4251 = FStar_Util.set_is_empty intersection  in
                  if uu____4251
                  then
                    let uu____4256 = pat_vars p1  in
                    FStar_Util.set_union out uu____4256
                  else
                    (let duplicate_bv =
                       let uu____4262 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4262  in
                     let uu____4265 =
                       let uu____4271 =
                         let uu____4273 =
                           FStar_Ident.text_of_id
                             duplicate_bv.FStar_Syntax_Syntax.ppname
                            in
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           uu____4273
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4271)
                        in
                     FStar_Errors.raise_error uu____4265 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4297 = pat_vars p  in
          FStar_All.pipe_right uu____4297 (fun uu____4302  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4326 =
              let uu____4328 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4328  in
            if uu____4326
            then ()
            else
              (let nonlinear_vars =
                 let uu____4337 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4337  in
               let first_nonlinear_var =
                 let uu____4341 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4341  in
               let uu____4344 =
                 let uu____4350 =
                   let uu____4352 =
                     FStar_Ident.text_of_id
                       first_nonlinear_var.FStar_Syntax_Syntax.ppname
                      in
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     uu____4352
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4350)  in
               FStar_Errors.raise_error uu____4344 r)
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
          let uu____4679 =
            FStar_Util.find_opt
              (fun y  ->
                 let uu____4686 =
                   FStar_Ident.text_of_id y.FStar_Syntax_Syntax.ppname  in
                 let uu____4688 = FStar_Ident.text_of_id x  in
                 uu____4686 = uu____4688) l
             in
          match uu____4679 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4702 ->
              let uu____4705 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4705 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4846 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4868 =
                  let uu____4874 =
                    let uu____4876 = FStar_Ident.text_of_id op  in
                    let uu____4878 = FStar_Ident.range_of_id op  in
                    FStar_Parser_AST.compile_op Prims.int_zero uu____4876
                      uu____4878
                     in
                  let uu____4880 = FStar_Ident.range_of_id op  in
                  (uu____4874, uu____4880)  in
                FStar_Ident.mk_ident uu____4868  in
              let p2 =
                let uu___909_4883 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___909_4883.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4900 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4903 = aux loc env1 p2  in
                match uu____4903 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____4959 =
                      match binder with
                      | LetBinder uu____4980 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5005 = close_fun env1 t  in
                            desugar_term env1 uu____5005  in
                          let x1 =
                            let uu___935_5007 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___935_5007.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___935_5007.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____4959 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5053 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5054 -> ()
                           | uu____5055 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5056 ->
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
              let uu____5074 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5074, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5087 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5087, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5105 = resolvex loc env1 x  in
              (match uu____5105 with
               | (loc1,env2,xbv) ->
                   let uu____5137 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5137, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5155 = resolvex loc env1 x  in
              (match uu____5155 with
               | (loc1,env2,xbv) ->
                   let uu____5187 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5187, []))
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
              let uu____5201 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5201, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5229;_},args)
              ->
              let uu____5235 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5296  ->
                       match uu____5296 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5377 = aux loc1 env2 arg  in
                           (match uu____5377 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5235 with
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
                   let uu____5549 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5549, annots))
          | FStar_Parser_AST.PatApp uu____5565 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5593 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5643  ->
                       match uu____5643 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5704 = aux loc1 env2 pat  in
                           (match uu____5704 with
                            | (loc2,env3,uu____5743,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5593 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5837 =
                       let uu____5840 =
                         let uu____5847 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5847  in
                       let uu____5848 =
                         let uu____5849 =
                           let uu____5863 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5863, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5849  in
                       FStar_All.pipe_left uu____5840 uu____5848  in
                     FStar_List.fold_right
                       (fun hd  ->
                          fun tl  ->
                            let r =
                              FStar_Range.union_ranges
                                hd.FStar_Syntax_Syntax.p
                                tl.FStar_Syntax_Syntax.p
                               in
                            let uu____5897 =
                              let uu____5898 =
                                let uu____5912 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5912, [(hd, false); (tl, false)])  in
                              FStar_Syntax_Syntax.Pat_cons uu____5898  in
                            FStar_All.pipe_left (pos_r r) uu____5897) pats1
                       uu____5837
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
              let uu____5968 =
                FStar_List.fold_left
                  (fun uu____6027  ->
                     fun p2  ->
                       match uu____6027 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6109 = aux loc1 env2 p2  in
                           (match uu____6109 with
                            | (loc2,env3,uu____6153,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____5968 with
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
                     | uu____6316 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6319 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6319, annots))
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
                     (fun uu____6396  ->
                        match uu____6396 with
                        | (f,p2) ->
                            let uu____6407 = FStar_Ident.ident_of_lid f  in
                            (uu____6407, p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6427  ->
                        match uu____6427 with
                        | (f,uu____6433) ->
                            let uu____6434 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6462  ->
                                      match uu____6462 with
                                      | (g,uu____6469) ->
                                          let uu____6470 =
                                            FStar_Ident.text_of_id f  in
                                          let uu____6472 =
                                            FStar_Ident.text_of_id g  in
                                          uu____6470 = uu____6472))
                               in
                            (match uu____6434 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6479,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6486 =
                  let uu____6487 =
                    let uu____6494 =
                      let uu____6495 =
                        let uu____6496 =
                          let uu____6497 =
                            let uu____6498 =
                              FStar_Ident.ns_of_lid
                                record.FStar_Syntax_DsEnv.typename
                               in
                            FStar_List.append uu____6498
                              [record.FStar_Syntax_DsEnv.constrname]
                             in
                          FStar_Ident.lid_of_ids uu____6497  in
                        FStar_Parser_AST.PatName uu____6496  in
                      FStar_Parser_AST.mk_pattern uu____6495
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6494, args)  in
                  FStar_Parser_AST.PatApp uu____6487  in
                FStar_Parser_AST.mk_pattern uu____6486
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6503 = aux loc env1 app  in
              (match uu____6503 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6580 =
                           let uu____6581 =
                             let uu____6595 =
                               let uu___1085_6596 = fv  in
                               let uu____6597 =
                                 let uu____6600 =
                                   let uu____6601 =
                                     let uu____6608 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6608)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6601
                                    in
                                 FStar_Pervasives_Native.Some uu____6600  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1085_6596.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1085_6596.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6597
                               }  in
                             (uu____6595, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6581  in
                         FStar_All.pipe_left pos uu____6580
                     | uu____6634 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6718 = aux' true loc env1 p2  in
              (match uu____6718 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6771 =
                     FStar_List.fold_left
                       (fun uu____6819  ->
                          fun p4  ->
                            match uu____6819 with
                            | (loc2,env3,ps1) ->
                                let uu____6884 = aux' true loc2 env3 p4  in
                                (match uu____6884 with
                                 | (loc3,env4,uu____6922,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6771 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7083 ->
              let uu____7084 = aux' true loc env1 p1  in
              (match uu____7084 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7175 = aux_maybe_or env p  in
        match uu____7175 with
        | (env1,b,pats) ->
            ((let uu____7230 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7230
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
            let uu____7304 =
              let uu____7305 =
                let uu____7316 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7316, (ty, tacopt))  in
              LetBinder uu____7305  in
            (env, uu____7304, [])  in
          let op_to_ident x =
            let uu____7333 =
              let uu____7339 =
                let uu____7341 = FStar_Ident.text_of_id x  in
                let uu____7343 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.compile_op Prims.int_zero uu____7341
                  uu____7343
                 in
              let uu____7345 = FStar_Ident.range_of_id x  in
              (uu____7339, uu____7345)  in
            FStar_Ident.mk_ident uu____7333  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7356 = op_to_ident x  in
              mklet uu____7356 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7358) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7364;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7380 = op_to_ident x  in
              let uu____7381 = desugar_term env t  in
              mklet uu____7380 uu____7381 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7383);
                 FStar_Parser_AST.prange = uu____7384;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7404 = desugar_term env t  in
              mklet x uu____7404 tacopt1
          | uu____7405 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7418 = desugar_data_pat true env p  in
           match uu____7418 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7448;
                      FStar_Syntax_Syntax.p = uu____7449;_},uu____7450)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7463;
                      FStar_Syntax_Syntax.p = uu____7464;_},uu____7465)::[]
                     -> []
                 | uu____7478 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7486  ->
    fun env  ->
      fun pat  ->
        let uu____7490 = desugar_data_pat false env pat  in
        match uu____7490 with | (env1,uu____7507,pat1) -> (env1, pat1)

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
      let uu____7529 = desugar_term_aq env e  in
      match uu____7529 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7548 = desugar_typ_aq env e  in
      match uu____7548 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7558  ->
        fun range  ->
          match uu____7558 with
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
              ((let uu____7580 =
                  let uu____7582 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7582  in
                if uu____7580
                then
                  let uu____7585 =
                    let uu____7591 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7591)  in
                  FStar_Errors.log_issue range uu____7585
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
                  let uu____7612 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7612 range  in
                let lid1 =
                  let uu____7616 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7616 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7626 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7626 range  in
                           let private_fv =
                             let uu____7628 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7628 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1252_7629 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1252_7629.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1252_7629.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7630 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7634 =
                        let uu____7640 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7640)
                         in
                      FStar_Errors.raise_error uu____7634 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7660 =
                  let uu____7667 =
                    let uu____7668 =
                      let uu____7685 =
                        let uu____7696 =
                          let uu____7705 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7705)  in
                        [uu____7696]  in
                      (lid1, uu____7685)  in
                    FStar_Syntax_Syntax.Tm_app uu____7668  in
                  FStar_Syntax_Syntax.mk uu____7667  in
                uu____7660 FStar_Pervasives_Native.None range))

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
          let uu___1268_7824 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1268_7824.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1268_7824.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7827 =
          let uu____7828 = unparen top  in uu____7828.FStar_Parser_AST.tm  in
        match uu____7827 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7833 ->
            let uu____7842 = desugar_formula env top  in (uu____7842, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7851 = desugar_formula env t  in (uu____7851, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7860 = desugar_formula env t  in (uu____7860, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7887 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7887, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7889 = mk (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7889, noaqs)
        | FStar_Parser_AST.Op (id,args) when
            let uu____7896 = FStar_Ident.text_of_id id  in uu____7896 = "=!="
            ->
            let r = FStar_Ident.range_of_id id  in
            let e =
              let uu____7902 =
                let uu____7903 =
                  let uu____7910 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7910, args)  in
                FStar_Parser_AST.Op uu____7903  in
              FStar_Parser_AST.mk_term uu____7902 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7915 =
              let uu____7916 =
                let uu____7917 =
                  let uu____7924 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7924, [e])  in
                FStar_Parser_AST.Op uu____7917  in
              FStar_Parser_AST.mk_term uu____7916 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7915
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7936 = FStar_Ident.text_of_id op_star  in
             uu____7936 = "*") &&
              (let uu____7941 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____7941 FStar_Option.isNone)
            ->
            let rec flatten t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op (id,t1::t2::[]) when
                  (let uu____7965 = FStar_Ident.text_of_id id  in
                   uu____7965 = "*") &&
                    (let uu____7970 =
                       op_as_term env (Prims.of_int (2))
                         top.FStar_Parser_AST.range op_star
                        in
                     FStar_All.pipe_right uu____7970 FStar_Option.isNone)
                  ->
                  let uu____7977 = flatten t1  in
                  FStar_List.append uu____7977 [t2]
              | uu____7980 -> [t]  in
            let terms = flatten lhs  in
            let t =
              let uu___1313_7985 = top  in
              let uu____7986 =
                let uu____7987 =
                  let uu____7998 =
                    FStar_List.map
                      (fun uu____8009  -> FStar_Util.Inr uu____8009) terms
                     in
                  (uu____7998, rhs)  in
                FStar_Parser_AST.Sum uu____7987  in
              {
                FStar_Parser_AST.tm = uu____7986;
                FStar_Parser_AST.range =
                  (uu___1313_7985.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1313_7985.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8017 =
              let uu____8018 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8018  in
            (uu____8017, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8024 =
              let uu____8030 =
                let uu____8032 =
                  let uu____8034 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8034 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8032  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8030)  in
            FStar_Errors.raise_error uu____8024 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8049 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8049 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8056 =
                   let uu____8062 =
                     let uu____8064 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8064
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8062)
                    in
                 FStar_Errors.raise_error uu____8056
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8079 =
                     let uu____8104 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8166 = desugar_term_aq env t  in
                               match uu____8166 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8104 FStar_List.unzip  in
                   (match uu____8079 with
                    | (args1,aqs) ->
                        let uu____8299 =
                          mk (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8299, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n,(a,uu____8316)::[]) when
            let uu____8331 = FStar_Ident.string_of_lid n  in
            uu____8331 = "SMTPat" ->
            let uu____8335 =
              let uu___1342_8336 = top  in
              let uu____8337 =
                let uu____8338 =
                  let uu____8345 =
                    let uu___1344_8346 = top  in
                    let uu____8347 =
                      let uu____8348 = smt_pat_lid top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8348  in
                    {
                      FStar_Parser_AST.tm = uu____8347;
                      FStar_Parser_AST.range =
                        (uu___1344_8346.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1344_8346.FStar_Parser_AST.level)
                    }  in
                  (uu____8345, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8338  in
              {
                FStar_Parser_AST.tm = uu____8337;
                FStar_Parser_AST.range =
                  (uu___1342_8336.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1342_8336.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8335
        | FStar_Parser_AST.Construct (n,(a,uu____8351)::[]) when
            let uu____8366 = FStar_Ident.string_of_lid n  in
            uu____8366 = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8373 =
                let uu___1354_8374 = top  in
                let uu____8375 =
                  let uu____8376 =
                    let uu____8383 =
                      let uu___1356_8384 = top  in
                      let uu____8385 =
                        let uu____8386 =
                          smt_pat_lid top.FStar_Parser_AST.range  in
                        FStar_Parser_AST.Var uu____8386  in
                      {
                        FStar_Parser_AST.tm = uu____8385;
                        FStar_Parser_AST.range =
                          (uu___1356_8384.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1356_8384.FStar_Parser_AST.level)
                      }  in
                    (uu____8383, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8376  in
                {
                  FStar_Parser_AST.tm = uu____8375;
                  FStar_Parser_AST.range =
                    (uu___1354_8374.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1354_8374.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8373))
        | FStar_Parser_AST.Construct (n,(a,uu____8389)::[]) when
            let uu____8404 = FStar_Ident.string_of_lid n  in
            uu____8404 = "SMTPatOr" ->
            let uu____8408 =
              let uu___1365_8409 = top  in
              let uu____8410 =
                let uu____8411 =
                  let uu____8418 =
                    let uu___1367_8419 = top  in
                    let uu____8420 =
                      let uu____8421 =
                        smt_pat_or_lid top.FStar_Parser_AST.range  in
                      FStar_Parser_AST.Var uu____8421  in
                    {
                      FStar_Parser_AST.tm = uu____8420;
                      FStar_Parser_AST.range =
                        (uu___1367_8419.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1367_8419.FStar_Parser_AST.level)
                    }  in
                  (uu____8418, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8411  in
              {
                FStar_Parser_AST.tm = uu____8410;
                FStar_Parser_AST.range =
                  (uu___1365_8409.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1365_8409.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8408
        | FStar_Parser_AST.Name lid when
            let uu____8423 = FStar_Ident.string_of_lid lid  in
            uu____8423 = "Type0" ->
            let uu____8427 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)  in
            (uu____8427, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8429 = FStar_Ident.string_of_lid lid  in
            uu____8429 = "Type" ->
            let uu____8433 =
              mk (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8433, noaqs)
        | FStar_Parser_AST.Construct (lid,(t,FStar_Parser_AST.UnivApp )::[])
            when
            let uu____8450 = FStar_Ident.string_of_lid lid  in
            uu____8450 = "Type" ->
            let uu____8454 =
              let uu____8455 =
                let uu____8456 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8456  in
              mk uu____8455  in
            (uu____8454, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8458 = FStar_Ident.string_of_lid lid  in
            uu____8458 = "Effect" ->
            let uu____8462 =
              mk (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8462, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8464 = FStar_Ident.string_of_lid lid  in
            uu____8464 = "True" ->
            let uu____8468 =
              let uu____8469 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8469
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8468, noaqs)
        | FStar_Parser_AST.Name lid when
            let uu____8471 = FStar_Ident.string_of_lid lid  in
            uu____8471 = "False" ->
            let uu____8475 =
              let uu____8476 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8476
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8475, noaqs)
        | FStar_Parser_AST.Projector (eff_name,id) when
            (let uu____8481 = FStar_Ident.text_of_id id  in
             is_special_effect_combinator uu____8481) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let txt = FStar_Ident.text_of_id id  in
            let uu____8485 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8485 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8494 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8494, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8496 =
                   let uu____8498 = FStar_Ident.string_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8498 txt
                    in
                 failwith uu____8496)
        | FStar_Parser_AST.Var l ->
            let uu____8506 = desugar_name mk setpos env true l  in
            (uu____8506, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8514 = desugar_name mk setpos env true l  in
            (uu____8514, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8531 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8531 with
              | FStar_Pervasives_Native.Some uu____8541 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8549 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8549 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8567 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8588 =
                   let uu____8589 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk setpos env resolve uu____8589  in
                 (uu____8588, noaqs)
             | uu____8595 ->
                 let uu____8603 =
                   let uu____8609 =
                     let uu____8611 = FStar_Ident.string_of_lid l  in
                     FStar_Util.format1
                       "Data constructor or effect %s not found" uu____8611
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8609)  in
                 FStar_Errors.raise_error uu____8603
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8620 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8620 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8627 =
                   let uu____8633 =
                     let uu____8635 = FStar_Ident.string_of_lid lid  in
                     FStar_Util.format1 "Data constructor %s not found"
                       uu____8635
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8633)
                    in
                 FStar_Errors.raise_error uu____8627
                   top.FStar_Parser_AST.range
             | uu____8643 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8647 = desugar_name mk setpos env true lid'  in
                 (uu____8647, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8668 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8668 with
             | FStar_Pervasives_Native.Some head ->
                 let head1 = mk (FStar_Syntax_Syntax.Tm_fvar head)  in
                 (match args with
                  | [] -> (head1, noaqs)
                  | uu____8687 ->
                      let uu____8694 =
                        FStar_Util.take
                          (fun uu____8718  ->
                             match uu____8718 with
                             | (uu____8724,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8694 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8769 =
                             let uu____8794 =
                               FStar_List.map
                                 (fun uu____8837  ->
                                    match uu____8837 with
                                    | (t,imp) ->
                                        let uu____8854 =
                                          desugar_term_aq env t  in
                                        (match uu____8854 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8794 FStar_List.unzip
                              in
                           (match uu____8769 with
                            | (args2,aqs) ->
                                let head2 =
                                  if universes1 = []
                                  then head1
                                  else
                                    mk
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head1, universes1))
                                   in
                                let uu____8997 =
                                  mk
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head2, args2))
                                   in
                                (uu____8997, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9016 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9016 with
                   | FStar_Pervasives_Native.None  ->
                       let uu____9024 =
                         let uu____9026 =
                           let uu____9028 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9028 " not found"  in
                         Prims.op_Hat "Constructor " uu____9026  in
                       (FStar_Errors.Fatal_ConstructorNotFound, uu____9024)
                   | FStar_Pervasives_Native.Some uu____9033 ->
                       let uu____9034 =
                         let uu____9036 =
                           let uu____9038 = FStar_Ident.string_of_lid l  in
                           Prims.op_Hat uu____9038
                             " used at an unexpected position"
                            in
                         Prims.op_Hat "Effect " uu____9036  in
                       (FStar_Errors.Fatal_UnexpectedEffect, uu____9034)
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9067  ->
                 match uu___8_9067 with
                 | FStar_Util.Inr uu____9073 -> true
                 | uu____9075 -> false) binders
            ->
            let terms =
              let uu____9084 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9101  ->
                        match uu___9_9101 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9107 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9084 [t]  in
            let uu____9109 =
              let uu____9134 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9191 = desugar_typ_aq env t1  in
                        match uu____9191 with
                        | (t',aq) ->
                            let uu____9202 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9202, aq)))
                 in
              FStar_All.pipe_right uu____9134 FStar_List.unzip  in
            (match uu____9109 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9312 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9312
                    in
                 let uu____9321 =
                   mk (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9321, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9348 =
              let uu____9365 =
                let uu____9372 =
                  let uu____9379 =
                    FStar_All.pipe_left
                      (fun uu____9388  -> FStar_Util.Inl uu____9388)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9379]  in
                FStar_List.append binders uu____9372  in
              FStar_List.fold_left
                (fun uu____9433  ->
                   fun b  ->
                     match uu____9433 with
                     | (env1,tparams,typs) ->
                         let uu____9494 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9509 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9509)
                            in
                         (match uu____9494 with
                          | (xopt,t1) ->
                              let uu____9534 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9543 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9543)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9534 with
                               | (env2,x) ->
                                   let uu____9563 =
                                     let uu____9566 =
                                       let uu____9569 =
                                         let uu____9570 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9570
                                          in
                                       [uu____9569]  in
                                     FStar_List.append typs uu____9566  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1496_9596 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1496_9596.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1496_9596.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9563)))) (env, [], []) uu____9365
               in
            (match uu____9348 with
             | (env1,uu____9624,targs) ->
                 let tup =
                   let uu____9647 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9647
                    in
                 let uu____9648 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9648, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9667 = uncurry binders t  in
            (match uu____9667 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9711 =
                   match uu___10_9711 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9728 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9728
                   | hd::tl ->
                       let bb = desugar_binder env1 hd  in
                       let uu____9752 =
                         as_binder env1 hd.FStar_Parser_AST.aqual bb  in
                       (match uu____9752 with
                        | (b,env2) -> aux env2 (b :: bs1) tl)
                    in
                 let uu____9785 = aux env [] bs  in (uu____9785, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9794 = desugar_binder env b  in
            (match uu____9794 with
             | (FStar_Pervasives_Native.None ,uu____9805) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9820 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9820 with
                  | ((x,uu____9836),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9849 =
                        let uu____9850 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9850  in
                      (uu____9849, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set::sets2 ->
                    let i = FStar_Util.set_intersect acc set  in
                    let uu____9928 = FStar_Util.set_is_empty i  in
                    if uu____9928
                    then
                      let uu____9933 = FStar_Util.set_union acc set  in
                      aux uu____9933 sets2
                    else
                      (let uu____9938 =
                         let uu____9939 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9939  in
                       FStar_Pervasives_Native.Some uu____9938)
                 in
              let uu____9942 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9942 sets  in
            ((let uu____9946 = check_disjoint bvss  in
              match uu____9946 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id ->
                  let uu____9950 =
                    let uu____9956 =
                      let uu____9958 = FStar_Ident.text_of_id id  in
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        uu____9958
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9956)
                     in
                  let uu____9962 = FStar_Ident.range_of_id id  in
                  FStar_Errors.raise_error uu____9950 uu____9962);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9970 =
                FStar_List.fold_left
                  (fun uu____9990  ->
                     fun pat  ->
                       match uu____9990 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10016,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10026 =
                                  let uu____10029 = free_type_vars env1 t  in
                                  FStar_List.append uu____10029 ftvs  in
                                (env1, uu____10026)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10034,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10045 =
                                  let uu____10048 = free_type_vars env1 t  in
                                  let uu____10051 =
                                    let uu____10054 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10054 ftvs  in
                                  FStar_List.append uu____10048 uu____10051
                                   in
                                (env1, uu____10045)
                            | uu____10059 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____9970 with
              | (uu____10068,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10080 =
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
                    FStar_List.append uu____10080 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10160 = desugar_term_aq env1 body  in
                        (match uu____10160 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10195 =
                                       let uu____10196 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10196
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10195
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
                             let uu____10265 =
                               let uu____10266 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10266  in
                             (uu____10265, aq))
                    | p::rest ->
                        let uu____10279 = desugar_binding_pat env1 p  in
                        (match uu____10279 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10311)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10326 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10335 =
                               match b with
                               | LetBinder uu____10376 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10445) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10499 =
                                           let uu____10508 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10508, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10499
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10570,uu____10571) ->
                                              let tup2 =
                                                let uu____10573 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10573
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10578 =
                                                  let uu____10585 =
                                                    let uu____10586 =
                                                      let uu____10603 =
                                                        mk
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10606 =
                                                        let uu____10617 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10626 =
                                                          let uu____10637 =
                                                            let uu____10646 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10646
                                                             in
                                                          [uu____10637]  in
                                                        uu____10617 ::
                                                          uu____10626
                                                         in
                                                      (uu____10603,
                                                        uu____10606)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10586
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10585
                                                   in
                                                uu____10578
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10694 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10694
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10745,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10747,pats1)) ->
                                              let tupn =
                                                let uu____10792 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10792
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10805 =
                                                  let uu____10806 =
                                                    let uu____10823 =
                                                      mk
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10826 =
                                                      let uu____10837 =
                                                        let uu____10848 =
                                                          let uu____10857 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10857
                                                           in
                                                        [uu____10848]  in
                                                      FStar_List.append args
                                                        uu____10837
                                                       in
                                                    (uu____10823,
                                                      uu____10826)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10806
                                                   in
                                                mk uu____10805  in
                                              let p2 =
                                                let uu____10905 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10905
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10952 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10335 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11044,uu____11045,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11067 =
                let uu____11068 = unparen e  in
                uu____11068.FStar_Parser_AST.tm  in
              match uu____11067 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11078 ->
                  let uu____11079 = desugar_term_aq env e  in
                  (match uu____11079 with
                   | (head,aq) ->
                       let uu____11092 =
                         mk (FStar_Syntax_Syntax.Tm_uinst (head, universes))
                          in
                       (uu____11092, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11099 ->
            let rec aux args aqs e =
              let uu____11176 =
                let uu____11177 = unparen e  in
                uu____11177.FStar_Parser_AST.tm  in
              match uu____11176 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11195 = desugar_term_aq env t  in
                  (match uu____11195 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11243 ->
                  let uu____11244 = desugar_term_aq env e  in
                  (match uu____11244 with
                   | (head,aq) ->
                       let uu____11265 =
                         mk (FStar_Syntax_Syntax.Tm_app (head, args))  in
                       (uu____11265, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              let uu____11318 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                uu____11318
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              let uu____11325 = FStar_Ident.range_of_id x  in
              FStar_Ident.lid_of_path ["bind"] uu____11325  in
            let bind =
              let uu____11330 = FStar_Ident.range_of_id x  in
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                uu____11330 FStar_Parser_AST.Expr
               in
            let uu____11331 =
              FStar_Parser_AST.mkExplicitApp bind [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11331
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
            let uu____11383 = desugar_term_aq env t  in
            (match uu____11383 with
             | (tm,s) ->
                 let uu____11394 =
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11394, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11400 =
              let uu____11413 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11413 then desugar_typ_aq else desugar_term_aq  in
            uu____11400 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11480 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11623  ->
                        match uu____11623 with
                        | (attr_opt,(p,def)) ->
                            let uu____11681 = is_app_pattern p  in
                            if uu____11681
                            then
                              let uu____11714 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11714, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11797 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11797, def1)
                               | uu____11842 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id,uu____11880);
                                           FStar_Parser_AST.prange =
                                             uu____11881;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11930 =
                                            let uu____11951 =
                                              let uu____11956 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____11956  in
                                            (uu____11951, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11930, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id,uu____12048) ->
                                        if top_level
                                        then
                                          let uu____12084 =
                                            let uu____12105 =
                                              let uu____12110 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id
                                                 in
                                              FStar_Util.Inr uu____12110  in
                                            (uu____12105, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12084, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12201 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12234 =
                FStar_List.fold_left
                  (fun uu____12323  ->
                     fun uu____12324  ->
                       match (uu____12323, uu____12324) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12454,uu____12455),uu____12456))
                           ->
                           let uu____12590 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12630 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12630 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12665 =
                                        let uu____12668 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12668 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12665, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12684 =
                                   let uu____12692 =
                                     FStar_Ident.ident_of_lid l  in
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 uu____12692
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12684 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12590 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12234 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12938 =
                    match uu____12938 with
                    | (attrs_opt,(uu____12978,args,result_t),def) ->
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
                                let uu____13070 = is_comp_type env1 t  in
                                if uu____13070
                                then
                                  ((let uu____13074 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13084 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13084))
                                       in
                                    match uu____13074 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13091 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13094 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13094))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13091
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
                          | uu____13105 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13108 = desugar_term_aq env1 def2  in
                        (match uu____13108 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13130 =
                                     let uu____13131 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13131
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13130
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
                  let uu____13172 =
                    let uu____13189 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13189 FStar_List.unzip  in
                  (match uu____13172 with
                   | (lbs1,aqss) ->
                       let uu____13331 = desugar_term_aq env' body  in
                       (match uu____13331 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13437  ->
                                    fun used_marker  ->
                                      match uu____13437 with
                                      | (_attr_opt,(f,uu____13511,uu____13512),uu____13513)
                                          ->
                                          let uu____13570 =
                                            let uu____13572 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13572  in
                                          if uu____13570
                                          then
                                            let uu____13596 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13614 =
                                                    FStar_Ident.text_of_id x
                                                     in
                                                  let uu____13616 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13614, "Local",
                                                    uu____13616)
                                              | FStar_Util.Inr l ->
                                                  let uu____13621 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13623 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13621, "Global",
                                                    uu____13623)
                                               in
                                            (match uu____13596 with
                                             | (nm,gl,rng) ->
                                                 let uu____13634 =
                                                   let uu____13640 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13640)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13634)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13648 =
                                let uu____13651 =
                                  let uu____13652 =
                                    let uu____13666 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13666)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13652  in
                                FStar_All.pipe_left mk uu____13651  in
                              (uu____13648,
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
              let uu____13768 = desugar_term_aq env t1  in
              match uu____13768 with
              | (t11,aq0) ->
                  let uu____13789 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13789 with
                   | (env1,binder,pat1) ->
                       let uu____13819 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13861 = desugar_term_aq env1 t2  in
                             (match uu____13861 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13883 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13883
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13884 =
                                    FStar_All.pipe_left mk
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13884, aq))
                         | LocalBinder (x,uu____13925) ->
                             let uu____13926 = desugar_term_aq env1 t2  in
                             (match uu____13926 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13948;
                                         FStar_Syntax_Syntax.p = uu____13949;_},uu____13950)::[]
                                        -> body1
                                    | uu____13963 ->
                                        let uu____13966 =
                                          let uu____13973 =
                                            let uu____13974 =
                                              let uu____13997 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14000 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____13997, uu____14000)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____13974
                                             in
                                          FStar_Syntax_Syntax.mk uu____13973
                                           in
                                        uu____13966
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14037 =
                                    let uu____14040 =
                                      let uu____14041 =
                                        let uu____14055 =
                                          let uu____14058 =
                                            let uu____14059 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14059]  in
                                          FStar_Syntax_Subst.close
                                            uu____14058 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14055)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14041
                                       in
                                    FStar_All.pipe_left mk uu____14040  in
                                  (uu____14037, aq))
                          in
                       (match uu____13819 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14167 = FStar_List.hd lbs  in
            (match uu____14167 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14211 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14211
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool =
              let uu____14227 =
                let uu____14228 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14228  in
              mk uu____14227  in
            let uu____14229 = desugar_term_aq env t1  in
            (match uu____14229 with
             | (t1',aq1) ->
                 let uu____14240 = desugar_term_aq env t2  in
                 (match uu____14240 with
                  | (t2',aq2) ->
                      let uu____14251 = desugar_term_aq env t3  in
                      (match uu____14251 with
                       | (t3',aq3) ->
                           let uu____14262 =
                             let uu____14263 =
                               let uu____14264 =
                                 let uu____14287 =
                                   let uu____14304 =
                                     let uu____14319 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14319,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14333 =
                                     let uu____14350 =
                                       let uu____14365 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14365,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14350]  in
                                   uu____14304 :: uu____14333  in
                                 (t1', uu____14287)  in
                               FStar_Syntax_Syntax.Tm_match uu____14264  in
                             mk uu____14263  in
                           (uu____14262, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14561 =
              match uu____14561 with
              | (pat,wopt,b) ->
                  let uu____14583 = desugar_match_pat env pat  in
                  (match uu____14583 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14614 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14614
                          in
                       let uu____14619 = desugar_term_aq env1 b  in
                       (match uu____14619 with
                        | (b1,aq) ->
                            let uu____14632 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14632, aq)))
               in
            let uu____14637 = desugar_term_aq env e  in
            (match uu____14637 with
             | (e1,aq) ->
                 let uu____14648 =
                   let uu____14679 =
                     let uu____14712 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14712 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14679
                     (fun uu____14930  ->
                        match uu____14930 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14648 with
                  | (brs,aqs) ->
                      let uu____15149 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15149, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15183 =
              let uu____15204 = is_comp_type env t  in
              if uu____15204
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15259 = desugar_term_aq env t  in
                 match uu____15259 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15183 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15351 = desugar_term_aq env e  in
                 (match uu____15351 with
                  | (e1,aq) ->
                      let uu____15362 =
                        FStar_All.pipe_left mk
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15362, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15401,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15444 = FStar_List.hd fields  in
              match uu____15444 with
              | (f,uu____15456) -> FStar_Ident.ns_of_lid f  in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15504  ->
                        match uu____15504 with
                        | (g,uu____15511) ->
                            let uu____15512 = FStar_Ident.text_of_id f  in
                            let uu____15514 =
                              let uu____15516 = FStar_Ident.ident_of_lid g
                                 in
                              FStar_Ident.text_of_id uu____15516  in
                            uu____15512 = uu____15514))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15523,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15537 =
                         let uu____15543 =
                           let uu____15545 = FStar_Ident.text_of_id f  in
                           let uu____15547 =
                             FStar_Ident.string_of_lid
                               record.FStar_Syntax_DsEnv.typename
                              in
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             uu____15545 uu____15547
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15543)
                          in
                       FStar_Errors.raise_error uu____15537
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
                  let uu____15558 =
                    let uu____15569 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15600  ->
                              match uu____15600 with
                              | (f,uu____15610) ->
                                  let uu____15611 =
                                    let uu____15612 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15612
                                     in
                                  (uu____15611, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15569)  in
                  FStar_Parser_AST.Construct uu____15558
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15630 =
                      let uu____15631 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15631  in
                    let uu____15632 = FStar_Ident.range_of_id x  in
                    FStar_Parser_AST.mk_term uu____15630 uu____15632
                      FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15634 =
                      let uu____15647 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15677  ->
                                match uu____15677 with
                                | (f,uu____15687) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15647)  in
                    FStar_Parser_AST.Record uu____15634  in
                  let uu____15696 =
                    let uu____15717 =
                      let uu____15732 =
                        let uu____15745 =
                          let uu____15750 =
                            let uu____15751 = FStar_Ident.range_of_id x  in
                            FStar_Parser_AST.mk_pattern
                              (FStar_Parser_AST.PatVar
                                 (x, FStar_Pervasives_Native.None))
                              uu____15751
                             in
                          (uu____15750, e)  in
                        (FStar_Pervasives_Native.None, uu____15745)  in
                      [uu____15732]  in
                    (FStar_Parser_AST.NoLetQualifier, uu____15717,
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
                     in
                  FStar_Parser_AST.Let uu____15696
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15803 = desugar_term_aq env recterm1  in
            (match uu____15803 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15819;
                         FStar_Syntax_Syntax.vars = uu____15820;_},args)
                      ->
                      let uu____15846 =
                        let uu____15847 =
                          let uu____15848 =
                            let uu____15865 =
                              let uu____15868 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15869 =
                                let uu____15872 =
                                  let uu____15873 =
                                    let uu____15880 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15880)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15873
                                   in
                                FStar_Pervasives_Native.Some uu____15872  in
                              FStar_Syntax_Syntax.fvar uu____15868
                                FStar_Syntax_Syntax.delta_constant
                                uu____15869
                               in
                            (uu____15865, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15848  in
                        FStar_All.pipe_left mk uu____15847  in
                      (uu____15846, s)
                  | uu____15909 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____15912 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____15912 with
             | (constrname,is_rec) ->
                 let uu____15931 = desugar_term_aq env e  in
                 (match uu____15931 with
                  | (e1,s) ->
                      let projname =
                        let uu____15943 = FStar_Ident.ident_of_lid f  in
                        FStar_Syntax_Util.mk_field_projector_name_from_ident
                          constrname uu____15943
                         in
                      let qual =
                        if is_rec
                        then
                          let uu____15950 =
                            let uu____15951 =
                              let uu____15956 = FStar_Ident.ident_of_lid f
                                 in
                              (constrname, uu____15956)  in
                            FStar_Syntax_Syntax.Record_projector uu____15951
                             in
                          FStar_Pervasives_Native.Some uu____15950
                        else FStar_Pervasives_Native.None  in
                      let uu____15959 =
                        let uu____15960 =
                          let uu____15961 =
                            let uu____15978 =
                              let uu____15981 =
                                let uu____15982 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____15982
                                 in
                              FStar_Syntax_Syntax.fvar uu____15981
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____15984 =
                              let uu____15995 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____15995]  in
                            (uu____15978, uu____15984)  in
                          FStar_Syntax_Syntax.Tm_app uu____15961  in
                        FStar_All.pipe_left mk uu____15960  in
                      (uu____15959, s)))
        | FStar_Parser_AST.NamedTyp (n,e) ->
            ((let uu____16035 = FStar_Ident.range_of_id n  in
              FStar_Errors.log_issue uu____16035
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16046 =
              let uu____16047 = FStar_Syntax_Subst.compress tm  in
              uu____16047.FStar_Syntax_Syntax.n  in
            (match uu____16046 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16055 =
                   let uu___2064_16056 =
                     let uu____16057 =
                       let uu____16059 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16059  in
                     FStar_Syntax_Util.exp_string uu____16057  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2064_16056.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2064_16056.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16055, noaqs)
             | uu____16060 ->
                 let uu____16061 =
                   let uu____16067 =
                     let uu____16069 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16069
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16067)  in
                 FStar_Errors.raise_error uu____16061
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16078 = desugar_term_aq env e  in
            (match uu____16078 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16090 =
                   FStar_All.pipe_left mk
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16090, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16095 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16096 =
              let uu____16097 =
                let uu____16104 = desugar_term env e  in (bv, uu____16104)
                 in
              [uu____16097]  in
            (uu____16095, uu____16096)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16129 =
              let uu____16130 =
                let uu____16131 =
                  let uu____16138 = desugar_term env e  in (uu____16138, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16131  in
              FStar_All.pipe_left mk uu____16130  in
            (uu____16129, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16167 -> false  in
              let uu____16169 =
                let uu____16170 = unparen rel1  in
                uu____16170.FStar_Parser_AST.tm  in
              match uu____16169 with
              | FStar_Parser_AST.Op (id,uu____16173) ->
                  let uu____16178 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id
                     in
                  (match uu____16178 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16186 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16186 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id ->
                  let uu____16197 = FStar_Syntax_DsEnv.try_lookup_id env id
                     in
                  (match uu____16197 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16203 -> false  in
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
              let uu____16224 =
                let uu____16225 =
                  let uu____16232 =
                    let uu____16233 =
                      let uu____16234 =
                        let uu____16243 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16256 =
                          let uu____16257 =
                            let uu____16258 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16258  in
                          FStar_Parser_AST.mk_term uu____16257
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16243, uu____16256,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16234  in
                    FStar_Parser_AST.mk_term uu____16233
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16232)  in
                FStar_Parser_AST.Abs uu____16225  in
              FStar_Parser_AST.mk_term uu____16224
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
                FStar_Range.dummyRange FStar_Parser_AST.Expr
               in
            let push_impl r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_push_impl_lid)
                r FStar_Parser_AST.Expr
               in
            let last_expr =
              let uu____16279 = FStar_List.last steps  in
              match uu____16279 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16282,uu____16283,last_expr)) -> last_expr
              | uu____16285 -> failwith "impossible: no last_expr on calc"
               in
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
                FStar_Range.dummyRange
               in
            let uu____16313 =
              FStar_List.fold_left
                (fun uu____16331  ->
                   fun uu____16332  ->
                     match (uu____16331, uu____16332) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16355 = is_impl rel2  in
                           if uu____16355
                           then
                             let uu____16358 =
                               let uu____16365 =
                                 let uu____16370 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16370, FStar_Parser_AST.Nothing)  in
                               [uu____16365]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16358 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16382 =
                             let uu____16389 =
                               let uu____16396 =
                                 let uu____16403 =
                                   let uu____16410 =
                                     let uu____16415 = eta_and_annot rel2  in
                                     (uu____16415, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16416 =
                                     let uu____16423 =
                                       let uu____16430 =
                                         let uu____16435 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16435,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16436 =
                                         let uu____16443 =
                                           let uu____16448 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16448,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16443]  in
                                       uu____16430 :: uu____16436  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16423
                                      in
                                   uu____16410 :: uu____16416  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16403
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16396
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16389
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16382
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16313 with
             | (e1,uu____16486) ->
                 let e2 =
                   let uu____16488 =
                     let uu____16495 =
                       let uu____16502 =
                         let uu____16509 =
                           let uu____16514 = FStar_Parser_AST.thunk e1  in
                           (uu____16514, FStar_Parser_AST.Nothing)  in
                         [uu____16509]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16502  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16495  in
                   FStar_Parser_AST.mkApp finish uu____16488
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16531 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16532 = desugar_formula env top  in
            (uu____16532, noaqs)
        | uu____16533 ->
            let uu____16534 =
              let uu____16540 =
                let uu____16542 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16542  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16540)  in
            FStar_Errors.raise_error uu____16534 top.FStar_Parser_AST.range

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
           (fun uu____16586  ->
              match uu____16586 with
              | (a,imp) ->
                  let uu____16599 = desugar_term env a  in
                  arg_withimp_e imp uu____16599))

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
          let is_requires uu____16636 =
            match uu____16636 with
            | (t1,uu____16643) ->
                let uu____16644 =
                  let uu____16645 = unparen t1  in
                  uu____16645.FStar_Parser_AST.tm  in
                (match uu____16644 with
                 | FStar_Parser_AST.Requires uu____16647 -> true
                 | uu____16656 -> false)
             in
          let is_ensures uu____16668 =
            match uu____16668 with
            | (t1,uu____16675) ->
                let uu____16676 =
                  let uu____16677 = unparen t1  in
                  uu____16677.FStar_Parser_AST.tm  in
                (match uu____16676 with
                 | FStar_Parser_AST.Ensures uu____16679 -> true
                 | uu____16688 -> false)
             in
          let is_app head uu____16706 =
            match uu____16706 with
            | (t1,uu____16714) ->
                let uu____16715 =
                  let uu____16716 = unparen t1  in
                  uu____16716.FStar_Parser_AST.tm  in
                (match uu____16715 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16719;
                        FStar_Parser_AST.level = uu____16720;_},uu____16721,uu____16722)
                     ->
                     let uu____16723 =
                       let uu____16725 = FStar_Ident.ident_of_lid d  in
                       FStar_Ident.text_of_id uu____16725  in
                     uu____16723 = head
                 | uu____16727 -> false)
             in
          let is_smt_pat uu____16739 =
            match uu____16739 with
            | (t1,uu____16746) ->
                let uu____16747 =
                  let uu____16748 = unparen t1  in
                  uu____16748.FStar_Parser_AST.tm  in
                (match uu____16747 with
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm =
                                FStar_Parser_AST.Construct
                                (smtpat,uu____16752);
                              FStar_Parser_AST.range = uu____16753;
                              FStar_Parser_AST.level = uu____16754;_},uu____16755)::uu____16756::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16796 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16796 = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons,({
                              FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                smtpat;
                              FStar_Parser_AST.range = uu____16808;
                              FStar_Parser_AST.level = uu____16809;_},uu____16810)::uu____16811::[])
                     ->
                     (FStar_Ident.lid_equals cons FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  ->
                             let uu____16839 =
                               FStar_Ident.string_of_lid smtpat  in
                             uu____16839 = s) ["smt_pat"; "smt_pat_or"])
                 | uu____16847 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16882 = head_and_args t1  in
            match uu____16882 with
            | (head,args) ->
                (match head.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     let uu____16940 =
                       let uu____16942 = FStar_Ident.ident_of_lid lemma  in
                       FStar_Ident.text_of_id uu____16942  in
                     uu____16940 = "Lemma" ->
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
                     let thunk_ens uu____16978 =
                       match uu____16978 with
                       | (e,i) ->
                           let uu____16989 = FStar_Parser_AST.thunk e  in
                           (uu____16989, i)
                        in
                     let fail_lemma uu____17001 =
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
                           let uu____17107 =
                             let uu____17114 =
                               let uu____17121 = thunk_ens ens  in
                               [uu____17121; nil_pat]  in
                             req_true :: uu____17114  in
                           unit_tm :: uu____17107
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17168 =
                             let uu____17175 =
                               let uu____17182 = thunk_ens ens  in
                               [uu____17182; nil_pat]  in
                             req :: uu____17175  in
                           unit_tm :: uu____17168
                       | ens::smtpat::[] when
                           (((let uu____17231 = is_requires ens  in
                              Prims.op_Negation uu____17231) &&
                               (let uu____17234 = is_smt_pat ens  in
                                Prims.op_Negation uu____17234))
                              &&
                              (let uu____17237 = is_decreases ens  in
                               Prims.op_Negation uu____17237))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17239 =
                             let uu____17246 =
                               let uu____17253 = thunk_ens ens  in
                               [uu____17253; smtpat]  in
                             req_true :: uu____17246  in
                           unit_tm :: uu____17239
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17300 =
                             let uu____17307 =
                               let uu____17314 = thunk_ens ens  in
                               [uu____17314; nil_pat; dec]  in
                             req_true :: uu____17307  in
                           unit_tm :: uu____17300
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17374 =
                             let uu____17381 =
                               let uu____17388 = thunk_ens ens  in
                               [uu____17388; smtpat; dec]  in
                             req_true :: uu____17381  in
                           unit_tm :: uu____17374
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17448 =
                             let uu____17455 =
                               let uu____17462 = thunk_ens ens  in
                               [uu____17462; nil_pat; dec]  in
                             req :: uu____17455  in
                           unit_tm :: uu____17448
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17522 =
                             let uu____17529 =
                               let uu____17536 = thunk_ens ens  in
                               [uu____17536; smtpat]  in
                             req :: uu____17529  in
                           unit_tm :: uu____17522
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17601 =
                             let uu____17608 =
                               let uu____17615 = thunk_ens ens  in
                               [uu____17615; dec; smtpat]  in
                             req :: uu____17608  in
                           unit_tm :: uu____17601
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17677 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17677, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17705 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17705
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17707 =
                          let uu____17709 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17709  in
                        uu____17707 = "Tot")
                     ->
                     let uu____17712 =
                       let uu____17719 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17719, [])  in
                     (uu____17712, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17737 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17737
                        FStar_Parser_Const.prims_lid)
                       &&
                       (let uu____17739 =
                          let uu____17741 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17741  in
                        uu____17739 = "GTot")
                     ->
                     let uu____17744 =
                       let uu____17751 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17751, [])  in
                     (uu____17744, args)
                 | FStar_Parser_AST.Name l when
                     ((let uu____17769 =
                         let uu____17771 = FStar_Ident.ident_of_lid l  in
                         FStar_Ident.text_of_id uu____17771  in
                       uu____17769 = "Type") ||
                        (let uu____17775 =
                           let uu____17777 = FStar_Ident.ident_of_lid l  in
                           FStar_Ident.text_of_id uu____17777  in
                         uu____17775 = "Type0"))
                       ||
                       (let uu____17781 =
                          let uu____17783 = FStar_Ident.ident_of_lid l  in
                          FStar_Ident.text_of_id uu____17783  in
                        uu____17781 = "Effect")
                     ->
                     let uu____17786 =
                       let uu____17793 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head.FStar_Parser_AST.range
                          in
                       (uu____17793, [])  in
                     (uu____17786, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17816 when allow_type_promotion ->
                     let default_effect =
                       let uu____17818 = FStar_Options.ml_ish ()  in
                       if uu____17818
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17824 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17824
                           then
                             FStar_Errors.log_issue
                               head.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17831 =
                       let uu____17838 =
                         FStar_Ident.set_lid_range default_effect
                           head.FStar_Parser_AST.range
                          in
                       (uu____17838, [])  in
                     (uu____17831, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17861 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17880 = pre_process_comp_typ t  in
          match uu____17880 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17932 =
                    let uu____17938 =
                      let uu____17940 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17940
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17938)
                     in
                  fail uu____17932)
               else ();
               (let is_universe uu____17956 =
                  match uu____17956 with
                  | (uu____17962,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17964 = FStar_Util.take is_universe args  in
                match uu____17964 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____18023  ->
                           match uu____18023 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____18030 =
                      let uu____18045 = FStar_List.hd args1  in
                      let uu____18054 = FStar_List.tl args1  in
                      (uu____18045, uu____18054)  in
                    (match uu____18030 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18109 =
                           let is_decrease uu____18148 =
                             match uu____18148 with
                             | (t1,uu____18159) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18170;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18171;_},uu____18172::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18211 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18109 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18328  ->
                                        match uu____18328 with
                                        | (t1,uu____18338) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18347,(arg,uu____18349)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18388 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18409 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18421 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18421
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18428 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18428
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18438 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18438
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18445 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18445
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18452 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18452
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18459 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18459
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18480 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18480
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
                                                    let uu____18571 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18571
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
                                              | uu____18592 -> pat  in
                                            let uu____18593 =
                                              let uu____18604 =
                                                let uu____18615 =
                                                  let uu____18624 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18624, aq)  in
                                                [uu____18615]  in
                                              ens :: uu____18604  in
                                            req :: uu____18593
                                        | uu____18665 -> rest2
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
        let uu___2389_18700 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2389_18700.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2389_18700.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2396_18754 = b  in
             {
               FStar_Parser_AST.b = (uu___2396_18754.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2396_18754.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2396_18754.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18783 body1 =
          match uu____18783 with
          | (names,pats1) ->
              (match (names, pats1) with
               | ([],[]) -> body1
               | ([],uu____18829::uu____18830) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18848 ->
                   let names1 =
                     FStar_All.pipe_right names
                       (FStar_List.map
                          (fun i  ->
                             let uu___2415_18876 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             let uu____18877 = FStar_Ident.range_of_id i  in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2415_18876.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos = uu____18877;
                               FStar_Syntax_Syntax.vars =
                                 (uu___2415_18876.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18940 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18940))))
                      in
                   mk
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names1, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18971 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18971 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2428_18981 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2428_18981.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2428_18981.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18987 =
                     let uu____18990 =
                       let uu____18991 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18991]  in
                     no_annot_abs uu____18990 body2  in
                   FStar_All.pipe_left setpos uu____18987  in
                 let uu____19012 =
                   let uu____19013 =
                     let uu____19030 =
                       let uu____19033 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____19033
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____19035 =
                       let uu____19046 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____19046]  in
                     (uu____19030, uu____19035)  in
                   FStar_Syntax_Syntax.Tm_app uu____19013  in
                 FStar_All.pipe_left mk uu____19012)
        | uu____19085 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19150 = q (rest, pats, body)  in
              let uu____19153 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19150 uu____19153
                FStar_Parser_AST.Formula
               in
            let uu____19154 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19154 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19165 -> failwith "impossible"  in
      let uu____19169 =
        let uu____19170 = unparen f  in uu____19170.FStar_Parser_AST.tm  in
      match uu____19169 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19183,uu____19184) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19208,uu____19209) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19265 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19265
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19309 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19309
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19373 -> desugar_term env f

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
          let uu____19384 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19384)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19389 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19389)
      | FStar_Parser_AST.TVariable x ->
          let uu____19393 =
            let uu____19394 = FStar_Ident.range_of_id x  in
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None uu____19394
             in
          ((FStar_Pervasives_Native.Some x), uu____19393)
      | FStar_Parser_AST.NoName t ->
          let uu____19398 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19398)
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
      fun uu___11_19406  ->
        match uu___11_19406 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19428 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19428, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19445 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19445 with
             | (env1,a1) ->
                 let uu____19462 =
                   let uu____19469 = trans_aqual env1 imp  in
                   ((let uu___2528_19475 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2528_19475.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2528_19475.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19469)
                    in
                 (uu____19462, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19483  ->
      match uu___12_19483 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19487 =
            let uu____19488 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19488  in
          FStar_Pervasives_Native.Some uu____19487
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19516 =
        FStar_List.fold_left
          (fun uu____19549  ->
             fun b  ->
               match uu____19549 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2546_19593 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2546_19593.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2546_19593.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2546_19593.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19608 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19608 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2556_19626 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2556_19626.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2556_19626.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19627 =
                               let uu____19634 =
                                 let uu____19639 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19639)  in
                               uu____19634 :: out  in
                             (env2, uu____19627))
                    | uu____19650 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19516 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19738 =
          let uu____19739 = unparen t  in uu____19739.FStar_Parser_AST.tm  in
        match uu____19738 with
        | FStar_Parser_AST.Var lid when
            let uu____19741 = FStar_Ident.string_of_lid lid  in
            uu____19741 = "cps" -> FStar_Syntax_Syntax.CPS
        | uu____19745 ->
            let uu____19746 =
              let uu____19752 =
                let uu____19754 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19754  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19752)  in
            FStar_Errors.raise_error uu____19746 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19771) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19773) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19776 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19794 = binder_ident b  in
         FStar_Common.list_of_option uu____19794) bs
  
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
               (fun uu___13_19831  ->
                  match uu___13_19831 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19836 -> false))
           in
        let quals2 q =
          let uu____19850 =
            (let uu____19854 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19854) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19850
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19871 = FStar_Ident.range_of_lid disc_name  in
                let uu____19872 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19871;
                  FStar_Syntax_Syntax.sigquals = uu____19872;
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
            let uu____19912 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19948  ->
                        match uu____19948 with
                        | (x,uu____19959) ->
                            let field_name =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            let only_decl =
                              ((let uu____19969 =
                                  FStar_Syntax_DsEnv.current_module env  in
                                FStar_Ident.lid_equals
                                  FStar_Parser_Const.prims_lid uu____19969)
                                 || (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                ||
                                (let uu____19971 =
                                   let uu____19973 =
                                     FStar_Syntax_DsEnv.current_module env
                                      in
                                   FStar_Ident.string_of_lid uu____19973  in
                                 FStar_Options.dont_gen_projectors
                                   uu____19971)
                               in
                            let no_decl =
                              FStar_Syntax_Syntax.is_type
                                x.FStar_Syntax_Syntax.sort
                               in
                            let quals q =
                              if only_decl
                              then
                                let uu____19991 =
                                  FStar_List.filter
                                    (fun uu___14_19995  ->
                                       match uu___14_19995 with
                                       | FStar_Syntax_Syntax.Abstract  ->
                                           false
                                       | uu____19998 -> true) q
                                   in
                                FStar_Syntax_Syntax.Assumption :: uu____19991
                              else q  in
                            let quals1 =
                              let iquals1 =
                                FStar_All.pipe_right iquals
                                  (FStar_List.filter
                                     (fun uu___15_20013  ->
                                        match uu___15_20013 with
                                        | FStar_Syntax_Syntax.NoExtract  ->
                                            true
                                        | FStar_Syntax_Syntax.Abstract  ->
                                            true
                                        | FStar_Syntax_Syntax.Private  ->
                                            true
                                        | uu____20018 -> false))
                                 in
                              quals (FStar_Syntax_Syntax.OnlyName ::
                                (FStar_Syntax_Syntax.Projector
                                   (lid, (x.FStar_Syntax_Syntax.ppname))) ::
                                iquals1)
                               in
                            let decl =
                              let uu____20021 =
                                FStar_Ident.range_of_lid field_name  in
                              {
                                FStar_Syntax_Syntax.sigel =
                                  (FStar_Syntax_Syntax.Sig_declare_typ
                                     (field_name, [],
                                       FStar_Syntax_Syntax.tun));
                                FStar_Syntax_Syntax.sigrng = uu____20021;
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
                                 let uu____20028 =
                                   FStar_All.pipe_right quals1
                                     (FStar_List.contains
                                        FStar_Syntax_Syntax.Abstract)
                                    in
                                 if uu____20028
                                 then
                                   FStar_Syntax_Syntax.Delta_abstract
                                     (FStar_Syntax_Syntax.Delta_equational_at_level
                                        Prims.int_one)
                                 else
                                   FStar_Syntax_Syntax.Delta_equational_at_level
                                     Prims.int_one
                                  in
                               let lb =
                                 let uu____20039 =
                                   let uu____20044 =
                                     FStar_Syntax_Syntax.lid_as_fv field_name
                                       dd FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____20044  in
                                 {
                                   FStar_Syntax_Syntax.lbname = uu____20039;
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
                                 let uu____20048 =
                                   let uu____20049 =
                                     let uu____20056 =
                                       let uu____20059 =
                                         let uu____20060 =
                                           FStar_All.pipe_right
                                             lb.FStar_Syntax_Syntax.lbname
                                             FStar_Util.right
                                            in
                                         FStar_All.pipe_right uu____20060
                                           (fun fv  ->
                                              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                          in
                                       [uu____20059]  in
                                     ((false, [lb]), uu____20056)  in
                                   FStar_Syntax_Syntax.Sig_let uu____20049
                                    in
                                 {
                                   FStar_Syntax_Syntax.sigel = uu____20048;
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
            FStar_All.pipe_right uu____19912 FStar_List.flatten
  
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
            (lid,uu____20109,t,uu____20111,n,uu____20113) when
            let uu____20120 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20120 ->
            let uu____20122 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20122 with
             | (formals,uu____20132) ->
                 (match formals with
                  | [] -> []
                  | uu____20145 ->
                      let filter_records uu___16_20153 =
                        match uu___16_20153 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20156,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20168 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20170 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20170 with
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
                      let uu____20182 = FStar_Util.first_N n formals  in
                      (match uu____20182 with
                       | (uu____20211,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20245 -> []
  
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
                        let uu____20339 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20339
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20363 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20363
                        then
                          let uu____20369 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20369
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20373 =
                          let uu____20378 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20378  in
                        let uu____20379 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20385 =
                              let uu____20388 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20388  in
                            FStar_Syntax_Util.arrow typars uu____20385
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20393 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20373;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20379;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20393;
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
          let tycon_id uu___17_20447 =
            match uu___17_20447 with
            | FStar_Parser_AST.TyconAbstract (id,uu____20449,uu____20450) ->
                id
            | FStar_Parser_AST.TyconAbbrev
                (id,uu____20460,uu____20461,uu____20462) -> id
            | FStar_Parser_AST.TyconRecord
                (id,uu____20472,uu____20473,uu____20474) -> id
            | FStar_Parser_AST.TyconVariant
                (id,uu____20496,uu____20497,uu____20498) -> id
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20536) ->
                let uu____20537 =
                  let uu____20538 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20538  in
                let uu____20539 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20537 uu____20539
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20541 =
                  let uu____20542 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20542  in
                let uu____20543 = FStar_Ident.range_of_id x  in
                FStar_Parser_AST.mk_term uu____20541 uu____20543
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20545) ->
                let uu____20546 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20546 FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                let uu____20548 = FStar_Ident.range_of_id a  in
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  uu____20548 FStar_Parser_AST.Type_level
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
              | uu____20578 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20586 =
                     let uu____20587 =
                       let uu____20594 = binder_to_term b  in
                       (out, uu____20594, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20587  in
                   FStar_Parser_AST.mk_term uu____20586
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20606 =
            match uu___18_20606 with
            | FStar_Parser_AST.TyconRecord (id,parms,kopt,fields) ->
                let constrName =
                  let uu____20638 =
                    let uu____20644 =
                      let uu____20646 = FStar_Ident.text_of_id id  in
                      Prims.op_Hat "Mk" uu____20646  in
                    let uu____20649 = FStar_Ident.range_of_id id  in
                    (uu____20644, uu____20649)  in
                  FStar_Ident.mk_ident uu____20638  in
                let mfields =
                  FStar_List.map
                    (fun uu____20662  ->
                       match uu____20662 with
                       | (x,t) ->
                           let uu____20669 = FStar_Ident.range_of_id x  in
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t)) uu____20669
                             FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20671 =
                    let uu____20672 =
                      let uu____20673 = FStar_Ident.lid_of_ids [id]  in
                      FStar_Parser_AST.Var uu____20673  in
                    let uu____20674 = FStar_Ident.range_of_id id  in
                    FStar_Parser_AST.mk_term uu____20672 uu____20674
                      FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20671 parms  in
                let constrTyp =
                  let uu____20676 = FStar_Ident.range_of_id id  in
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    uu____20676 FStar_Parser_AST.Type_level
                   in
                let names =
                  let uu____20682 = binder_idents parms  in id :: uu____20682
                   in
                (FStar_List.iter
                   (fun uu____20696  ->
                      match uu____20696 with
                      | (f,uu____20702) ->
                          let uu____20703 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names
                             in
                          if uu____20703
                          then
                            let uu____20708 =
                              let uu____20714 =
                                let uu____20716 = FStar_Ident.text_of_id f
                                   in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20716
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20714)
                               in
                            let uu____20720 = FStar_Ident.range_of_id f  in
                            FStar_Errors.raise_error uu____20708 uu____20720
                          else ()) fields;
                 (let uu____20723 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20723)))
            | uu____20777 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20817 =
            match uu___19_20817 with
            | FStar_Parser_AST.TyconAbstract (id,binders,kopt) ->
                let uu____20841 = typars_of_binders _env binders  in
                (match uu____20841 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20877 =
                         let uu____20878 =
                           let uu____20879 = FStar_Ident.lid_of_ids [id]  in
                           FStar_Parser_AST.Var uu____20879  in
                         let uu____20880 = FStar_Ident.range_of_id id  in
                         FStar_Parser_AST.mk_term uu____20878 uu____20880
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20877 binders  in
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
                     let uu____20889 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20889 with
                      | (_env1,uu____20906) ->
                          let uu____20913 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20913 with
                           | (_env2,uu____20930) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20937 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20980 =
              FStar_List.fold_left
                (fun uu____21014  ->
                   fun uu____21015  ->
                     match (uu____21014, uu____21015) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21084 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21084 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20980 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21175 =
                      let uu____21176 = FStar_Ident.range_of_id id  in
                      tm_type_z uu____21176  in
                    FStar_Pervasives_Native.Some uu____21175
                | uu____21177 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id, bs, kopt1)  in
              let uu____21185 = desugar_abstract_tc quals env [] tc  in
              (match uu____21185 with
               | (uu____21198,uu____21199,se,uu____21201) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21204,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21223 =
                                 let uu____21225 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21225  in
                               if uu____21223
                               then
                                 let uu____21228 =
                                   let uu____21234 =
                                     let uu____21236 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21236
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21234)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21228
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
                           | uu____21249 ->
                               let uu____21250 =
                                 let uu____21257 =
                                   let uu____21258 =
                                     let uu____21273 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21273)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21258
                                    in
                                 FStar_Syntax_Syntax.mk uu____21257  in
                               uu____21250 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2833_21286 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2833_21286.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2833_21286.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2833_21286.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2833_21286.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21287 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t))::[] ->
              let uu____21302 = typars_of_binders env binders  in
              (match uu____21302 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21336 =
                           FStar_Util.for_some
                             (fun uu___20_21339  ->
                                match uu___20_21339 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21342 -> false) quals
                            in
                         if uu____21336
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21350 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21350
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21355 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21361  ->
                               match uu___21_21361 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21364 -> false))
                        in
                     if uu____21355
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id  in
                   let se =
                     let uu____21378 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21378
                     then
                       let uu____21384 =
                         let uu____21391 =
                           let uu____21392 = unparen t  in
                           uu____21392.FStar_Parser_AST.tm  in
                         match uu____21391 with
                         | FStar_Parser_AST.Construct (head,args) ->
                             let uu____21413 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21443)::args_rev ->
                                   let uu____21455 =
                                     let uu____21456 = unparen last_arg  in
                                     uu____21456.FStar_Parser_AST.tm  in
                                   (match uu____21455 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21484 -> ([], args))
                               | uu____21493 -> ([], args)  in
                             (match uu____21413 with
                              | (cattributes,args1) ->
                                  let uu____21532 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21532))
                         | uu____21543 -> (t, [])  in
                       match uu____21384 with
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
                                  (fun uu___22_21566  ->
                                     match uu___22_21566 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21569 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21577)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21597 = tycon_record_as_variant trec  in
              (match uu____21597 with
               | (t,fs) ->
                   let uu____21614 =
                     let uu____21617 =
                       let uu____21618 =
                         let uu____21627 =
                           let uu____21630 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21630  in
                         (uu____21627, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21618  in
                     uu____21617 :: quals  in
                   desugar_tycon env d uu____21614 [t])
          | uu____21635::uu____21636 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21794 = et  in
                match uu____21794 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____22004 ->
                         let trec = tc  in
                         let uu____22024 = tycon_record_as_variant trec  in
                         (match uu____22024 with
                          | (t,fs) ->
                              let uu____22080 =
                                let uu____22083 =
                                  let uu____22084 =
                                    let uu____22093 =
                                      let uu____22096 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22096  in
                                    (uu____22093, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22084
                                   in
                                uu____22083 :: quals1  in
                              collect_tcs uu____22080 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id,binders,kopt,constructors) ->
                         let uu____22174 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22174 with
                          | (env2,uu____22231,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id,binders,kopt,t) ->
                         let uu____22368 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id, binders, kopt))
                            in
                         (match uu____22368 with
                          | (env2,uu____22425,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22541 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22587 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22587 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_23039  ->
                             match uu___24_23039 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id,uvs,tpars,k,uu____23093,uu____23094);
                                    FStar_Syntax_Syntax.sigrng = uu____23095;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23096;
                                    FStar_Syntax_Syntax.sigmeta = uu____23097;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23098;
                                    FStar_Syntax_Syntax.sigopts = uu____23099;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23161 =
                                     typars_of_binders env1 binders  in
                                   match uu____23161 with
                                   | (env2,tpars1) ->
                                       let uu____23188 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23188 with
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
                                 let uu____23217 =
                                   let uu____23228 =
                                     mk_typ_abbrev env1 d id uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id] quals1 rng
                                      in
                                   ([], uu____23228)  in
                                 [uu____23217]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs,tpars,k,mutuals1,uu____23264);
                                    FStar_Syntax_Syntax.sigrng = uu____23265;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23267;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23268;
                                    FStar_Syntax_Syntax.sigopts = uu____23269;_},constrs,tconstr,quals1)
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
                                 let uu____23360 = push_tparams env1 tpars
                                    in
                                 (match uu____23360 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23419  ->
                                             match uu____23419 with
                                             | (x,uu____23431) ->
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
                                        let uu____23442 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23442
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23465 =
                                        let uu____23484 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23561  ->
                                                  match uu____23561 with
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
                                                        let uu____23604 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23604
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
                                                                uu___23_23615
                                                                 ->
                                                                match uu___23_23615
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23627
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23635 =
                                                        let uu____23646 =
                                                          let uu____23647 =
                                                            let uu____23648 =
                                                              let uu____23664
                                                                =
                                                                let uu____23665
                                                                  =
                                                                  let uu____23668
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23668
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23665
                                                                 in
                                                              (name, univs,
                                                                uu____23664,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23648
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23647;
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
                                                        (tps, uu____23646)
                                                         in
                                                      (name, uu____23635)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23484
                                         in
                                      (match uu____23465 with
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
                             | uu____23800 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23881  ->
                             match uu____23881 with | (uu____23892,se) -> se))
                      in
                   let uu____23906 =
                     let uu____23913 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23913 rng
                      in
                   (match uu____23906 with
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
                               (fun uu____23958  ->
                                  match uu____23958 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____24006,tps,k,uu____24009,constrs)
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
                                      let uu____24030 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____24045 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24062,uu____24063,uu____24064,uu____24065,uu____24066)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24073
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____24045
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24077 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24084  ->
                                                          match uu___25_24084
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24086 ->
                                                              true
                                                          | uu____24096 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24077))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____24030
                                  | uu____24098 -> []))
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
      let uu____24135 =
        FStar_List.fold_left
          (fun uu____24170  ->
             fun b  ->
               match uu____24170 with
               | (env1,binders1) ->
                   let uu____24214 = desugar_binder env1 b  in
                   (match uu____24214 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24237 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24237 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24290 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24135 with
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
          let uu____24394 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24401  ->
                    match uu___26_24401 with
                    | FStar_Syntax_Syntax.Reflectable uu____24403 -> true
                    | uu____24405 -> false))
             in
          if uu____24394
          then
            let monad_env =
              let uu____24409 = FStar_Ident.ident_of_lid effect_name  in
              FStar_Syntax_DsEnv.enter_monad_scope env uu____24409  in
            let reflect_lid =
              let uu____24411 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24411
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
        let warn1 uu____24462 =
          if warn
          then
            let uu____24464 =
              let uu____24470 =
                let uu____24472 = FStar_Ident.string_of_lid head  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24472
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24470)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24464
          else ()  in
        let uu____24478 = FStar_Syntax_Util.head_and_args at  in
        match uu____24478 with
        | (hd,args) ->
            let uu____24531 =
              let uu____24532 = FStar_Syntax_Subst.compress hd  in
              uu____24532.FStar_Syntax_Syntax.n  in
            (match uu____24531 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24576)::[] ->
                      let uu____24601 =
                        let uu____24606 =
                          let uu____24615 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24615 a1  in
                        uu____24606 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24601 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24638 =
                             let uu____24644 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24644  in
                           (uu____24638, true)
                       | uu____24659 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24675 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24697 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24814 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24814 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24863 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24863 with | (res1,uu____24885) -> rebind res1 true)
  
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
        | uu____25212 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25270 = get_fail_attr1 warn at  in
             comb uu____25270 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25305 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25305 with
        | FStar_Pervasives_Native.None  ->
            let uu____25308 =
              let uu____25314 =
                let uu____25316 =
                  let uu____25318 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25318 " not found"  in
                Prims.op_Hat "Effect name " uu____25316  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25314)  in
            FStar_Errors.raise_error uu____25308 r
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
                    let uu____25474 = desugar_binders monad_env eff_binders
                       in
                    match uu____25474 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25513 =
                            let uu____25522 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25522  in
                          FStar_List.length uu____25513  in
                        (if is_layered && (num_indices <= Prims.int_one)
                         then
                           (let uu____25540 =
                              let uu____25546 =
                                let uu____25548 =
                                  let uu____25550 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25550
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25548  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25546)
                               in
                            FStar_Errors.raise_error uu____25540
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
                                (uu____25618,uu____25619,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25621,uu____25622,uu____25623))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25638 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25641 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25653 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25653 mandatory_members)
                              eff_decls
                             in
                          match uu____25641 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25672 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25701  ->
                                        fun decl  ->
                                          match uu____25701 with
                                          | (env2,out) ->
                                              let uu____25721 =
                                                desugar_decl env2 decl  in
                                              (match uu____25721 with
                                               | (env3,ses) ->
                                                   let uu____25734 =
                                                     let uu____25737 =
                                                       FStar_List.hd ses  in
                                                     uu____25737 :: out  in
                                                   (env3, uu____25734)))
                                     (env1, []))
                                 in
                              (match uu____25672 with
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
                                                 (uu____25783,uu____25784,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25787,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25788,(def,uu____25790)::
                                                        (cps_type,uu____25792)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25793;
                                                     FStar_Parser_AST.level =
                                                       uu____25794;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25827 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25827 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25859 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25860 =
                                                        let uu____25861 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25861
                                                         in
                                                      let uu____25868 =
                                                        let uu____25869 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25869
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25859;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25860;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25868
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25876,uu____25877,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25880,defn))::[])
                                                 when for_free || is_layered
                                                 ->
                                                 let uu____25896 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25896 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25928 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25929 =
                                                        let uu____25930 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25930
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25928;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25929;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25937 ->
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
                                       let uu____25956 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25956
                                        in
                                     let uu____25958 =
                                       let uu____25959 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25959
                                        in
                                     ([], uu____25958)  in
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
                                       let uu____25981 =
                                         let uu____25982 =
                                           let uu____25985 = lookup "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25985
                                            in
                                         let uu____25987 =
                                           let uu____25990 = lookup "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25990
                                            in
                                         let uu____25992 =
                                           let uu____25995 = lookup "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25995
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
                                             uu____25982;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25987;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25992
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25981
                                     else
                                       if is_layered
                                       then
                                         (let to_comb uu____26029 =
                                            match uu____26029 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26076 =
                                            let uu____26077 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26079 =
                                              let uu____26084 = lookup "repr"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26084 to_comb
                                               in
                                            let uu____26102 =
                                              let uu____26107 =
                                                lookup "return"  in
                                              FStar_All.pipe_right
                                                uu____26107 to_comb
                                               in
                                            let uu____26125 =
                                              let uu____26130 = lookup "bind"
                                                 in
                                              FStar_All.pipe_right
                                                uu____26130 to_comb
                                               in
                                            let uu____26148 =
                                              let uu____26153 =
                                                lookup "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26153 to_comb
                                               in
                                            let uu____26171 =
                                              let uu____26176 =
                                                lookup "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26176 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26077;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26079;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26102;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26125;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26148;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26171
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26076)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26199  ->
                                                 match uu___27_26199 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26202 -> true
                                                 | uu____26204 -> false)
                                              qualifiers
                                             in
                                          let uu____26206 =
                                            let uu____26207 =
                                              lookup "return_wp"  in
                                            let uu____26209 =
                                              lookup "bind_wp"  in
                                            let uu____26211 =
                                              lookup "stronger"  in
                                            let uu____26213 =
                                              lookup "if_then_else"  in
                                            let uu____26215 = lookup "ite_wp"
                                               in
                                            let uu____26217 =
                                              lookup "close_wp"  in
                                            let uu____26219 =
                                              lookup "trivial"  in
                                            let uu____26221 =
                                              if rr
                                              then
                                                let uu____26227 =
                                                  lookup "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26227
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26231 =
                                              if rr
                                              then
                                                let uu____26237 =
                                                  lookup "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26237
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26241 =
                                              if rr
                                              then
                                                let uu____26247 =
                                                  lookup "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26247
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26207;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26209;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26211;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26213;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26215;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26217;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26219;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26221;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26231;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26241
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26206)
                                      in
                                   let sigel =
                                     let uu____26252 =
                                       let uu____26253 =
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
                                           uu____26253
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26252
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
                                               let uu____26270 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26270) env3)
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
                let uu____26293 = desugar_binders env1 eff_binders  in
                match uu____26293 with
                | (env2,binders) ->
                    let uu____26330 =
                      let uu____26341 = head_and_args defn  in
                      match uu____26341 with
                      | (head,args) ->
                          let lid =
                            match head.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26378 ->
                                let uu____26379 =
                                  let uu____26385 =
                                    let uu____26387 =
                                      let uu____26389 =
                                        FStar_Parser_AST.term_to_string head
                                         in
                                      Prims.op_Hat uu____26389 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26387  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26385)
                                   in
                                FStar_Errors.raise_error uu____26379
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26395 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26425)::args_rev ->
                                let uu____26437 =
                                  let uu____26438 = unparen last_arg  in
                                  uu____26438.FStar_Parser_AST.tm  in
                                (match uu____26437 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26466 -> ([], args))
                            | uu____26475 -> ([], args)  in
                          (match uu____26395 with
                           | (cattributes,args1) ->
                               let uu____26518 = desugar_args env2 args1  in
                               let uu____26519 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26518, uu____26519))
                       in
                    (match uu____26330 with
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
                          (let uu____26559 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26559 with
                           | (ed_binders,uu____26573,ed_binders_opening) ->
                               let sub' shift_n uu____26592 =
                                 match uu____26592 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26607 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26607 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26611 =
                                       let uu____26612 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26612)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26611
                                  in
                               let sub = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26633 =
                                   sub ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26634 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26635 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26651 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26652 =
                                          let uu____26653 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26653
                                           in
                                        let uu____26668 =
                                          let uu____26669 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26669
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26651;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26652;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26668
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
                                     uu____26633;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26634;
                                   FStar_Syntax_Syntax.actions = uu____26635;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26685 =
                                   let uu____26688 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26688 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26685;
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
                                           let uu____26703 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26703) env3)
                                  in
                               let env5 =
                                 let uu____26705 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26705
                                 then
                                   let reflect_lid =
                                     let uu____26712 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26712
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
             let uu____26745 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26745) ats
         in
      let env0 =
        let uu____26766 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26766 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26781 =
        let uu____26788 = get_fail_attr false attrs  in
        match uu____26788 with
        | FStar_Pervasives_Native.Some (expected_errs,lax) ->
            let d1 =
              let uu___3388_26825 = d  in
              {
                FStar_Parser_AST.d = (uu___3388_26825.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3388_26825.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3388_26825.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26826 =
              FStar_Errors.catch_errors
                (fun uu____26844  ->
                   FStar_Options.with_saved_options
                     (fun uu____26850  -> desugar_decl_noattrs env d1))
               in
            (match uu____26826 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3403_26910 = se  in
                             let uu____26911 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3403_26910.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3403_26910.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3403_26910.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3403_26910.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____26911;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3403_26910.FStar_Syntax_Syntax.sigopts)
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
                        (let uu____26964 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____26964 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____27013 =
                                 let uu____27019 =
                                   let uu____27021 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____27024 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____27027 =
                                     FStar_Util.string_of_int e  in
                                   let uu____27029 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____27031 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____27021 uu____27024 uu____27027
                                     uu____27029 uu____27031
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____27019)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____27013);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26781 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27069;
                FStar_Syntax_Syntax.sigrng = uu____27070;
                FStar_Syntax_Syntax.sigquals = uu____27071;
                FStar_Syntax_Syntax.sigmeta = uu____27072;
                FStar_Syntax_Syntax.sigattrs = uu____27073;
                FStar_Syntax_Syntax.sigopts = uu____27074;_}::[] ->
                let uu____27087 =
                  let uu____27090 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27090  in
                FStar_All.pipe_right uu____27087
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27098 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27098))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27111;
                FStar_Syntax_Syntax.sigrng = uu____27112;
                FStar_Syntax_Syntax.sigquals = uu____27113;
                FStar_Syntax_Syntax.sigmeta = uu____27114;
                FStar_Syntax_Syntax.sigattrs = uu____27115;
                FStar_Syntax_Syntax.sigopts = uu____27116;_}::uu____27117 ->
                let uu____27142 =
                  let uu____27145 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27145  in
                FStar_All.pipe_right uu____27142
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27153 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27153))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27169;
                FStar_Syntax_Syntax.sigquals = uu____27170;
                FStar_Syntax_Syntax.sigmeta = uu____27171;
                FStar_Syntax_Syntax.sigattrs = uu____27172;
                FStar_Syntax_Syntax.sigopts = uu____27173;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27194 -> []  in
          let attrs1 =
            let uu____27200 = val_attrs sigelts  in
            FStar_List.append attrs uu____27200  in
          let uu____27203 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3463_27207 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3463_27207.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3463_27207.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3463_27207.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3463_27207.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3463_27207.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27203)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27214 = desugar_decl_aux env d  in
      match uu____27214 with
      | (env1,ses) ->
          let uu____27225 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27225)

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
          let uu____27257 = FStar_Syntax_DsEnv.iface env  in
          if uu____27257
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27272 =
               let uu____27274 =
                 let uu____27276 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27277 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27276
                   uu____27277
                  in
               Prims.op_Negation uu____27274  in
             if uu____27272
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27291 =
                  let uu____27293 =
                    let uu____27295 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27295 lid  in
                  Prims.op_Negation uu____27293  in
                if uu____27291
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27309 =
                     let uu____27311 =
                       let uu____27313 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27313
                         lid
                        in
                     Prims.op_Negation uu____27311  in
                   if uu____27309
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27331 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27331, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27360)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27379 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27388 =
            let uu____27393 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27393 tcs  in
          (match uu____27388 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27410 =
                   let uu____27411 =
                     let uu____27418 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27418  in
                   [uu____27411]  in
                 let uu____27431 =
                   let uu____27434 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27437 =
                     let uu____27448 =
                       let uu____27457 =
                         let uu____27458 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27458  in
                       FStar_Syntax_Syntax.as_arg uu____27457  in
                     [uu____27448]  in
                   FStar_Syntax_Util.mk_app uu____27434 uu____27437  in
                 FStar_Syntax_Util.abs uu____27410 uu____27431
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27498,id))::uu____27500 ->
                       FStar_Pervasives_Native.Some id
                   | uu____27503::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27507 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27507 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id ->
                     let uu____27513 = FStar_Syntax_DsEnv.qualify env1 id  in
                     [uu____27513]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27534) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27544,uu____27545,uu____27546,uu____27547,uu____27548)
                     ->
                     let uu____27557 =
                       let uu____27558 =
                         let uu____27559 =
                           let uu____27566 = mkclass lid  in
                           (meths, uu____27566)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27559  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27558;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27557]
                 | uu____27569 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27603;
                    FStar_Parser_AST.prange = uu____27604;_},uu____27605)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27615;
                    FStar_Parser_AST.prange = uu____27616;_},uu____27617)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27633;
                         FStar_Parser_AST.prange = uu____27634;_},uu____27635);
                    FStar_Parser_AST.prange = uu____27636;_},uu____27637)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27659;
                         FStar_Parser_AST.prange = uu____27660;_},uu____27661);
                    FStar_Parser_AST.prange = uu____27662;_},uu____27663)::[]
                   -> false
               | (p,uu____27692)::[] ->
                   let uu____27701 = is_app_pattern p  in
                   Prims.op_Negation uu____27701
               | uu____27703 -> false)
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
            let uu____27778 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27778 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27791 =
                     let uu____27792 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27792.FStar_Syntax_Syntax.n  in
                   match uu____27791 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27802) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27833 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27858  ->
                                match uu____27858 with
                                | (qs,ats) ->
                                    let uu____27885 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27885 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27833 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27939::uu____27940 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27943 -> val_quals  in
                            let quals2 =
                              let uu____27947 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27980  ->
                                        match uu____27980 with
                                        | (uu____27994,(uu____27995,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27947
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____28015 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____28015
                              then
                                let uu____28021 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3640_28036 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3642_28038 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3642_28038.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3642_28038.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3640_28036.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3640_28036.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3640_28036.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3640_28036.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3640_28036.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3640_28036.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____28021)
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
                   | uu____28063 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28071 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28090 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28071 with
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
                       let uu___3665_28127 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3665_28127.FStar_Parser_AST.prange)
                       }
                   | uu____28134 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3669_28141 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3669_28141.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3669_28141.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28157 =
                     let uu____28158 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28158  in
                   FStar_Parser_AST.mk_term uu____28157
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28182 id_opt =
                   match uu____28182 with
                   | (env1,ses) ->
                       let uu____28204 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id ->
                             let lid = FStar_Ident.lid_of_ids [id]  in
                             let branch =
                               let uu____28216 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28216
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28218 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28218
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
                               let uu____28224 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id, FStar_Pervasives_Native.None))
                                 uu____28224
                                in
                             let bv_pat1 =
                               let uu____28228 = FStar_Ident.range_of_id id
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____28228
                                in
                             (bv_pat1, branch)
                          in
                       (match uu____28204 with
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
                            let uu____28289 = desugar_decl env1 id_decl  in
                            (match uu____28289 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28325 id =
                   match uu____28325 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id)
                    in
                 let build_coverage_check uu____28364 =
                   match uu____28364 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28388 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28388 FStar_Util.set_elements
                    in
                 let uu____28395 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28398 = is_var_pattern pat  in
                      Prims.op_Negation uu____28398)
                    in
                 if uu____28395
                 then build_coverage_check main_let
                 else FStar_List.fold_left build_projection main_let bvs)
      | FStar_Parser_AST.Main t ->
          let e = desugar_term env t  in
          let se =
            {
              FStar_Syntax_Syntax.sigel = (FStar_Syntax_Syntax.Sig_main e);
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          (env, [se])
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
            let uu____28422 = close_fun env t  in
            desugar_term env uu____28422  in
          let quals1 =
            let uu____28426 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28426
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28438 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28438;
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
                let uu____28451 =
                  let uu____28460 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28460]  in
                let uu____28479 =
                  let uu____28482 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28482
                   in
                FStar_Syntax_Util.arrow uu____28451 uu____28479
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
          uu____28545) ->
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
          let uu____28562 =
            let uu____28564 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28564  in
          if uu____28562
          then
            let uu____28571 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28589 =
                    let uu____28592 =
                      let uu____28593 = desugar_term env t  in
                      ([], uu____28593)  in
                    FStar_Pervasives_Native.Some uu____28592  in
                  (uu____28589, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28606 =
                    let uu____28609 =
                      let uu____28610 = desugar_term env wp  in
                      ([], uu____28610)  in
                    FStar_Pervasives_Native.Some uu____28609  in
                  let uu____28617 =
                    let uu____28620 =
                      let uu____28621 = desugar_term env t  in
                      ([], uu____28621)  in
                    FStar_Pervasives_Native.Some uu____28620  in
                  (uu____28606, uu____28617)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28633 =
                    let uu____28636 =
                      let uu____28637 = desugar_term env t  in
                      ([], uu____28637)  in
                    FStar_Pervasives_Native.Some uu____28636  in
                  (FStar_Pervasives_Native.None, uu____28633)
               in
            (match uu____28571 with
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
                   let uu____28671 =
                     let uu____28674 =
                       let uu____28675 = desugar_term env t  in
                       ([], uu____28675)  in
                     FStar_Pervasives_Native.Some uu____28674  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28671
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
             | uu____28682 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28695 =
            let uu____28696 =
              let uu____28697 =
                let uu____28698 =
                  let uu____28709 =
                    let uu____28710 = desugar_term env bind  in
                    ([], uu____28710)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28709,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28698  in
              {
                FStar_Syntax_Syntax.sigel = uu____28697;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28696]  in
          (env, uu____28695)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28729 =
              let uu____28730 =
                let uu____28737 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28737, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28730  in
            {
              FStar_Syntax_Syntax.sigel = uu____28729;
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
      let uu____28764 =
        FStar_List.fold_left
          (fun uu____28784  ->
             fun d  ->
               match uu____28784 with
               | (env1,sigelts) ->
                   let uu____28804 = desugar_decl env1 d  in
                   (match uu____28804 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28764 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28895) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28899;
               FStar_Syntax_Syntax.exports = uu____28900;
               FStar_Syntax_Syntax.is_interface = uu____28901;_},FStar_Parser_AST.Module
             (current_lid,uu____28903)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28912) ->
              let uu____28915 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28915
           in
        let uu____28920 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28962 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28962, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28984 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28984, mname, decls, false)
           in
        match uu____28920 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____29026 = desugar_decls env2 decls  in
            (match uu____29026 with
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
          let uu____29094 =
            (FStar_Options.interactive ()) &&
              (let uu____29097 =
                 let uu____29099 =
                   let uu____29101 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29101  in
                 FStar_Util.get_file_extension uu____29099  in
               FStar_List.mem uu____29097 ["fsti"; "fsi"])
             in
          if uu____29094 then as_interface m else m  in
        let uu____29115 = desugar_modul_common curmod env m1  in
        match uu____29115 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29137 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29137, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29159 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29159 with
      | (env1,modul,pop_when_done) ->
          let uu____29176 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29176 with
           | (env2,modul1) ->
               ((let uu____29188 =
                   let uu____29190 =
                     FStar_Ident.string_of_lid
                       modul1.FStar_Syntax_Syntax.name
                      in
                   FStar_Options.dump_module uu____29190  in
                 if uu____29188
                 then
                   let uu____29193 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29193
                 else ());
                (let uu____29198 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29198, modul1))))
  
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
        (fun uu____29248  ->
           let uu____29249 = desugar_modul env modul  in
           match uu____29249 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29287  ->
           let uu____29288 = desugar_decls env decls  in
           match uu____29288 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29339  ->
             let uu____29340 = desugar_partial_modul modul env a_modul  in
             match uu____29340 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29435 ->
                  let t =
                    let uu____29445 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29445  in
                  let uu____29458 =
                    let uu____29459 = FStar_Syntax_Subst.compress t  in
                    uu____29459.FStar_Syntax_Syntax.n  in
                  (match uu____29458 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29471,uu____29472)
                       -> bs1
                   | uu____29497 -> failwith "Impossible")
               in
            let uu____29507 =
              let uu____29514 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29514
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29507 with
            | (binders,uu____29516,binders_opening) ->
                let erase_term t =
                  let uu____29524 =
                    let uu____29525 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29525  in
                  FStar_Syntax_Subst.close binders uu____29524  in
                let erase_tscheme uu____29543 =
                  match uu____29543 with
                  | (us,t) ->
                      let t1 =
                        let uu____29563 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29563 t  in
                      let uu____29566 =
                        let uu____29567 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29567  in
                      ([], uu____29566)
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
                    | uu____29590 ->
                        let bs =
                          let uu____29600 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29600  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29640 =
                          let uu____29641 =
                            let uu____29644 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29644  in
                          uu____29641.FStar_Syntax_Syntax.n  in
                        (match uu____29640 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29646,uu____29647) -> bs1
                         | uu____29672 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29680 =
                      let uu____29681 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29681  in
                    FStar_Syntax_Subst.close binders uu____29680  in
                  let uu___3965_29682 = action  in
                  let uu____29683 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29684 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3965_29682.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3965_29682.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29683;
                    FStar_Syntax_Syntax.action_typ = uu____29684
                  }  in
                let uu___3967_29685 = ed  in
                let uu____29686 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29687 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29688 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29689 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3967_29685.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3967_29685.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29686;
                  FStar_Syntax_Syntax.signature = uu____29687;
                  FStar_Syntax_Syntax.combinators = uu____29688;
                  FStar_Syntax_Syntax.actions = uu____29689;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3967_29685.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3974_29705 = se  in
                  let uu____29706 =
                    let uu____29707 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29707  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29706;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3974_29705.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3974_29705.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3974_29705.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3974_29705.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3974_29705.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29709 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29710 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29710 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29727 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt uu____29727
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29729 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29729)
  