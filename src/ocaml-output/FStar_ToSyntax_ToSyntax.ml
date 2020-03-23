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
      fun branch1  ->
        FStar_All.pipe_right annotated_pats
          (FStar_List.map
             (fun uu____103  ->
                match uu____103 with
                | (pat,annots) ->
                    let branch2 =
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
                                 let branch2 =
                                   let uu____182 =
                                     let uu____183 =
                                       FStar_Syntax_Syntax.mk_binder bv  in
                                     [uu____183]  in
                                   FStar_Syntax_Subst.close uu____182 branch1
                                    in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      ((false, [lb]), branch2))
                                   FStar_Pervasives_Native.None
                                   br.FStar_Syntax_Syntax.pos) branch1 annots
                       in
                    FStar_Syntax_Util.branch (pat, when_opt, branch2)))
  
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
  'Auu____289 .
    FStar_Parser_AST.imp ->
      'Auu____289 ->
        ('Auu____289 * FStar_Syntax_Syntax.arg_qualifier
          FStar_Pervasives_Native.option)
  = fun imp  -> fun t  -> (t, (as_imp imp)) 
let arg_withimp_t :
  'Auu____315 .
    FStar_Parser_AST.imp ->
      'Auu____315 ->
        ('Auu____315 * FStar_Syntax_Syntax.arg_qualifier
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
      | FStar_Parser_AST.App (head1,uu____436,uu____437) ->
          is_comp_type env head1
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
              let warn_if_deprecated attrs1 =
                FStar_List.iter
                  (fun a  ->
                     match a.FStar_Syntax_Syntax.n with
                     | FStar_Syntax_Syntax.Tm_app
                         ({
                            FStar_Syntax_Syntax.n =
                              FStar_Syntax_Syntax.Tm_fvar fv;
                            FStar_Syntax_Syntax.pos = uu____551;
                            FStar_Syntax_Syntax.vars = uu____552;_},args)
                         when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____580 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____580 " is deprecated"  in
                         let msg1 =
                           if (FStar_List.length args) > Prims.int_zero
                           then
                             let uu____596 =
                               let uu____597 =
                                 let uu____600 = FStar_List.hd args  in
                                 FStar_Pervasives_Native.fst uu____600  in
                               uu____597.FStar_Syntax_Syntax.n  in
                             match uu____596 with
                             | FStar_Syntax_Syntax.Tm_constant
                                 (FStar_Const.Const_string (s,uu____623))
                                 when
                                 Prims.op_Negation
                                   ((FStar_Util.trim_string s) = "")
                                 ->
                                 Prims.op_Hat msg
                                   (Prims.op_Hat ", use "
                                      (Prims.op_Hat s " instead"))
                             | uu____630 -> msg
                           else msg  in
                         let uu____633 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____633
                           (FStar_Errors.Warning_DeprecatedDefinition, msg1)
                     | FStar_Syntax_Syntax.Tm_fvar fv when
                         FStar_Ident.lid_equals
                           (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           FStar_Parser_Const.deprecated_attr
                         ->
                         let msg =
                           let uu____638 =
                             FStar_Syntax_Print.term_to_string tm  in
                           Prims.op_Hat uu____638 " is deprecated"  in
                         let uu____641 = FStar_Ident.range_of_lid l  in
                         FStar_Errors.log_issue uu____641
                           (FStar_Errors.Warning_DeprecatedDefinition, msg)
                     | uu____643 -> ()) attrs1
                 in
              (warn_if_deprecated attrs;
               (let tm1 = setpos tm  in FStar_Pervasives_Native.Some tm1))
  
let desugar_name :
  'Auu____659 .
    'Auu____659 ->
      (FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) ->
        env_t -> Prims.bool -> FStar_Ident.lident -> FStar_Syntax_Syntax.term
  =
  fun mk1  ->
    fun setpos  ->
      fun env  ->
        fun resolve  ->
          fun l  ->
            FStar_Syntax_DsEnv.fail_or env (desugar_name' setpos env resolve)
              l
  
let (compile_op_lid :
  Prims.int -> Prims.string -> FStar_Range.range -> FStar_Ident.lident) =
  fun n1  ->
    fun s  ->
      fun r  ->
        let uu____712 =
          let uu____715 =
            let uu____716 =
              let uu____722 = FStar_Parser_AST.compile_op n1 s r  in
              (uu____722, r)  in
            FStar_Ident.mk_ident uu____716  in
          [uu____715]  in
        FStar_All.pipe_right uu____712 FStar_Ident.lid_of_ids
  
let op_as_term :
  'Auu____738 .
    env_t ->
      Prims.int ->
        'Auu____738 ->
          FStar_Ident.ident ->
            FStar_Syntax_Syntax.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun arity  ->
      fun rng  ->
        fun op  ->
          let r l dd =
            let uu____776 =
              let uu____777 =
                let uu____778 =
                  FStar_Ident.set_lid_range l op.FStar_Ident.idRange  in
                FStar_Syntax_Syntax.lid_as_fv uu____778 dd
                  FStar_Pervasives_Native.None
                 in
              FStar_All.pipe_right uu____777 FStar_Syntax_Syntax.fv_to_tm  in
            FStar_Pervasives_Native.Some uu____776  in
          let fallback uu____786 =
            let uu____787 = FStar_Ident.text_of_id op  in
            match uu____787 with
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
                let uu____808 = FStar_Options.ml_ish ()  in
                if uu____808
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
            | uu____833 -> FStar_Pervasives_Native.None  in
          let uu____835 =
            let uu____838 =
              compile_op_lid arity op.FStar_Ident.idText
                op.FStar_Ident.idRange
               in
            desugar_name'
              (fun t  ->
                 let uu___203_844 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___203_844.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___203_844.FStar_Syntax_Syntax.vars)
                 }) env true uu____838
             in
          match uu____835 with
          | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
          | uu____849 -> fallback ()
  
let (sort_ftv : FStar_Ident.ident Prims.list -> FStar_Ident.ident Prims.list)
  =
  fun ftv  ->
    let uu____864 =
      FStar_Util.remove_dups
        (fun x  -> fun y  -> x.FStar_Ident.idText = y.FStar_Ident.idText) ftv
       in
    FStar_All.pipe_left
      (FStar_Util.sort_with
         (fun x  ->
            fun y  ->
              FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))
      uu____864
  
let rec (free_type_vars_b :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder ->
      (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list))
  =
  fun env  ->
    fun binder  ->
      match binder.FStar_Parser_AST.b with
      | FStar_Parser_AST.Variable uu____913 -> (env, [])
      | FStar_Parser_AST.TVariable x ->
          let uu____917 = FStar_Syntax_DsEnv.push_bv env x  in
          (match uu____917 with | (env1,uu____929) -> (env1, [x]))
      | FStar_Parser_AST.Annotated (uu____932,term) ->
          let uu____934 = free_type_vars env term  in (env, uu____934)
      | FStar_Parser_AST.TAnnotated (id1,uu____940) ->
          let uu____941 = FStar_Syntax_DsEnv.push_bv env id1  in
          (match uu____941 with | (env1,uu____953) -> (env1, []))
      | FStar_Parser_AST.NoName t ->
          let uu____957 = free_type_vars env t  in (env, uu____957)

and (free_type_vars :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.term -> FStar_Ident.ident Prims.list)
  =
  fun env  ->
    fun t  ->
      let uu____964 =
        let uu____965 = unparen t  in uu____965.FStar_Parser_AST.tm  in
      match uu____964 with
      | FStar_Parser_AST.Labeled uu____968 ->
          failwith "Impossible --- labeled source term"
      | FStar_Parser_AST.Tvar a ->
          let uu____981 = FStar_Syntax_DsEnv.try_lookup_id env a  in
          (match uu____981 with
           | FStar_Pervasives_Native.None  -> [a]
           | uu____986 -> [])
      | FStar_Parser_AST.Wild  -> []
      | FStar_Parser_AST.Const uu____989 -> []
      | FStar_Parser_AST.Uvar uu____990 -> []
      | FStar_Parser_AST.Var uu____991 -> []
      | FStar_Parser_AST.Projector uu____992 -> []
      | FStar_Parser_AST.Discrim uu____997 -> []
      | FStar_Parser_AST.Name uu____998 -> []
      | FStar_Parser_AST.Requires (t1,uu____1000) -> free_type_vars env t1
      | FStar_Parser_AST.Ensures (t1,uu____1008) -> free_type_vars env t1
      | FStar_Parser_AST.NamedTyp (uu____1015,t1) -> free_type_vars env t1
      | FStar_Parser_AST.Paren t1 -> failwith "impossible"
      | FStar_Parser_AST.Ascribed (t1,t',tacopt) ->
          let ts = t1 :: t' ::
            (match tacopt with
             | FStar_Pervasives_Native.None  -> []
             | FStar_Pervasives_Native.Some t2 -> [t2])
             in
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.Construct (uu____1034,ts) ->
          FStar_List.collect
            (fun uu____1055  ->
               match uu____1055 with
               | (t1,uu____1063) -> free_type_vars env t1) ts
      | FStar_Parser_AST.Op (uu____1064,ts) ->
          FStar_List.collect (free_type_vars env) ts
      | FStar_Parser_AST.App (t1,t2,uu____1072) ->
          let uu____1073 = free_type_vars env t1  in
          let uu____1076 = free_type_vars env t2  in
          FStar_List.append uu____1073 uu____1076
      | FStar_Parser_AST.Refine (b,t1) ->
          let uu____1081 = free_type_vars_b env b  in
          (match uu____1081 with
           | (env1,f) ->
               let uu____1096 = free_type_vars env1 t1  in
               FStar_List.append f uu____1096)
      | FStar_Parser_AST.Sum (binders,body) ->
          let uu____1113 =
            FStar_List.fold_left
              (fun uu____1137  ->
                 fun bt  ->
                   match uu____1137 with
                   | (env1,free) ->
                       let uu____1161 =
                         match bt with
                         | FStar_Util.Inl binder ->
                             free_type_vars_b env1 binder
                         | FStar_Util.Inr t1 ->
                             let uu____1176 = free_type_vars env1 body  in
                             (env1, uu____1176)
                          in
                       (match uu____1161 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1113 with
           | (env1,free) ->
               let uu____1205 = free_type_vars env1 body  in
               FStar_List.append free uu____1205)
      | FStar_Parser_AST.Product (binders,body) ->
          let uu____1214 =
            FStar_List.fold_left
              (fun uu____1234  ->
                 fun binder  ->
                   match uu____1234 with
                   | (env1,free) ->
                       let uu____1254 = free_type_vars_b env1 binder  in
                       (match uu____1254 with
                        | (env2,f) -> (env2, (FStar_List.append f free))))
              (env, []) binders
             in
          (match uu____1214 with
           | (env1,free) ->
               let uu____1285 = free_type_vars env1 body  in
               FStar_List.append free uu____1285)
      | FStar_Parser_AST.Project (t1,uu____1289) -> free_type_vars env t1
      | FStar_Parser_AST.Attributes cattributes ->
          FStar_List.collect (free_type_vars env) cattributes
      | FStar_Parser_AST.CalcProof (rel,init1,steps) ->
          let uu____1300 = free_type_vars env rel  in
          let uu____1303 =
            let uu____1306 = free_type_vars env init1  in
            let uu____1309 =
              FStar_List.collect
                (fun uu____1318  ->
                   match uu____1318 with
                   | FStar_Parser_AST.CalcStep (rel1,just,next) ->
                       let uu____1324 = free_type_vars env rel1  in
                       let uu____1327 =
                         let uu____1330 = free_type_vars env just  in
                         let uu____1333 = free_type_vars env next  in
                         FStar_List.append uu____1330 uu____1333  in
                       FStar_List.append uu____1324 uu____1327) steps
               in
            FStar_List.append uu____1306 uu____1309  in
          FStar_List.append uu____1300 uu____1303
      | FStar_Parser_AST.Abs uu____1336 -> []
      | FStar_Parser_AST.Let uu____1343 -> []
      | FStar_Parser_AST.LetOpen uu____1364 -> []
      | FStar_Parser_AST.If uu____1369 -> []
      | FStar_Parser_AST.QForall uu____1376 -> []
      | FStar_Parser_AST.QExists uu____1395 -> []
      | FStar_Parser_AST.Record uu____1414 -> []
      | FStar_Parser_AST.Match uu____1427 -> []
      | FStar_Parser_AST.TryWith uu____1442 -> []
      | FStar_Parser_AST.Bind uu____1457 -> []
      | FStar_Parser_AST.Quote uu____1464 -> []
      | FStar_Parser_AST.VQuote uu____1469 -> []
      | FStar_Parser_AST.Antiquote uu____1470 -> []
      | FStar_Parser_AST.Seq uu____1471 -> []

let (head_and_args :
  FStar_Parser_AST.term ->
    (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp)
      Prims.list))
  =
  fun t  ->
    let rec aux args t1 =
      let uu____1525 =
        let uu____1526 = unparen t1  in uu____1526.FStar_Parser_AST.tm  in
      match uu____1525 with
      | FStar_Parser_AST.App (t2,arg,imp) -> aux ((arg, imp) :: args) t2
      | FStar_Parser_AST.Construct (l,args') ->
          ({
             FStar_Parser_AST.tm = (FStar_Parser_AST.Name l);
             FStar_Parser_AST.range = (t1.FStar_Parser_AST.range);
             FStar_Parser_AST.level = (t1.FStar_Parser_AST.level)
           }, (FStar_List.append args' args))
      | uu____1568 -> (t1, args)  in
    aux [] t
  
let (close :
  FStar_Syntax_DsEnv.env -> FStar_Parser_AST.term -> FStar_Parser_AST.term) =
  fun env  ->
    fun t  ->
      let ftv =
        let uu____1593 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1593  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1615 =
                     let uu____1616 =
                       let uu____1621 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1621)  in
                     FStar_Parser_AST.TAnnotated uu____1616  in
                   FStar_Parser_AST.mk_binder uu____1615
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
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
        let uu____1639 = free_type_vars env t  in
        FStar_All.pipe_left sort_ftv uu____1639  in
      if (FStar_List.length ftv) = Prims.int_zero
      then t
      else
        (let binders =
           FStar_All.pipe_right ftv
             (FStar_List.map
                (fun x  ->
                   let uu____1661 =
                     let uu____1662 =
                       let uu____1667 = tm_type x.FStar_Ident.idRange  in
                       (x, uu____1667)  in
                     FStar_Parser_AST.TAnnotated uu____1662  in
                   FStar_Parser_AST.mk_binder uu____1661
                     x.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)))
            in
         let t1 =
           let uu____1669 =
             let uu____1670 = unparen t  in uu____1670.FStar_Parser_AST.tm
              in
           match uu____1669 with
           | FStar_Parser_AST.Product uu____1671 -> t
           | uu____1678 ->
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
      | uu____1715 -> (bs, t)
  
let rec (is_var_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatWild uu____1726 -> true
    | FStar_Parser_AST.PatTvar (uu____1730,uu____1731) -> true
    | FStar_Parser_AST.PatVar (uu____1737,uu____1738) -> true
    | FStar_Parser_AST.PatAscribed (p1,uu____1745) -> is_var_pattern p1
    | uu____1758 -> false
  
let rec (is_app_pattern : FStar_Parser_AST.pattern -> Prims.bool) =
  fun p  ->
    match p.FStar_Parser_AST.pat with
    | FStar_Parser_AST.PatAscribed (p1,uu____1769) -> is_app_pattern p1
    | FStar_Parser_AST.PatApp
        ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatVar uu____1782;
           FStar_Parser_AST.prange = uu____1783;_},uu____1784)
        -> true
    | uu____1796 -> false
  
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
    | uu____1812 -> p
  
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
    fun is_top_level1  ->
      fun p  ->
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatAscribed (p1,t) ->
            let uu____1885 = destruct_app_pattern env is_top_level1 p1  in
            (match uu____1885 with
             | (name,args,uu____1928) ->
                 (name, args, (FStar_Pervasives_Native.Some t)))
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____1978);
               FStar_Parser_AST.prange = uu____1979;_},args)
            when is_top_level1 ->
            let uu____1989 =
              let uu____1994 = FStar_Syntax_DsEnv.qualify env id1  in
              FStar_Util.Inr uu____1994  in
            (uu____1989, args, FStar_Pervasives_Native.None)
        | FStar_Parser_AST.PatApp
            ({
               FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                 (id1,uu____2016);
               FStar_Parser_AST.prange = uu____2017;_},args)
            -> ((FStar_Util.Inl id1), args, FStar_Pervasives_Native.None)
        | uu____2047 -> failwith "Not an app pattern"
  
let rec (gather_pattern_bound_vars_maybe_top :
  Prims.bool ->
    FStar_Ident.ident FStar_Util.set ->
      FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun acc  ->
      fun p  ->
        let gather_pattern_bound_vars_from_list =
          FStar_List.fold_left
            (gather_pattern_bound_vars_maybe_top fail_on_patconst) acc
           in
        match p.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatWild uu____2106 -> acc
        | FStar_Parser_AST.PatName uu____2109 -> acc
        | FStar_Parser_AST.PatOp uu____2110 -> acc
        | FStar_Parser_AST.PatConst uu____2111 ->
            if fail_on_patconst
            then
              FStar_Errors.raise_error
                (FStar_Errors.Error_CannotRedefineConst,
                  "Constants cannot be redefined") p.FStar_Parser_AST.prange
            else acc
        | FStar_Parser_AST.PatApp (phead,pats) ->
            gather_pattern_bound_vars_from_list (phead :: pats)
        | FStar_Parser_AST.PatTvar (x,uu____2128) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatVar (x,uu____2134) -> FStar_Util.set_add x acc
        | FStar_Parser_AST.PatList pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatTuple (pats,uu____2143) ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatOr pats ->
            gather_pattern_bound_vars_from_list pats
        | FStar_Parser_AST.PatRecord guarded_pats ->
            let uu____2160 =
              FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
            gather_pattern_bound_vars_from_list uu____2160
        | FStar_Parser_AST.PatAscribed (pat,uu____2168) ->
            gather_pattern_bound_vars_maybe_top fail_on_patconst acc pat
  
let (gather_pattern_bound_vars :
  Prims.bool -> FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun fail_on_patconst  ->
    fun p  ->
      let acc =
        FStar_Util.new_set
          (fun id1  ->
             fun id2  ->
               if id1.FStar_Ident.idText = id2.FStar_Ident.idText
               then Prims.int_zero
               else Prims.int_one)
         in
      gather_pattern_bound_vars_maybe_top fail_on_patconst acc p
  
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2250 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2291 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (is_implicit : bnd -> Prims.bool) =
  fun b  ->
    match b with
    | LocalBinder
        (uu____2339,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2340))
        -> true
    | uu____2343 -> false
  
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2354  ->
    match uu___3_2354 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2361 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2394  ->
    match uu____2394 with
    | (attrs,n1,t,e,pos) ->
        {
          FStar_Syntax_Syntax.lbname = n1;
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
      let uu____2476 =
        let uu____2493 =
          let uu____2496 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2496  in
        let uu____2497 =
          let uu____2508 =
            let uu____2517 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2517)  in
          [uu____2508]  in
        (uu____2493, uu____2497)  in
      FStar_Syntax_Syntax.Tm_app uu____2476  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2566 =
        let uu____2583 =
          let uu____2586 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2586  in
        let uu____2587 =
          let uu____2598 =
            let uu____2607 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2607)  in
          [uu____2598]  in
        (uu____2583, uu____2587)  in
      FStar_Syntax_Syntax.Tm_app uu____2566  in
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
          let uu____2670 =
            let uu____2687 =
              let uu____2690 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2690  in
            let uu____2691 =
              let uu____2702 =
                let uu____2711 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2711)  in
              let uu____2719 =
                let uu____2730 =
                  let uu____2739 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2739)  in
                [uu____2730]  in
              uu____2702 :: uu____2719  in
            (uu____2687, uu____2691)  in
          FStar_Syntax_Syntax.Tm_app uu____2670  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2799 =
        let uu____2814 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2833  ->
               match uu____2833 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2844;
                    FStar_Syntax_Syntax.index = uu____2845;
                    FStar_Syntax_Syntax.sort = t;_},uu____2847)
                   ->
                   let uu____2855 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2855) uu____2814
         in
      FStar_All.pipe_right bs uu____2799  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2871 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2889 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2917 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2938,uu____2939,bs,t,uu____2942,uu____2943)
                            ->
                            let uu____2952 = bs_univnames bs  in
                            let uu____2955 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2952 uu____2955
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2958,uu____2959,t,uu____2961,uu____2962,uu____2963)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2970 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2917 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___593_2979 = s  in
        let uu____2980 =
          let uu____2981 =
            let uu____2990 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____3008,bs,t,lids1,lids2) ->
                          let uu___604_3021 = se  in
                          let uu____3022 =
                            let uu____3023 =
                              let uu____3040 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3041 =
                                let uu____3042 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3042 t  in
                              (lid, uvs, uu____3040, uu____3041, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3023
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3022;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___604_3021.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___604_3021.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___604_3021.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___604_3021.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___604_3021.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3056,t,tlid,n1,lids1) ->
                          let uu___614_3067 = se  in
                          let uu____3068 =
                            let uu____3069 =
                              let uu____3085 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3085, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3069  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3068;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___614_3067.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___614_3067.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___614_3067.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___614_3067.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___614_3067.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____3089 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2990, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2981  in
        {
          FStar_Syntax_Syntax.sigel = uu____2980;
          FStar_Syntax_Syntax.sigrng =
            (uu___593_2979.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___593_2979.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___593_2979.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___593_2979.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___593_2979.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3096,t) ->
        let uvs =
          let uu____3099 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3099 FStar_Util.set_elements  in
        let uu___623_3104 = s  in
        let uu____3105 =
          let uu____3106 =
            let uu____3113 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3113)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3106  in
        {
          FStar_Syntax_Syntax.sigel = uu____3105;
          FStar_Syntax_Syntax.sigrng =
            (uu___623_3104.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___623_3104.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___623_3104.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___623_3104.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___623_3104.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3137 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3140 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3147) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3180,(FStar_Util.Inl t,uu____3182),uu____3183)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3230,(FStar_Util.Inr c,uu____3232),uu____3233)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3280 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3282) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3303,(FStar_Util.Inl t,uu____3305),uu____3306) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3353,(FStar_Util.Inr c,uu____3355),uu____3356) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3403 -> empty_set  in
          FStar_Util.set_union uu____3137 uu____3140  in
        let all_lb_univs =
          let uu____3407 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3423 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3423) empty_set)
             in
          FStar_All.pipe_right uu____3407 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___682_3433 = s  in
        let uu____3434 =
          let uu____3435 =
            let uu____3442 =
              let uu____3443 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___685_3455 = lb  in
                        let uu____3456 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3459 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___685_3455.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3456;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___685_3455.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3459;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___685_3455.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___685_3455.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3443)  in
            (uu____3442, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3435  in
        {
          FStar_Syntax_Syntax.sigel = uu____3434;
          FStar_Syntax_Syntax.sigrng =
            (uu___682_3433.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___682_3433.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___682_3433.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___682_3433.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___682_3433.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3468,fml) ->
        let uvs =
          let uu____3471 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3471 FStar_Util.set_elements  in
        let uu___693_3476 = s  in
        let uu____3477 =
          let uu____3478 =
            let uu____3485 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3485)  in
          FStar_Syntax_Syntax.Sig_assume uu____3478  in
        {
          FStar_Syntax_Syntax.sigel = uu____3477;
          FStar_Syntax_Syntax.sigrng =
            (uu___693_3476.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___693_3476.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___693_3476.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___693_3476.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___693_3476.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3487,bs,c,flags) ->
        let uvs =
          let uu____3496 =
            let uu____3499 = bs_univnames bs  in
            let uu____3502 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3499 uu____3502  in
          FStar_All.pipe_right uu____3496 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___704_3510 = s  in
        let uu____3511 =
          let uu____3512 =
            let uu____3525 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3526 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3525, uu____3526, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3512  in
        {
          FStar_Syntax_Syntax.sigel = uu____3511;
          FStar_Syntax_Syntax.sigrng =
            (uu___704_3510.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___704_3510.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___704_3510.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___704_3510.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___704_3510.FStar_Syntax_Syntax.sigopts)
        }
    | uu____3529 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3537  ->
    match uu___4_3537 with
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
    | uu____3586 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = Prims.int_zero
      then u
      else
        (let uu____3607 = sum_to_universe u (n1 - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3607)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3633 =
      let uu____3634 = unparen t  in uu____3634.FStar_Parser_AST.tm  in
    match uu____3633 with
    | FStar_Parser_AST.Wild  ->
        let uu____3640 =
          let uu____3641 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3641  in
        FStar_Util.Inr uu____3640
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3654)) ->
        let n1 = FStar_Util.int_of_string repr  in
        (if n1 < Prims.int_zero
         then
           FStar_Errors.raise_error
             (FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported,
               (Prims.op_Hat
                  "Negative universe constant  are not supported : " repr))
             t.FStar_Parser_AST.range
         else ();
         FStar_Util.Inl n1)
    | FStar_Parser_AST.Op (op_plus,t1::t2::[]) ->
        let u1 = desugar_maybe_non_constant_universe t1  in
        let u2 = desugar_maybe_non_constant_universe t2  in
        (match (u1, u2) with
         | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
         | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
             let uu____3745 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3745
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3762 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3762
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3778 =
               let uu____3784 =
                 let uu____3786 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3786
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3784)
                in
             FStar_Errors.raise_error uu____3778 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3795 ->
        let rec aux t1 univargs =
          let uu____3832 =
            let uu____3833 = unparen t1  in uu____3833.FStar_Parser_AST.tm
             in
          match uu____3832 with
          | FStar_Parser_AST.App (t2,targ,uu____3841) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3868  ->
                     match uu___5_3868 with
                     | FStar_Util.Inr uu____3875 -> true
                     | uu____3878 -> false) univargs
              then
                let uu____3886 =
                  let uu____3887 =
                    FStar_List.map
                      (fun uu___6_3897  ->
                         match uu___6_3897 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3887  in
                FStar_Util.Inr uu____3886
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3923  ->
                        match uu___7_3923 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3933 -> failwith "impossible")
                     univargs
                    in
                 let uu____3937 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3937)
          | uu____3953 ->
              let uu____3954 =
                let uu____3960 =
                  let uu____3962 =
                    let uu____3964 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3964 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3962  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3960)  in
              FStar_Errors.raise_error uu____3954 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3979 ->
        let uu____3980 =
          let uu____3986 =
            let uu____3988 =
              let uu____3990 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3990 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3988  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3986)  in
        FStar_Errors.raise_error uu____3980 t.FStar_Parser_AST.range
  
let (desugar_universe :
  FStar_Parser_AST.term -> FStar_Syntax_Syntax.universe) =
  fun t  ->
    let u = desugar_maybe_non_constant_universe t  in
    match u with
    | FStar_Util.Inl n1 -> int_to_universe n1
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
                   FStar_Syntax_Syntax.antiquotes = uu____4031;_});
            FStar_Syntax_Syntax.pos = uu____4032;
            FStar_Syntax_Syntax.vars = uu____4033;_})::uu____4034
        ->
        let uu____4065 =
          let uu____4071 =
            let uu____4073 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4073
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4071)  in
        FStar_Errors.raise_error uu____4065 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4079 ->
        let uu____4098 =
          let uu____4104 =
            let uu____4106 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4106
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4104)  in
        FStar_Errors.raise_error uu____4098 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4119 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4119) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4147 = FStar_List.hd fields  in
        match uu____4147 with
        | (f,uu____4157) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4169 =
                match uu____4169 with
                | (f',uu____4175) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4177 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4177
                      then ()
                      else
                        (let msg =
                           FStar_Util.format3
                             "Field %s belongs to record type %s, whereas field %s does not"
                             f.FStar_Ident.str
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                             f'.FStar_Ident.str
                            in
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_FieldsNotBelongToSameRecordType,
                             msg) rg)))
                 in
              (let uu____4187 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4187);
              (match () with | () -> record)))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4235 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4242 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4243 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4245,pats1) ->
            let aux out uu____4286 =
              match uu____4286 with
              | (p1,uu____4299) ->
                  let intersection =
                    let uu____4309 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4309 out  in
                  let uu____4312 = FStar_Util.set_is_empty intersection  in
                  if uu____4312
                  then
                    let uu____4317 = pat_vars p1  in
                    FStar_Util.set_union out uu____4317
                  else
                    (let duplicate_bv =
                       let uu____4323 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4323  in
                     let uu____4326 =
                       let uu____4332 =
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4332)
                        in
                     FStar_Errors.raise_error uu____4326 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4356 = pat_vars p  in
          FStar_All.pipe_right uu____4356 (fun a1  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4384 =
              let uu____4386 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4386  in
            if uu____4384
            then ()
            else
              (let nonlinear_vars =
                 let uu____4395 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4395  in
               let first_nonlinear_var =
                 let uu____4399 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4399  in
               let uu____4402 =
                 let uu____4408 =
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4408)  in
               FStar_Errors.raise_error uu____4402 r)
             in
          FStar_List.iter aux ps
  
let rec (desugar_data_pat :
  env_t ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun env  ->
    fun p  ->
      let resolvex l e x =
        let uu____4714 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4714 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4731 ->
            let uu____4734 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4734 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4835 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4856 =
              let uu____4857 =
                let uu____4858 =
                  let uu____4865 =
                    let uu____4866 =
                      let uu____4872 =
                        FStar_Parser_AST.compile_op Prims.int_zero
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4872, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4866  in
                  (uu____4865, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4858  in
              {
                FStar_Parser_AST.pat = uu____4857;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4856
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4892 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4895 = aux loc env1 p2  in
              match uu____4895 with
              | (loc1,env',binder,p3,annots) ->
                  let uu____4945 =
                    match binder with
                    | LetBinder uu____4966 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____4991 = close_fun env1 t  in
                          desugar_term env1 uu____4991  in
                        let x1 =
                          let uu___939_4993 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___939_4993.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___939_4993.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____4945 with
                   | (annots',binder1) ->
                       (loc1, env', binder1, p3,
                         (FStar_List.append annots' annots)))))
        | FStar_Parser_AST.PatWild aq ->
            let aq1 = trans_aqual env1 aq  in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5053 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____5053, [])
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5066 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5066, [])
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let aq1 = trans_aqual env1 aq  in
            let uu____5084 = resolvex loc env1 x  in
            (match uu____5084 with
             | (loc1,env2,xbv) ->
                 let uu____5110 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5110, []))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let aq1 = trans_aqual env1 aq  in
            let uu____5128 = resolvex loc env1 x  in
            (match uu____5128 with
             | (loc1,env2,xbv) ->
                 let uu____5154 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5154, []))
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
            let uu____5168 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5168, [])
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5196;_},args)
            ->
            let uu____5202 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5259  ->
                     match uu____5259 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5332 = aux loc1 env2 arg  in
                         (match uu____5332 with
                          | (loc2,env3,b,arg1,ans) ->
                              let imp = is_implicit b  in
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5202 with
             | (loc1,env2,annots,args1) ->
                 let l1 =
                   FStar_Syntax_DsEnv.fail_or env2
                     (FStar_Syntax_DsEnv.try_lookup_datacon env2) l
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____5482 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5482, annots))
        | FStar_Parser_AST.PatApp uu____5498 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5526 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5572  ->
                     match uu____5572 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5625 = aux loc1 env2 pat  in
                         (match uu____5625 with
                          | (loc2,env3,uu____5660,pat1,ans) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5526 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5738 =
                     let uu____5741 =
                       let uu____5748 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5748  in
                     let uu____5749 =
                       let uu____5750 =
                         let uu____5764 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5764, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5750  in
                     FStar_All.pipe_left uu____5741 uu____5749  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____5798 =
                            let uu____5799 =
                              let uu____5813 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____5813, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____5799  in
                          FStar_All.pipe_left (pos_r r) uu____5798) pats1
                     uu____5738
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                   annots))
        | FStar_Parser_AST.PatTuple (args,dep1) ->
            let uu____5869 =
              FStar_List.fold_left
                (fun uu____5924  ->
                   fun p2  ->
                     match uu____5924 with
                     | (loc1,env2,annots,pats) ->
                         let uu____5998 = aux loc1 env2 p2  in
                         (match uu____5998 with
                          | (loc2,env3,uu____6038,pat,ans) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____5869 with
             | (loc1,env2,annots,args1) ->
                 let args2 = FStar_List.rev args1  in
                 let l =
                   if dep1
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
                   | uu____6175 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6178 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6178, annots))
        | FStar_Parser_AST.PatRecord [] ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatRecord fields ->
            let record = check_fields env1 fields p1.FStar_Parser_AST.prange
               in
            let fields1 =
              FStar_All.pipe_right fields
                (FStar_List.map
                   (fun uu____6254  ->
                      match uu____6254 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6284  ->
                      match uu____6284 with
                      | (f,uu____6290) ->
                          let uu____6291 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6317  ->
                                    match uu____6317 with
                                    | (g,uu____6324) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6291 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6330,p2) ->
                               p2)))
               in
            let app =
              let uu____6337 =
                let uu____6338 =
                  let uu____6345 =
                    let uu____6346 =
                      let uu____6347 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6347  in
                    FStar_Parser_AST.mk_pattern uu____6346
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6345, args)  in
                FStar_Parser_AST.PatApp uu____6338  in
              FStar_Parser_AST.mk_pattern uu____6337
                p1.FStar_Parser_AST.prange
               in
            let uu____6350 = aux loc env1 app  in
            (match uu____6350 with
             | (env2,e,b,p2,annots) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6421 =
                         let uu____6422 =
                           let uu____6436 =
                             let uu___1082_6437 = fv  in
                             let uu____6438 =
                               let uu____6441 =
                                 let uu____6442 =
                                   let uu____6449 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6449)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6442
                                  in
                               FStar_Pervasives_Native.Some uu____6441  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1082_6437.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1082_6437.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6438
                             }  in
                           (uu____6436, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6422  in
                       FStar_All.pipe_left pos uu____6421
                   | uu____6475 -> p2  in
                 (env2, e, b, p3, annots))
         in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6555 = aux loc env1 p2  in
            (match uu____6555 with
             | (loc1,env2,var,p3,ans) ->
                 let uu____6607 =
                   FStar_List.fold_left
                     (fun uu____6655  ->
                        fun p4  ->
                          match uu____6655 with
                          | (loc2,env3,ps1) ->
                              let uu____6720 = aux loc2 env3 p4  in
                              (match uu____6720 with
                               | (loc3,env4,uu____6757,p5,ans1) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6607 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____6918 ->
            let uu____6919 = aux loc env1 p1  in
            (match uu____6919 with
             | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7009 = aux_maybe_or env p  in
      match uu____7009 with
      | (env1,b,pats) ->
          ((let uu____7064 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7064
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
            let uu____7138 =
              let uu____7139 =
                let uu____7150 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7150, (ty, tacopt))  in
              LetBinder uu____7139  in
            (env, uu____7138, [])  in
          let op_to_ident x =
            let uu____7167 =
              let uu____7173 =
                FStar_Parser_AST.compile_op Prims.int_zero
                  x.FStar_Ident.idText x.FStar_Ident.idRange
                 in
              (uu____7173, (x.FStar_Ident.idRange))  in
            FStar_Ident.mk_ident uu____7167  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7186 = op_to_ident x  in
              mklet uu____7186 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7188) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7194;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7210 = op_to_ident x  in
              let uu____7211 = desugar_term env t  in
              mklet uu____7210 uu____7211 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7213);
                 FStar_Parser_AST.prange = uu____7214;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7234 = desugar_term env t  in
              mklet x uu____7234 tacopt1
          | uu____7235 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7248 = desugar_data_pat env p  in
           match uu____7248 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7277;
                      FStar_Syntax_Syntax.p = uu____7278;_},uu____7279)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7292;
                      FStar_Syntax_Syntax.p = uu____7293;_},uu____7294)::[]
                     -> []
                 | uu____7307 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7315  ->
    fun env  ->
      fun pat  ->
        let uu____7319 = desugar_data_pat env pat  in
        match uu____7319 with | (env1,uu____7335,pat1) -> (env1, pat1)

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
      let uu____7357 = desugar_term_aq env e  in
      match uu____7357 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7376 = desugar_typ_aq env e  in
      match uu____7376 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7386  ->
        fun range  ->
          match uu____7386 with
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
              ((let uu____7408 =
                  let uu____7410 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7410  in
                if uu____7408
                then
                  let uu____7413 =
                    let uu____7419 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7419)  in
                  FStar_Errors.log_issue range uu____7413
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
                  let uu____7440 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7440 range  in
                let lid1 =
                  let uu____7444 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7444 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7454 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7454 range  in
                           let private_fv =
                             let uu____7456 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7456 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1246_7457 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1246_7457.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1246_7457.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7458 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7462 =
                        let uu____7468 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7468)
                         in
                      FStar_Errors.raise_error uu____7462 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7488 =
                  let uu____7495 =
                    let uu____7496 =
                      let uu____7513 =
                        let uu____7524 =
                          let uu____7533 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7533)  in
                        [uu____7524]  in
                      (lid1, uu____7513)  in
                    FStar_Syntax_Syntax.Tm_app uu____7496  in
                  FStar_Syntax_Syntax.mk uu____7495  in
                uu____7488 FStar_Pervasives_Native.None range))

and (desugar_term_maybe_top :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.term ->
        (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations))
  =
  fun top_level  ->
    fun env  ->
      fun top  ->
        let mk1 e =
          FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None
            top.FStar_Parser_AST.range
           in
        let noaqs = []  in
        let join_aqs aqs = FStar_List.flatten aqs  in
        let setpos e =
          let uu___1262_7652 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1262_7652.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1262_7652.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7655 =
          let uu____7656 = unparen top  in uu____7656.FStar_Parser_AST.tm  in
        match uu____7655 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7661 ->
            let uu____7670 = desugar_formula env top  in (uu____7670, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7679 = desugar_formula env t  in (uu____7679, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7688 = desugar_formula env t  in (uu____7688, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7715 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7715, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7717 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7717, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7726 =
                let uu____7727 =
                  let uu____7734 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7734, args)  in
                FStar_Parser_AST.Op uu____7727  in
              FStar_Parser_AST.mk_term uu____7726 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7739 =
              let uu____7740 =
                let uu____7741 =
                  let uu____7748 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7748, [e])  in
                FStar_Parser_AST.Op uu____7741  in
              FStar_Parser_AST.mk_term uu____7740 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7739
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7760 = FStar_Ident.text_of_id op_star  in
             uu____7760 = "*") &&
              (let uu____7765 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____7765 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7782;_},t1::t2::[])
                  when
                  let uu____7788 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____7788 FStar_Option.isNone ->
                  let uu____7795 = flatten1 t1  in
                  FStar_List.append uu____7795 [t2]
              | uu____7798 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1310_7803 = top  in
              let uu____7804 =
                let uu____7805 =
                  let uu____7816 =
                    FStar_List.map (fun _7827  -> FStar_Util.Inr _7827) terms
                     in
                  (uu____7816, rhs)  in
                FStar_Parser_AST.Sum uu____7805  in
              {
                FStar_Parser_AST.tm = uu____7804;
                FStar_Parser_AST.range =
                  (uu___1310_7803.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1310_7803.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____7835 =
              let uu____7836 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____7836  in
            (uu____7835, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____7842 =
              let uu____7848 =
                let uu____7850 =
                  let uu____7852 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____7852 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____7850  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____7848)  in
            FStar_Errors.raise_error uu____7842 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____7867 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____7867 with
             | FStar_Pervasives_Native.None  ->
                 let uu____7874 =
                   let uu____7880 =
                     let uu____7882 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____7882
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____7880)
                    in
                 FStar_Errors.raise_error uu____7874
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____7897 =
                     let uu____7922 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____7984 = desugar_term_aq env t  in
                               match uu____7984 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____7922 FStar_List.unzip  in
                   (match uu____7897 with
                    | (args1,aqs) ->
                        let uu____8117 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8117, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8134)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8151 =
              let uu___1339_8152 = top  in
              let uu____8153 =
                let uu____8154 =
                  let uu____8161 =
                    let uu___1341_8162 = top  in
                    let uu____8163 =
                      let uu____8164 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8164  in
                    {
                      FStar_Parser_AST.tm = uu____8163;
                      FStar_Parser_AST.range =
                        (uu___1341_8162.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1341_8162.FStar_Parser_AST.level)
                    }  in
                  (uu____8161, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8154  in
              {
                FStar_Parser_AST.tm = uu____8153;
                FStar_Parser_AST.range =
                  (uu___1339_8152.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1339_8152.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8151
        | FStar_Parser_AST.Construct (n1,(a,uu____8172)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8192 =
                let uu___1351_8193 = top  in
                let uu____8194 =
                  let uu____8195 =
                    let uu____8202 =
                      let uu___1353_8203 = top  in
                      let uu____8204 =
                        let uu____8205 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8205  in
                      {
                        FStar_Parser_AST.tm = uu____8204;
                        FStar_Parser_AST.range =
                          (uu___1353_8203.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1353_8203.FStar_Parser_AST.level)
                      }  in
                    (uu____8202, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8195  in
                {
                  FStar_Parser_AST.tm = uu____8194;
                  FStar_Parser_AST.range =
                    (uu___1351_8193.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1351_8193.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8192))
        | FStar_Parser_AST.Construct (n1,(a,uu____8213)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8230 =
              let uu___1362_8231 = top  in
              let uu____8232 =
                let uu____8233 =
                  let uu____8240 =
                    let uu___1364_8241 = top  in
                    let uu____8242 =
                      let uu____8243 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8243  in
                    {
                      FStar_Parser_AST.tm = uu____8242;
                      FStar_Parser_AST.range =
                        (uu___1364_8241.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1364_8241.FStar_Parser_AST.level)
                    }  in
                  (uu____8240, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8233  in
              {
                FStar_Parser_AST.tm = uu____8232;
                FStar_Parser_AST.range =
                  (uu___1362_8231.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1362_8231.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8230
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8249; FStar_Ident.ident = uu____8250;
              FStar_Ident.nsstr = uu____8251; FStar_Ident.str = "Type0";_}
            ->
            let uu____8256 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8256, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8257; FStar_Ident.ident = uu____8258;
              FStar_Ident.nsstr = uu____8259; FStar_Ident.str = "Type";_}
            ->
            let uu____8264 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8264, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8265; FStar_Ident.ident = uu____8266;
               FStar_Ident.nsstr = uu____8267; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8287 =
              let uu____8288 =
                let uu____8289 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8289  in
              mk1 uu____8288  in
            (uu____8287, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8290; FStar_Ident.ident = uu____8291;
              FStar_Ident.nsstr = uu____8292; FStar_Ident.str = "Effect";_}
            ->
            let uu____8297 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8297, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8298; FStar_Ident.ident = uu____8299;
              FStar_Ident.nsstr = uu____8300; FStar_Ident.str = "True";_}
            ->
            let uu____8305 =
              let uu____8306 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8306
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8305, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8307; FStar_Ident.ident = uu____8308;
              FStar_Ident.nsstr = uu____8309; FStar_Ident.str = "False";_}
            ->
            let uu____8314 =
              let uu____8315 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8315
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8314, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8318;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8321 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8321 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8330 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         Prims.int_one) FStar_Pervasives_Native.None
                     in
                  (uu____8330, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8332 =
                    let uu____8334 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8334 txt
                     in
                  failwith uu____8332))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8343 = desugar_name mk1 setpos env true l  in
              (uu____8343, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8352 = desugar_name mk1 setpos env true l  in
              (uu____8352, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8370 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8370 with
                | FStar_Pervasives_Native.Some uu____8380 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8388 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8388 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8406 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8427 =
                    let uu____8428 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8428  in
                  (uu____8427, noaqs)
              | uu____8434 ->
                  let uu____8442 =
                    let uu____8448 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8448)  in
                  FStar_Errors.raise_error uu____8442
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8458 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8458 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8465 =
                    let uu____8471 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8471)
                     in
                  FStar_Errors.raise_error uu____8465
                    top.FStar_Parser_AST.range
              | uu____8479 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8483 = desugar_name mk1 setpos env true lid'  in
                  (uu____8483, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8505 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8505 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8524 ->
                       let uu____8531 =
                         FStar_Util.take
                           (fun uu____8555  ->
                              match uu____8555 with
                              | (uu____8561,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8531 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8606 =
                              let uu____8631 =
                                FStar_List.map
                                  (fun uu____8674  ->
                                     match uu____8674 with
                                     | (t,imp) ->
                                         let uu____8691 =
                                           desugar_term_aq env t  in
                                         (match uu____8691 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8631
                                FStar_List.unzip
                               in
                            (match uu____8606 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____8834 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____8834, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____8853 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____8853 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____8864 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_8892  ->
                 match uu___8_8892 with
                 | FStar_Util.Inr uu____8898 -> true
                 | uu____8900 -> false) binders
            ->
            let terms =
              let uu____8909 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_8926  ->
                        match uu___9_8926 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____8932 -> failwith "Impossible"))
                 in
              FStar_List.append uu____8909 [t]  in
            let uu____8934 =
              let uu____8959 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9016 = desugar_typ_aq env t1  in
                        match uu____9016 with
                        | (t',aq) ->
                            let uu____9027 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9027, aq)))
                 in
              FStar_All.pipe_right uu____8959 FStar_List.unzip  in
            (match uu____8934 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9137 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9137
                    in
                 let uu____9146 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9146, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9173 =
              let uu____9190 =
                let uu____9197 =
                  let uu____9204 =
                    FStar_All.pipe_left (fun _9213  -> FStar_Util.Inl _9213)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9204]  in
                FStar_List.append binders uu____9197  in
              FStar_List.fold_left
                (fun uu____9258  ->
                   fun b  ->
                     match uu____9258 with
                     | (env1,tparams,typs) ->
                         let uu____9319 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9334 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9334)
                            in
                         (match uu____9319 with
                          | (xopt,t1) ->
                              let uu____9359 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9368 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9368)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9359 with
                               | (env2,x) ->
                                   let uu____9388 =
                                     let uu____9391 =
                                       let uu____9394 =
                                         let uu____9395 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9395
                                          in
                                       [uu____9394]  in
                                     FStar_List.append typs uu____9391  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1523_9421 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1523_9421.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1523_9421.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9388)))) (env, [], []) uu____9190
               in
            (match uu____9173 with
             | (env1,uu____9449,targs) ->
                 let tup =
                   let uu____9472 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9472
                    in
                 let uu____9473 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9473, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9492 = uncurry binders t  in
            (match uu____9492 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9536 =
                   match uu___10_9536 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9553 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9553
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9577 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9577 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9610 = aux env [] bs  in (uu____9610, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9619 = desugar_binder env b  in
            (match uu____9619 with
             | (FStar_Pervasives_Native.None ,uu____9630) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9645 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9645 with
                  | ((x,uu____9661),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9674 =
                        let uu____9675 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9675  in
                      (uu____9674, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9754 = FStar_Util.set_is_empty i  in
                    if uu____9754
                    then
                      let uu____9759 = FStar_Util.set_union acc set1  in
                      aux uu____9759 sets2
                    else
                      (let uu____9764 =
                         let uu____9765 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9765  in
                       FStar_Pervasives_Native.Some uu____9764)
                 in
              let uu____9768 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9768 sets  in
            ((let uu____9772 = check_disjoint bvss  in
              match uu____9772 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9776 =
                    let uu____9782 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9782)
                     in
                  let uu____9786 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9776 uu____9786);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9794 =
                FStar_List.fold_left
                  (fun uu____9814  ->
                     fun pat  ->
                       match uu____9814 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____9840,(t,FStar_Pervasives_Native.None ))
                                ->
                                let uu____9850 =
                                  let uu____9853 = free_type_vars env1 t  in
                                  FStar_List.append uu____9853 ftvs  in
                                (env1, uu____9850)
                            | FStar_Parser_AST.PatAscribed
                                (uu____9858,(t,FStar_Pervasives_Native.Some
                                             tac))
                                ->
                                let uu____9869 =
                                  let uu____9872 = free_type_vars env1 t  in
                                  let uu____9875 =
                                    let uu____9878 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____9878 ftvs  in
                                  FStar_List.append uu____9872 uu____9875  in
                                (env1, uu____9869)
                            | uu____9883 -> (env1, ftvs))) (env, []) binders1
                 in
              match uu____9794 with
              | (uu____9892,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____9904 =
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
                    FStar_List.append uu____9904 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___11_9961 =
                    match uu___11_9961 with
                    | [] ->
                        let uu____9988 = desugar_term_aq env1 body  in
                        (match uu____9988 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10025 =
                                       let uu____10026 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10026
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10025
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
                             let uu____10095 =
                               let uu____10098 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10098  in
                             (uu____10095, aq))
                    | p::rest ->
                        let uu____10113 = desugar_binding_pat env1 p  in
                        (match uu____10113 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10147)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10162 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10171 =
                               match b with
                               | LetBinder uu____10212 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10281) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10335 =
                                           let uu____10344 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10344, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10335
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10406,uu____10407) ->
                                              let tup2 =
                                                let uu____10409 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10409
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10414 =
                                                  let uu____10421 =
                                                    let uu____10422 =
                                                      let uu____10439 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10442 =
                                                        let uu____10453 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10462 =
                                                          let uu____10473 =
                                                            let uu____10482 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10482
                                                             in
                                                          [uu____10473]  in
                                                        uu____10453 ::
                                                          uu____10462
                                                         in
                                                      (uu____10439,
                                                        uu____10442)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10422
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10421
                                                   in
                                                uu____10414
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10530 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10530
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10581,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10583,pats)) ->
                                              let tupn =
                                                let uu____10628 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10628
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10641 =
                                                  let uu____10642 =
                                                    let uu____10659 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10662 =
                                                      let uu____10673 =
                                                        let uu____10684 =
                                                          let uu____10693 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10693
                                                           in
                                                        [uu____10684]  in
                                                      FStar_List.append args
                                                        uu____10673
                                                       in
                                                    (uu____10659,
                                                      uu____10662)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10642
                                                   in
                                                mk1 uu____10641  in
                                              let p2 =
                                                let uu____10741 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____10741
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10788 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10171 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____10882,uu____10883,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____10905 =
                let uu____10906 = unparen e  in
                uu____10906.FStar_Parser_AST.tm  in
              match uu____10905 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____10916 ->
                  let uu____10917 = desugar_term_aq env e  in
                  (match uu____10917 with
                   | (head1,aq) ->
                       let uu____10930 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____10930, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____10937 ->
            let rec aux args aqs e =
              let uu____11014 =
                let uu____11015 = unparen e  in
                uu____11015.FStar_Parser_AST.tm  in
              match uu____11014 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11033 = desugar_term_aq env t  in
                  (match uu____11033 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11081 ->
                  let uu____11082 = desugar_term_aq env e  in
                  (match uu____11082 with
                   | (head1,aq) ->
                       let uu____11103 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11103, (join_aqs (aq :: aqs))))
               in
            aux [] [] top
        | FStar_Parser_AST.Bind (x,t1,t2) ->
            let xpat =
              FStar_Parser_AST.mk_pattern
                (FStar_Parser_AST.PatVar (x, FStar_Pervasives_Native.None))
                x.FStar_Ident.idRange
               in
            let k =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ([xpat], t2))
                t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level
               in
            let bind_lid =
              FStar_Ident.lid_of_path ["bind"] x.FStar_Ident.idRange  in
            let bind1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var bind_lid)
                x.FStar_Ident.idRange FStar_Parser_AST.Expr
               in
            let uu____11166 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11166
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
            let uu____11218 = desugar_term_aq env t  in
            (match uu____11218 with
             | (tm,s) ->
                 let uu____11229 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11229, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11235 =
              let uu____11248 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11248 then desugar_typ_aq else desugar_term_aq  in
            uu____11235 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11315 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11458  ->
                        match uu____11458 with
                        | (attr_opt,(p,def)) ->
                            let uu____11516 = is_app_pattern p  in
                            if uu____11516
                            then
                              let uu____11549 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11549, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11632 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11632, def1)
                               | uu____11677 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11715);
                                           FStar_Parser_AST.prange =
                                             uu____11716;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11765 =
                                            let uu____11786 =
                                              let uu____11791 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11791  in
                                            (uu____11786, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11765, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____11883) ->
                                        if top_level
                                        then
                                          let uu____11919 =
                                            let uu____11940 =
                                              let uu____11945 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11945  in
                                            (uu____11940, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____11919, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12036 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12069 =
                FStar_List.fold_left
                  (fun uu____12158  ->
                     fun uu____12159  ->
                       match (uu____12158, uu____12159) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12289,uu____12290),uu____12291))
                           ->
                           let uu____12425 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12465 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12465 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12500 =
                                        let uu____12503 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12503 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12500, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12519 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12519 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12425 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12069 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12772 =
                    match uu____12772 with
                    | (attrs_opt,(uu____12812,args,result_t),def) ->
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
                                let uu____12904 = is_comp_type env1 t  in
                                if uu____12904
                                then
                                  ((let uu____12908 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____12918 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____12918))
                                       in
                                    match uu____12908 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____12925 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____12928 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____12928))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____12925
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
                          | uu____12939 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____12942 = desugar_term_aq env1 def2  in
                        (match uu____12942 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____12964 =
                                     let uu____12965 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____12965
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____12964
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
                  let uu____13006 =
                    let uu____13023 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13023 FStar_List.unzip  in
                  (match uu____13006 with
                   | (lbs1,aqss) ->
                       let uu____13165 = desugar_term_aq env' body  in
                       (match uu____13165 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13271  ->
                                    fun used_marker  ->
                                      match uu____13271 with
                                      | (_attr_opt,(f,uu____13345,uu____13346),uu____13347)
                                          ->
                                          let uu____13404 =
                                            let uu____13406 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13406  in
                                          if uu____13404
                                          then
                                            let uu____13430 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13448 =
                                                    FStar_Ident.string_of_ident
                                                      x
                                                     in
                                                  let uu____13450 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13448, "Local",
                                                    uu____13450)
                                              | FStar_Util.Inr l ->
                                                  let uu____13455 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13457 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13455, "Global",
                                                    uu____13457)
                                               in
                                            (match uu____13430 with
                                             | (nm,gl,rng) ->
                                                 let uu____13468 =
                                                   let uu____13474 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13474)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13468)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13482 =
                                let uu____13485 =
                                  let uu____13486 =
                                    let uu____13500 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13500)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13486  in
                                FStar_All.pipe_left mk1 uu____13485  in
                              (uu____13482,
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
              let uu____13602 = desugar_term_aq env t1  in
              match uu____13602 with
              | (t11,aq0) ->
                  let uu____13623 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13623 with
                   | (env1,binder,pat1) ->
                       let uu____13653 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13695 = desugar_term_aq env1 t2  in
                             (match uu____13695 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13717 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13717
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13718 =
                                    FStar_All.pipe_left mk1
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13718, aq))
                         | LocalBinder (x,uu____13759) ->
                             let uu____13760 = desugar_term_aq env1 t2  in
                             (match uu____13760 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13782;
                                         FStar_Syntax_Syntax.p = uu____13783;_},uu____13784)::[]
                                        -> body1
                                    | uu____13797 ->
                                        let uu____13800 =
                                          let uu____13807 =
                                            let uu____13808 =
                                              let uu____13831 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____13834 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____13831, uu____13834)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____13808
                                             in
                                          FStar_Syntax_Syntax.mk uu____13807
                                           in
                                        uu____13800
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____13871 =
                                    let uu____13874 =
                                      let uu____13875 =
                                        let uu____13889 =
                                          let uu____13892 =
                                            let uu____13893 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____13893]  in
                                          FStar_Syntax_Subst.close
                                            uu____13892 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____13889)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____13875
                                       in
                                    FStar_All.pipe_left mk1 uu____13874  in
                                  (uu____13871, aq))
                          in
                       (match uu____13653 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14001 = FStar_List.hd lbs  in
            (match uu____14001 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14045 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14045
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____14061 =
                let uu____14062 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14062  in
              mk1 uu____14061  in
            let uu____14063 = desugar_term_aq env t1  in
            (match uu____14063 with
             | (t1',aq1) ->
                 let uu____14074 = desugar_term_aq env t2  in
                 (match uu____14074 with
                  | (t2',aq2) ->
                      let uu____14085 = desugar_term_aq env t3  in
                      (match uu____14085 with
                       | (t3',aq3) ->
                           let uu____14096 =
                             let uu____14097 =
                               let uu____14098 =
                                 let uu____14121 =
                                   let uu____14138 =
                                     let uu____14153 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14153,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14167 =
                                     let uu____14184 =
                                       let uu____14199 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14199,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14184]  in
                                   uu____14138 :: uu____14167  in
                                 (t1', uu____14121)  in
                               FStar_Syntax_Syntax.Tm_match uu____14098  in
                             mk1 uu____14097  in
                           (uu____14096, (join_aqs [aq1; aq2; aq3])))))
        | FStar_Parser_AST.TryWith (e,branches) ->
            let r = top.FStar_Parser_AST.range  in
            let handler = FStar_Parser_AST.mk_function branches r r  in
            let body =
              FStar_Parser_AST.mk_function
                [((FStar_Parser_AST.mk_pattern
                     (FStar_Parser_AST.PatConst FStar_Const.Const_unit) r),
                   FStar_Pervasives_Native.None, e)] r r
               in
            let try_with_lid1 = FStar_Ident.lid_of_path ["try_with"] r  in
            let try_with1 =
              FStar_Parser_AST.mk_term (FStar_Parser_AST.Var try_with_lid1) r
                FStar_Parser_AST.Expr
               in
            let a1 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App
                   (try_with1, body, FStar_Parser_AST.Nothing)) r
                top.FStar_Parser_AST.level
               in
            let a2 =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.App (a1, handler, FStar_Parser_AST.Nothing))
                r top.FStar_Parser_AST.level
               in
            desugar_term_aq env a2
        | FStar_Parser_AST.Match (e,branches) ->
            let desugar_branch uu____14395 =
              match uu____14395 with
              | (pat,wopt,b) ->
                  let uu____14417 = desugar_match_pat env pat  in
                  (match uu____14417 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14448 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14448
                          in
                       let uu____14453 = desugar_term_aq env1 b  in
                       (match uu____14453 with
                        | (b1,aq) ->
                            let uu____14466 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14466, aq)))
               in
            let uu____14471 = desugar_term_aq env e  in
            (match uu____14471 with
             | (e1,aq) ->
                 let uu____14482 =
                   let uu____14513 =
                     let uu____14546 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14546 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14513
                     (fun uu____14764  ->
                        match uu____14764 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14482 with
                  | (brs,aqs) ->
                      let uu____14983 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14983, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15017 =
              let uu____15038 = is_comp_type env t  in
              if uu____15038
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15093 = desugar_term_aq env t  in
                 match uu____15093 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15017 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15185 = desugar_term_aq env e  in
                 (match uu____15185 with
                  | (e1,aq) ->
                      let uu____15196 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15196, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15235,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15278 = FStar_List.hd fields  in
              match uu____15278 with | (f,uu____15290) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15336  ->
                        match uu____15336 with
                        | (g,uu____15343) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15350,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15364 =
                         let uu____15370 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15370)
                          in
                       FStar_Errors.raise_error uu____15364
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
                  let uu____15381 =
                    let uu____15392 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15423  ->
                              match uu____15423 with
                              | (f,uu____15433) ->
                                  let uu____15434 =
                                    let uu____15435 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15435
                                     in
                                  (uu____15434, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15392)  in
                  FStar_Parser_AST.Construct uu____15381
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15453 =
                      let uu____15454 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15454  in
                    FStar_Parser_AST.mk_term uu____15453
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15456 =
                      let uu____15469 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15499  ->
                                match uu____15499 with
                                | (f,uu____15509) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15469)  in
                    FStar_Parser_AST.Record uu____15456  in
                  FStar_Parser_AST.Let
                    (FStar_Parser_AST.NoLetQualifier,
                      [(FStar_Pervasives_Native.None,
                         ((FStar_Parser_AST.mk_pattern
                             (FStar_Parser_AST.PatVar
                                (x, FStar_Pervasives_Native.None))
                             x.FStar_Ident.idRange), e))],
                      (FStar_Parser_AST.mk_term record1
                         top.FStar_Parser_AST.range
                         top.FStar_Parser_AST.level))
               in
            let recterm1 =
              FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____15569 = desugar_term_aq env recterm1  in
            (match uu____15569 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15585;
                         FStar_Syntax_Syntax.vars = uu____15586;_},args)
                      ->
                      let uu____15612 =
                        let uu____15613 =
                          let uu____15614 =
                            let uu____15631 =
                              let uu____15634 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15635 =
                                let uu____15638 =
                                  let uu____15639 =
                                    let uu____15646 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15646)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15639
                                   in
                                FStar_Pervasives_Native.Some uu____15638  in
                              FStar_Syntax_Syntax.fvar uu____15634
                                FStar_Syntax_Syntax.delta_constant
                                uu____15635
                               in
                            (uu____15631, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15614  in
                        FStar_All.pipe_left mk1 uu____15613  in
                      (uu____15612, s)
                  | uu____15675 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15679 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15679 with
              | (constrname,is_rec) ->
                  let uu____15698 = desugar_term_aq env e  in
                  (match uu____15698 with
                   | (e1,s) ->
                       let projname =
                         FStar_Syntax_Util.mk_field_projector_name_from_ident
                           constrname f.FStar_Ident.ident
                          in
                       let qual =
                         if is_rec
                         then
                           FStar_Pervasives_Native.Some
                             (FStar_Syntax_Syntax.Record_projector
                                (constrname, (f.FStar_Ident.ident)))
                         else FStar_Pervasives_Native.None  in
                       let uu____15718 =
                         let uu____15719 =
                           let uu____15720 =
                             let uu____15737 =
                               let uu____15740 =
                                 let uu____15741 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15741
                                  in
                               FStar_Syntax_Syntax.fvar uu____15740
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    Prims.int_one) qual
                                in
                             let uu____15743 =
                               let uu____15754 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15754]  in
                             (uu____15737, uu____15743)  in
                           FStar_Syntax_Syntax.Tm_app uu____15720  in
                         FStar_All.pipe_left mk1 uu____15719  in
                       (uu____15718, s))))
        | FStar_Parser_AST.NamedTyp (n1,e) ->
            ((let uu____15794 = FStar_Ident.range_of_id n1  in
              FStar_Errors.log_issue uu____15794
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15805 =
              let uu____15806 = FStar_Syntax_Subst.compress tm  in
              uu____15806.FStar_Syntax_Syntax.n  in
            (match uu____15805 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15814 =
                   let uu___2092_15815 =
                     let uu____15816 =
                       let uu____15818 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15818  in
                     FStar_Syntax_Util.exp_string uu____15816  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2092_15815.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2092_15815.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15814, noaqs)
             | uu____15819 ->
                 let uu____15820 =
                   let uu____15826 =
                     let uu____15828 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15828
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15826)  in
                 FStar_Errors.raise_error uu____15820
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15837 = desugar_term_aq env e  in
            (match uu____15837 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15849 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15849, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15854 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15855 =
              let uu____15856 =
                let uu____15863 = desugar_term env e  in (bv, uu____15863)
                 in
              [uu____15856]  in
            (uu____15854, uu____15855)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15888 =
              let uu____15889 =
                let uu____15890 =
                  let uu____15897 = desugar_term env e  in (uu____15897, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15890  in
              FStar_All.pipe_left mk1 uu____15889  in
            (uu____15888, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____15926 -> false  in
              let uu____15928 =
                let uu____15929 = unparen rel1  in
                uu____15929.FStar_Parser_AST.tm  in
              match uu____15928 with
              | FStar_Parser_AST.Op (id1,uu____15932) ->
                  let uu____15937 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id1
                     in
                  (match uu____15937 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____15945 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____15945 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id1 ->
                  let uu____15956 = FStar_Syntax_DsEnv.try_lookup_id env id1
                     in
                  (match uu____15956 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____15962 -> false  in
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
              let uu____15983 =
                let uu____15984 =
                  let uu____15991 =
                    let uu____15992 =
                      let uu____15993 =
                        let uu____16002 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16015 =
                          let uu____16016 =
                            let uu____16017 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16017  in
                          FStar_Parser_AST.mk_term uu____16016
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16002, uu____16015,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15993  in
                    FStar_Parser_AST.mk_term uu____15992
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15991)  in
                FStar_Parser_AST.Abs uu____15984  in
              FStar_Parser_AST.mk_term uu____15983
                rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
               in
            let rel1 = eta_and_annot rel  in
            let wild r =
              FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r
                FStar_Parser_AST.Expr
               in
            let init1 =
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
              let uu____16038 = FStar_List.last steps  in
              match uu____16038 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16041,uu____16042,last_expr)) -> last_expr
              | uu____16044 -> failwith "impossible: no last_expr on calc"
               in
            let step r =
              FStar_Parser_AST.mk_term
                (FStar_Parser_AST.Var FStar_Parser_Const.calc_step_lid) r
                FStar_Parser_AST.Expr
               in
            let finish1 =
              FStar_Parser_AST.mkApp
                (FStar_Parser_AST.mk_term
                   (FStar_Parser_AST.Var FStar_Parser_Const.calc_finish_lid)
                   top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
                [(rel1, FStar_Parser_AST.Nothing)] top.FStar_Parser_AST.range
               in
            let e =
              FStar_Parser_AST.mkApp init1
                [(init_expr, FStar_Parser_AST.Nothing)]
                FStar_Range.dummyRange
               in
            let uu____16072 =
              FStar_List.fold_left
                (fun uu____16090  ->
                   fun uu____16091  ->
                     match (uu____16090, uu____16091) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16114 = is_impl rel2  in
                           if uu____16114
                           then
                             let uu____16117 =
                               let uu____16124 =
                                 let uu____16129 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16129, FStar_Parser_AST.Nothing)  in
                               [uu____16124]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16117 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16141 =
                             let uu____16148 =
                               let uu____16155 =
                                 let uu____16162 =
                                   let uu____16169 =
                                     let uu____16174 = eta_and_annot rel2  in
                                     (uu____16174, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16175 =
                                     let uu____16182 =
                                       let uu____16189 =
                                         let uu____16194 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16194,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16195 =
                                         let uu____16202 =
                                           let uu____16207 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16207,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16202]  in
                                       uu____16189 :: uu____16195  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16182
                                      in
                                   uu____16169 :: uu____16175  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16162
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16155
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16148
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16141
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16072 with
             | (e1,uu____16245) ->
                 let e2 =
                   let uu____16247 =
                     let uu____16254 =
                       let uu____16261 =
                         let uu____16268 =
                           let uu____16273 = FStar_Parser_AST.thunk e1  in
                           (uu____16273, FStar_Parser_AST.Nothing)  in
                         [uu____16268]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16261  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16254  in
                   FStar_Parser_AST.mkApp finish1 uu____16247
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16290 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16291 = desugar_formula env top  in
            (uu____16291, noaqs)
        | uu____16292 ->
            let uu____16293 =
              let uu____16299 =
                let uu____16301 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16301  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16299)  in
            FStar_Errors.raise_error uu____16293 top.FStar_Parser_AST.range

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
           (fun uu____16345  ->
              match uu____16345 with
              | (a,imp) ->
                  let uu____16358 = desugar_term env a  in
                  arg_withimp_e imp uu____16358))

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
          let fail1 err = FStar_Errors.raise_error err r  in
          let is_requires uu____16395 =
            match uu____16395 with
            | (t1,uu____16402) ->
                let uu____16403 =
                  let uu____16404 = unparen t1  in
                  uu____16404.FStar_Parser_AST.tm  in
                (match uu____16403 with
                 | FStar_Parser_AST.Requires uu____16406 -> true
                 | uu____16415 -> false)
             in
          let is_ensures uu____16427 =
            match uu____16427 with
            | (t1,uu____16434) ->
                let uu____16435 =
                  let uu____16436 = unparen t1  in
                  uu____16436.FStar_Parser_AST.tm  in
                (match uu____16435 with
                 | FStar_Parser_AST.Ensures uu____16438 -> true
                 | uu____16447 -> false)
             in
          let is_app head1 uu____16465 =
            match uu____16465 with
            | (t1,uu____16473) ->
                let uu____16474 =
                  let uu____16475 = unparen t1  in
                  uu____16475.FStar_Parser_AST.tm  in
                (match uu____16474 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16478;
                        FStar_Parser_AST.level = uu____16479;_},uu____16480,uu____16481)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____16483 -> false)
             in
          let is_smt_pat uu____16495 =
            match uu____16495 with
            | (t1,uu____16502) ->
                let uu____16503 =
                  let uu____16504 = unparen t1  in
                  uu____16504.FStar_Parser_AST.tm  in
                (match uu____16503 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16508);
                               FStar_Parser_AST.range = uu____16509;
                               FStar_Parser_AST.level = uu____16510;_},uu____16511)::uu____16512::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["SMTPat"; "SMTPatT"; "SMTPatOr"])
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm = FStar_Parser_AST.Var
                                 smtpat;
                               FStar_Parser_AST.range = uu____16561;
                               FStar_Parser_AST.level = uu____16562;_},uu____16563)::uu____16564::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16597 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16632 = head_and_args t1  in
            match uu____16632 with
            | (head1,args) ->
                (match head1.FStar_Parser_AST.tm with
                 | FStar_Parser_AST.Name lemma when
                     (lemma.FStar_Ident.ident).FStar_Ident.idText = "Lemma"
                     ->
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
                     let thunk_ens uu____16725 =
                       match uu____16725 with
                       | (e,i) ->
                           let uu____16736 = FStar_Parser_AST.thunk e  in
                           (uu____16736, i)
                        in
                     let fail_lemma uu____16748 =
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
                           let uu____16854 =
                             let uu____16861 =
                               let uu____16868 = thunk_ens ens  in
                               [uu____16868; nil_pat]  in
                             req_true :: uu____16861  in
                           unit_tm :: uu____16854
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16915 =
                             let uu____16922 =
                               let uu____16929 = thunk_ens ens  in
                               [uu____16929; nil_pat]  in
                             req :: uu____16922  in
                           unit_tm :: uu____16915
                       | ens::smtpat::[] when
                           (((let uu____16978 = is_requires ens  in
                              Prims.op_Negation uu____16978) &&
                               (let uu____16981 = is_smt_pat ens  in
                                Prims.op_Negation uu____16981))
                              &&
                              (let uu____16984 = is_decreases ens  in
                               Prims.op_Negation uu____16984))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16986 =
                             let uu____16993 =
                               let uu____17000 = thunk_ens ens  in
                               [uu____17000; smtpat]  in
                             req_true :: uu____16993  in
                           unit_tm :: uu____16986
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17047 =
                             let uu____17054 =
                               let uu____17061 = thunk_ens ens  in
                               [uu____17061; nil_pat; dec]  in
                             req_true :: uu____17054  in
                           unit_tm :: uu____17047
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17121 =
                             let uu____17128 =
                               let uu____17135 = thunk_ens ens  in
                               [uu____17135; smtpat; dec]  in
                             req_true :: uu____17128  in
                           unit_tm :: uu____17121
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17195 =
                             let uu____17202 =
                               let uu____17209 = thunk_ens ens  in
                               [uu____17209; nil_pat; dec]  in
                             req :: uu____17202  in
                           unit_tm :: uu____17195
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17269 =
                             let uu____17276 =
                               let uu____17283 = thunk_ens ens  in
                               [uu____17283; smtpat]  in
                             req :: uu____17276  in
                           unit_tm :: uu____17269
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17348 =
                             let uu____17355 =
                               let uu____17362 = thunk_ens ens  in
                               [uu____17362; dec; smtpat]  in
                             req :: uu____17355  in
                           unit_tm :: uu____17348
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17424 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17424, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17452 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17452
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____17455 =
                       let uu____17462 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17462, [])  in
                     (uu____17455, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17480 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17480
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____17483 =
                       let uu____17490 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17490, [])  in
                     (uu____17483, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17512 =
                       let uu____17519 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17519, [])  in
                     (uu____17512, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17542 when allow_type_promotion ->
                     let default_effect =
                       let uu____17544 = FStar_Options.ml_ish ()  in
                       if uu____17544
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17550 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17550
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17557 =
                       let uu____17564 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17564, [])  in
                     (uu____17557, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17587 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17606 = pre_process_comp_typ t  in
          match uu____17606 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17658 =
                    let uu____17664 =
                      let uu____17666 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17666
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17664)
                     in
                  fail1 uu____17658)
               else ();
               (let is_universe uu____17682 =
                  match uu____17682 with
                  | (uu____17688,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17690 = FStar_Util.take is_universe args  in
                match uu____17690 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17749  ->
                           match uu____17749 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17756 =
                      let uu____17771 = FStar_List.hd args1  in
                      let uu____17780 = FStar_List.tl args1  in
                      (uu____17771, uu____17780)  in
                    (match uu____17756 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17835 =
                           let is_decrease uu____17874 =
                             match uu____17874 with
                             | (t1,uu____17885) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17896;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17897;_},uu____17898::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17937 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17835 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18054  ->
                                        match uu____18054 with
                                        | (t1,uu____18064) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18073,(arg,uu____18075)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18114 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18135 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18147 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18147
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18154 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18154
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18164 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18164
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18171 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18171
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18178 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18178
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18185 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18185
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18206 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18206
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
                                                    let uu____18297 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18297
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
                                              | uu____18318 -> pat  in
                                            let uu____18319 =
                                              let uu____18330 =
                                                let uu____18341 =
                                                  let uu____18350 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18350, aq)  in
                                                [uu____18341]  in
                                              ens :: uu____18330  in
                                            req :: uu____18319
                                        | uu____18391 -> rest2
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
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2417_18426 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2417_18426.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2417_18426.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2424_18480 = b  in
             {
               FStar_Parser_AST.b = (uu___2424_18480.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2424_18480.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2424_18480.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18509 body1 =
          match uu____18509 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18555::uu____18556) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18574 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2443_18601 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2443_18601.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2443_18601.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18664 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18664))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18695 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18695 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2456_18705 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2456_18705.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2456_18705.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18711 =
                     let uu____18714 =
                       let uu____18715 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18715]  in
                     no_annot_abs uu____18714 body2  in
                   FStar_All.pipe_left setpos uu____18711  in
                 let uu____18736 =
                   let uu____18737 =
                     let uu____18754 =
                       let uu____18757 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18757
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____18759 =
                       let uu____18770 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18770]  in
                     (uu____18754, uu____18759)  in
                   FStar_Syntax_Syntax.Tm_app uu____18737  in
                 FStar_All.pipe_left mk1 uu____18736)
        | uu____18809 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18874 = q (rest, pats, body)  in
              let uu____18877 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18874 uu____18877
                FStar_Parser_AST.Formula
               in
            let uu____18878 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____18878 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18889 -> failwith "impossible"  in
      let uu____18893 =
        let uu____18894 = unparen f  in uu____18894.FStar_Parser_AST.tm  in
      match uu____18893 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18907,uu____18908) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18932,uu____18933) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18989 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18989
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19033 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19033
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19097 -> desugar_term env f

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
          let uu____19108 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19108)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19113 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19113)
      | FStar_Parser_AST.TVariable x ->
          let uu____19117 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____19117)
      | FStar_Parser_AST.NoName t ->
          let uu____19121 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19121)
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
      fun uu___12_19129  ->
        match uu___12_19129 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19151 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19151, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19168 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19168 with
             | (env1,a1) ->
                 let uu____19185 =
                   let uu____19192 = trans_aqual env1 imp  in
                   ((let uu___2556_19198 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2556_19198.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2556_19198.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19192)
                    in
                 (uu____19185, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___13_19206  ->
      match uu___13_19206 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19210 =
            let uu____19211 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19211  in
          FStar_Pervasives_Native.Some uu____19210
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19239 =
        FStar_List.fold_left
          (fun uu____19272  ->
             fun b  ->
               match uu____19272 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2574_19316 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2574_19316.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2574_19316.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2574_19316.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19331 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19331 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2584_19349 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2584_19349.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2584_19349.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19350 =
                               let uu____19357 =
                                 let uu____19362 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19362)  in
                               uu____19357 :: out  in
                             (env2, uu____19350))
                    | uu____19373 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19239 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19461 =
          let uu____19462 = unparen t  in uu____19462.FStar_Parser_AST.tm  in
        match uu____19461 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____19463; FStar_Ident.ident = uu____19464;
              FStar_Ident.nsstr = uu____19465; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____19470 ->
            let uu____19471 =
              let uu____19477 =
                let uu____19479 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19479  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19477)  in
            FStar_Errors.raise_error uu____19471 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19496) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19498) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19501 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19519 = binder_ident b  in
         FStar_Common.list_of_option uu____19519) bs
  
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
               (fun uu___14_19556  ->
                  match uu___14_19556 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19561 -> false))
           in
        let quals2 q =
          let uu____19575 =
            (let uu____19579 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19579) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19575
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19596 = FStar_Ident.range_of_lid disc_name  in
                let uu____19597 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19596;
                  FStar_Syntax_Syntax.sigquals = uu____19597;
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
            let uu____19637 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19675  ->
                        match uu____19675 with
                        | (x,uu____19686) ->
                            let uu____19691 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19691 with
                             | (field_name,uu____19699) ->
                                 let only_decl =
                                   ((let uu____19704 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19704)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19706 =
                                        let uu____19708 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19708.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19706)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19726 =
                                       FStar_List.filter
                                         (fun uu___15_19730  ->
                                            match uu___15_19730 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19733 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19726
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_19748  ->
                                             match uu___16_19748 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19753 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19756 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19756;
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
                                      let uu____19763 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19763
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one
                                       in
                                    let lb =
                                      let uu____19774 =
                                        let uu____19779 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19779  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19774;
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
                                      let uu____19783 =
                                        let uu____19784 =
                                          let uu____19791 =
                                            let uu____19794 =
                                              let uu____19795 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19795
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19794]  in
                                          ((false, [lb]), uu____19791)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19784
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19783;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = [];
                                        FStar_Syntax_Syntax.sigopts =
                                          FStar_Pervasives_Native.None
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____19637 FStar_List.flatten
  
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
            (lid,uu____19844,t,uu____19846,n1,uu____19848) when
            let uu____19855 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____19855 ->
            let uu____19857 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____19857 with
             | (formals,uu____19875) ->
                 (match formals with
                  | [] -> []
                  | uu____19904 ->
                      let filter_records uu___17_19920 =
                        match uu___17_19920 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19923,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19935 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19937 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19937 with
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
                      let uu____19949 = FStar_Util.first_N n1 formals  in
                      (match uu____19949 with
                       | (uu____19978,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20012 -> []
  
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
                        let uu____20106 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20106
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20130 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20130
                        then
                          let uu____20136 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20136
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20140 =
                          let uu____20145 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20145  in
                        let uu____20146 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20152 =
                              let uu____20155 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20155  in
                            FStar_Syntax_Util.arrow typars uu____20152
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20160 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20140;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20146;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20160;
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
          let tycon_id uu___18_20214 =
            match uu___18_20214 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____20216,uu____20217) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____20227,uu____20228,uu____20229) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____20239,uu____20240,uu____20241) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____20263,uu____20264,uu____20265) -> id1
             in
          let binder_to_term1 b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20303) ->
                let uu____20304 =
                  let uu____20305 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20305  in
                FStar_Parser_AST.mk_term uu____20304 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20307 =
                  let uu____20308 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20308  in
                FStar_Parser_AST.mk_term uu____20307 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20310) ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
            | FStar_Parser_AST.TVariable a ->
                FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar a)
                  a.FStar_Ident.idRange FStar_Parser_AST.Type_level
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
              | uu____20341 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20349 =
                     let uu____20350 =
                       let uu____20357 = binder_to_term1 b  in
                       (out, uu____20357, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20350  in
                   FStar_Parser_AST.mk_term uu____20349
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___19_20369 =
            match uu___19_20369 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____20413  ->
                       match uu____20413 with
                       | (x,t) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20421 =
                    let uu____20422 =
                      let uu____20423 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____20423  in
                    FStar_Parser_AST.mk_term uu____20422
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20421 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____20430 = binder_idents parms  in id1 ::
                    uu____20430
                   in
                (FStar_List.iter
                   (fun uu____20443  ->
                      match uu____20443 with
                      | (f,uu____20449) ->
                          let uu____20450 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____20450
                          then
                            let uu____20455 =
                              let uu____20461 =
                                let uu____20463 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20463
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20461)
                               in
                            FStar_Errors.raise_error uu____20455
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____20469 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20469)))
            | uu____20523 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___20_20563 =
            match uu___20_20563 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20587 = typars_of_binders _env binders  in
                (match uu____20587 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20623 =
                         let uu____20624 =
                           let uu____20625 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20625  in
                         FStar_Parser_AST.mk_term uu____20624
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20623 binders  in
                     let qlid = FStar_Syntax_DsEnv.qualify _env id1  in
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
                     let uu____20634 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20634 with
                      | (_env1,uu____20651) ->
                          let uu____20658 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id1 FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20658 with
                           | (_env2,uu____20675) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20682 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20725 =
              FStar_List.fold_left
                (fun uu____20759  ->
                   fun uu____20760  ->
                     match (uu____20759, uu____20760) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20829 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20829 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20725 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20920 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20920
                | uu____20921 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20929 = desugar_abstract_tc quals env [] tc  in
              (match uu____20929 with
               | (uu____20942,uu____20943,se,uu____20945) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20948,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20967 =
                                 let uu____20969 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20969  in
                               if uu____20967
                               then
                                 let uu____20972 =
                                   let uu____20978 =
                                     let uu____20980 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20980
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20978)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20972
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
                           | uu____20993 ->
                               let uu____20994 =
                                 let uu____21001 =
                                   let uu____21002 =
                                     let uu____21017 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21017)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21002
                                    in
                                 FStar_Syntax_Syntax.mk uu____21001  in
                               uu____20994 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2867_21030 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2867_21030.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2867_21030.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2867_21030.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2867_21030.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21031 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____21046 = typars_of_binders env binders  in
              (match uu____21046 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21080 =
                           FStar_Util.for_some
                             (fun uu___21_21083  ->
                                match uu___21_21083 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21086 -> false) quals
                            in
                         if uu____21080
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21094 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21094
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21099 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_21105  ->
                               match uu___22_21105 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21108 -> false))
                        in
                     if uu____21099
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____21122 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21122
                     then
                       let uu____21128 =
                         let uu____21135 =
                           let uu____21136 = unparen t  in
                           uu____21136.FStar_Parser_AST.tm  in
                         match uu____21135 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____21157 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21187)::args_rev ->
                                   let uu____21199 =
                                     let uu____21200 = unparen last_arg  in
                                     uu____21200.FStar_Parser_AST.tm  in
                                   (match uu____21199 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21228 -> ([], args))
                               | uu____21237 -> ([], args)  in
                             (match uu____21157 with
                              | (cattributes,args1) ->
                                  let uu____21276 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21276))
                         | uu____21287 -> (t, [])  in
                       match uu____21128 with
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
                                  (fun uu___23_21310  ->
                                     match uu___23_21310 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21313 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21321)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21341 = tycon_record_as_variant trec  in
              (match uu____21341 with
               | (t,fs) ->
                   let uu____21358 =
                     let uu____21361 =
                       let uu____21362 =
                         let uu____21371 =
                           let uu____21374 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21374  in
                         (uu____21371, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21362  in
                     uu____21361 :: quals  in
                   desugar_tycon env d uu____21358 [t])
          | uu____21379::uu____21380 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21538 = et  in
                match uu____21538 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21748 ->
                         let trec = tc  in
                         let uu____21768 = tycon_record_as_variant trec  in
                         (match uu____21768 with
                          | (t,fs) ->
                              let uu____21824 =
                                let uu____21827 =
                                  let uu____21828 =
                                    let uu____21837 =
                                      let uu____21840 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21840  in
                                    (uu____21837, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21828
                                   in
                                uu____21827 :: quals1  in
                              collect_tcs uu____21824 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21918 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21918 with
                          | (env2,uu____21975,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____22112 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22112 with
                          | (env2,uu____22169,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22285 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22331 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22331 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_22783  ->
                             match uu___25_22783 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22837,uu____22838);
                                    FStar_Syntax_Syntax.sigrng = uu____22839;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22840;
                                    FStar_Syntax_Syntax.sigmeta = uu____22841;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22842;
                                    FStar_Syntax_Syntax.sigopts = uu____22843;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22905 =
                                     typars_of_binders env1 binders  in
                                   match uu____22905 with
                                   | (env2,tpars1) ->
                                       let uu____22932 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22932 with
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
                                 let uu____22961 =
                                   let uu____22972 =
                                     mk_typ_abbrev env1 d id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ([], uu____22972)  in
                                 [uu____22961]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____23008);
                                    FStar_Syntax_Syntax.sigrng = uu____23009;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23011;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23012;
                                    FStar_Syntax_Syntax.sigopts = uu____23013;_},constrs,tconstr,quals1)
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
                                 let uu____23104 = push_tparams env1 tpars
                                    in
                                 (match uu____23104 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23163  ->
                                             match uu____23163 with
                                             | (x,uu____23175) ->
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
                                        let uu____23186 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23186
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23209 =
                                        let uu____23228 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23305  ->
                                                  match uu____23305 with
                                                  | (id1,topt,of_notation) ->
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
                                                        let uu____23348 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23348
                                                         in
                                                      let name =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env1 id1
                                                         in
                                                      let quals2 =
                                                        FStar_All.pipe_right
                                                          tname_quals
                                                          (FStar_List.collect
                                                             (fun
                                                                uu___24_23359
                                                                 ->
                                                                match uu___24_23359
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23371
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23379 =
                                                        let uu____23390 =
                                                          let uu____23391 =
                                                            let uu____23392 =
                                                              let uu____23408
                                                                =
                                                                let uu____23409
                                                                  =
                                                                  let uu____23412
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23412
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23409
                                                                 in
                                                              (name, univs1,
                                                                uu____23408,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23392
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23391;
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
                                                        (tps, uu____23390)
                                                         in
                                                      (name, uu____23379)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23228
                                         in
                                      (match uu____23209 with
                                       | (constrNames,constrs1) ->
                                           ([],
                                             {
                                               FStar_Syntax_Syntax.sigel =
                                                 (FStar_Syntax_Syntax.Sig_inductive_typ
                                                    (tname, univs1, tpars, k,
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
                             | uu____23544 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23625  ->
                             match uu____23625 with | (uu____23636,se) -> se))
                      in
                   let uu____23650 =
                     let uu____23657 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23657 rng
                      in
                   (match uu____23650 with
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
                               (fun uu____23702  ->
                                  match uu____23702 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23750,tps,k,uu____23753,constrs)
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
                                      let uu____23774 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23789 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23806,uu____23807,uu____23808,uu____23809,uu____23810)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23817
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23789
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23821 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_23828  ->
                                                          match uu___26_23828
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23830 ->
                                                              true
                                                          | uu____23840 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23821))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23774
                                  | uu____23842 -> []))
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
      let uu____23879 =
        FStar_List.fold_left
          (fun uu____23914  ->
             fun b  ->
               match uu____23914 with
               | (env1,binders1) ->
                   let uu____23958 = desugar_binder env1 b  in
                   (match uu____23958 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____23981 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____23981 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24034 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23879 with
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
          let uu____24138 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_24145  ->
                    match uu___27_24145 with
                    | FStar_Syntax_Syntax.Reflectable uu____24147 -> true
                    | uu____24149 -> false))
             in
          if uu____24138
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24154 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24154
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
      fun head1  ->
        let warn1 uu____24205 =
          if warn
          then
            let uu____24207 =
              let uu____24213 =
                let uu____24215 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24215
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24213)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24207
          else ()  in
        let uu____24221 = FStar_Syntax_Util.head_and_args at  in
        match uu____24221 with
        | (hd1,args) ->
            let uu____24274 =
              let uu____24275 = FStar_Syntax_Subst.compress hd1  in
              uu____24275.FStar_Syntax_Syntax.n  in
            (match uu____24274 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24319)::[] ->
                      let uu____24344 =
                        let uu____24349 =
                          let uu____24358 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24358 a1  in
                        uu____24349 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24344 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24381 =
                             let uu____24387 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24387  in
                           (uu____24381, true)
                       | uu____24402 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24418 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24440 -> (FStar_Pervasives_Native.None, false))
  
let (get_fail_attr :
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
      let uu____24557 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24557 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24606 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24606 with | (res1,uu____24628) -> rebind res1 true)
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____24658 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____24658 with
        | FStar_Pervasives_Native.None  ->
            let uu____24661 =
              let uu____24667 =
                let uu____24669 =
                  let uu____24671 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____24671 " not found"  in
                Prims.op_Hat "Effect name " uu____24669  in
              (FStar_Errors.Fatal_EffectNotFound, uu____24667)  in
            FStar_Errors.raise_error uu____24661 r
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
        fun is_layered1  ->
          fun eff_name  ->
            fun eff_binders  ->
              fun eff_typ  ->
                fun eff_decls  ->
                  fun attrs  ->
                    let env0 = env  in
                    let monad_env =
                      FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                    let uu____24827 = desugar_binders monad_env eff_binders
                       in
                    match uu____24827 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____24866 =
                            let uu____24875 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24875  in
                          FStar_List.length uu____24866  in
                        (if is_layered1 && (num_indices <= Prims.int_one)
                         then
                           (let uu____24909 =
                              let uu____24915 =
                                let uu____24917 =
                                  let uu____24919 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____24919
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____24917  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____24915)
                               in
                            FStar_Errors.raise_error uu____24909
                              d.FStar_Parser_AST.drange)
                         else ();
                         (let for_free = num_indices = Prims.int_one  in
                          let mandatory_members =
                            let rr_members = ["repr"; "return"; "bind"]  in
                            if for_free
                            then rr_members
                            else
                              if is_layered1
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
                                (uu____24987,uu____24988,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____24990,uu____24991,uu____24992))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25007 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25010 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25022 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25022 mandatory_members)
                              eff_decls
                             in
                          match uu____25010 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25041 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25070  ->
                                        fun decl  ->
                                          match uu____25070 with
                                          | (env2,out) ->
                                              let uu____25090 =
                                                desugar_decl env2 decl  in
                                              (match uu____25090 with
                                               | (env3,ses) ->
                                                   let uu____25103 =
                                                     let uu____25106 =
                                                       FStar_List.hd ses  in
                                                     uu____25106 :: out  in
                                                   (env3, uu____25103)))
                                     (env1, []))
                                 in
                              (match uu____25041 with
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
                                                 (uu____25152,uu____25153,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25156,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25157,(def,uu____25159)::
                                                        (cps_type,uu____25161)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25162;
                                                     FStar_Parser_AST.level =
                                                       uu____25163;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25196 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25196 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25228 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25229 =
                                                        let uu____25230 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25230
                                                         in
                                                      let uu____25237 =
                                                        let uu____25238 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25238
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25228;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25229;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25237
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25245,uu____25246,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25249,defn))::[])
                                                 when for_free || is_layered1
                                                 ->
                                                 let uu____25265 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25265 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25297 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25298 =
                                                        let uu____25299 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25299
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25297;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25298;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25306 ->
                                                 FStar_Errors.raise_error
                                                   (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                     "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                   d1.FStar_Parser_AST.drange))
                                      in
                                   let eff_t1 =
                                     FStar_Syntax_Subst.close binders1 eff_t
                                      in
                                   let lookup1 s =
                                     let l =
                                       let uu____25325 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25325
                                        in
                                     let uu____25327 =
                                       let uu____25328 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25328
                                        in
                                     ([], uu____25327)  in
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
                                       let uu____25350 =
                                         let uu____25351 =
                                           let uu____25354 = lookup1 "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25354
                                            in
                                         let uu____25356 =
                                           let uu____25359 = lookup1 "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25359
                                            in
                                         let uu____25361 =
                                           let uu____25364 = lookup1 "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25364
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
                                             uu____25351;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25356;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25361
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25350
                                     else
                                       if is_layered1
                                       then
                                         (let to_comb uu____25398 =
                                            match uu____25398 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____25445 =
                                            let uu____25446 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____25448 =
                                              let uu____25453 =
                                                lookup1 "repr"  in
                                              FStar_All.pipe_right
                                                uu____25453 to_comb
                                               in
                                            let uu____25471 =
                                              let uu____25476 =
                                                lookup1 "return"  in
                                              FStar_All.pipe_right
                                                uu____25476 to_comb
                                               in
                                            let uu____25494 =
                                              let uu____25499 =
                                                lookup1 "bind"  in
                                              FStar_All.pipe_right
                                                uu____25499 to_comb
                                               in
                                            let uu____25517 =
                                              let uu____25522 =
                                                lookup1 "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____25522 to_comb
                                               in
                                            let uu____25540 =
                                              let uu____25545 =
                                                lookup1 "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____25545 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____25446;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____25448;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____25471;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____25494;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____25517;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____25540
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____25445)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___28_25568  ->
                                                 match uu___28_25568 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____25571 -> true
                                                 | uu____25573 -> false)
                                              qualifiers
                                             in
                                          let uu____25575 =
                                            let uu____25576 =
                                              lookup1 "return_wp"  in
                                            let uu____25578 =
                                              lookup1 "bind_wp"  in
                                            let uu____25580 =
                                              lookup1 "stronger"  in
                                            let uu____25582 =
                                              lookup1 "if_then_else"  in
                                            let uu____25584 =
                                              lookup1 "ite_wp"  in
                                            let uu____25586 =
                                              lookup1 "close_wp"  in
                                            let uu____25588 =
                                              lookup1 "trivial"  in
                                            let uu____25590 =
                                              if rr
                                              then
                                                let uu____25596 =
                                                  lookup1 "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25596
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25600 =
                                              if rr
                                              then
                                                let uu____25606 =
                                                  lookup1 "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25606
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25610 =
                                              if rr
                                              then
                                                let uu____25616 =
                                                  lookup1 "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25616
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____25576;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____25578;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____25580;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____25582;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____25584;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____25586;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____25588;
                                              FStar_Syntax_Syntax.repr =
                                                uu____25590;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____25600;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____25610
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____25575)
                                      in
                                   let sigel =
                                     let uu____25621 =
                                       let uu____25622 =
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
                                           uu____25622
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____25621
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
                                               let uu____25639 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____25639) env3)
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
                let uu____25662 = desugar_binders env1 eff_binders  in
                match uu____25662 with
                | (env2,binders) ->
                    let uu____25699 =
                      let uu____25710 = head_and_args defn  in
                      match uu____25710 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25747 ->
                                let uu____25748 =
                                  let uu____25754 =
                                    let uu____25756 =
                                      let uu____25758 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25758 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25756  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25754)
                                   in
                                FStar_Errors.raise_error uu____25748
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25764 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25794)::args_rev ->
                                let uu____25806 =
                                  let uu____25807 = unparen last_arg  in
                                  uu____25807.FStar_Parser_AST.tm  in
                                (match uu____25806 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25835 -> ([], args))
                            | uu____25844 -> ([], args)  in
                          (match uu____25764 with
                           | (cattributes,args1) ->
                               let uu____25887 = desugar_args env2 args1  in
                               let uu____25888 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25887, uu____25888))
                       in
                    (match uu____25699 with
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
                          (let uu____25928 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25928 with
                           | (ed_binders,uu____25942,ed_binders_opening) ->
                               let sub' shift_n uu____25961 =
                                 match uu____25961 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25976 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25976 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25980 =
                                       let uu____25981 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25981)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25980
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26002 =
                                   sub1 ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26003 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub1 ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26004 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26020 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26021 =
                                          let uu____26022 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26022
                                           in
                                        let uu____26037 =
                                          let uu____26038 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26038
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26020;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26021;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26037
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
                                     uu____26002;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26003;
                                   FStar_Syntax_Syntax.actions = uu____26004;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26054 =
                                   let uu____26057 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26057 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26054;
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
                                           let uu____26072 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26072) env3)
                                  in
                               let env5 =
                                 let uu____26074 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26074
                                 then
                                   let reflect_lid =
                                     let uu____26081 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26081
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
      let env0 =
        let uu____26098 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26098 FStar_Pervasives_Native.snd  in
      let uu____26110 = desugar_decl_noattrs env d  in
      match uu____26110 with
      | (env1,sigelts) ->
          let attrs =
            FStar_List.map (desugar_term env1) d.FStar_Parser_AST.attrs  in
          let val_attrs =
            match sigelts with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____26129;
                FStar_Syntax_Syntax.sigrng = uu____26130;
                FStar_Syntax_Syntax.sigquals = uu____26131;
                FStar_Syntax_Syntax.sigmeta = uu____26132;
                FStar_Syntax_Syntax.sigattrs = uu____26133;
                FStar_Syntax_Syntax.sigopts = uu____26134;_}::[] ->
                let uu____26147 =
                  let uu____26150 =
                    let uu____26153 = FStar_List.hd sigelts  in
                    FStar_Syntax_Util.lids_of_sigelt uu____26153  in
                  FStar_All.pipe_right uu____26150
                    (FStar_List.collect
                       (fun nm  ->
                          let uu____26161 =
                            FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                              env0 nm
                             in
                          FStar_Pervasives_Native.snd uu____26161))
                   in
                FStar_All.pipe_right uu____26147
                  (FStar_List.filter
                     (fun t  ->
                        let uu____26181 = get_fail_attr false t  in
                        FStar_Option.isNone uu____26181))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____26201;
                FStar_Syntax_Syntax.sigrng = uu____26202;
                FStar_Syntax_Syntax.sigquals = uu____26203;
                FStar_Syntax_Syntax.sigmeta = uu____26204;
                FStar_Syntax_Syntax.sigattrs = uu____26205;
                FStar_Syntax_Syntax.sigopts = uu____26206;_}::uu____26207 ->
                let uu____26232 =
                  let uu____26235 =
                    let uu____26238 = FStar_List.hd sigelts  in
                    FStar_Syntax_Util.lids_of_sigelt uu____26238  in
                  FStar_All.pipe_right uu____26235
                    (FStar_List.collect
                       (fun nm  ->
                          let uu____26246 =
                            FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                              env0 nm
                             in
                          FStar_Pervasives_Native.snd uu____26246))
                   in
                FStar_All.pipe_right uu____26232
                  (FStar_List.filter
                     (fun t  ->
                        let uu____26266 = get_fail_attr false t  in
                        FStar_Option.isNone uu____26266))
            | uu____26286 -> []  in
          let attrs1 = FStar_List.append attrs val_attrs  in
          let uu____26290 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = Prims.int_zero
                   then
                     let uu___3418_26300 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3418_26300.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3418_26300.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3418_26300.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3418_26300.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs1;
                       FStar_Syntax_Syntax.sigopts =
                         (uu___3418_26300.FStar_Syntax_Syntax.sigopts)
                     }
                   else
                     (let uu___3420_26303 = sigelt  in
                      let uu____26304 =
                        FStar_List.filter
                          (fun at  ->
                             let uu____26310 = get_fail_attr false at  in
                             FStar_Option.isNone uu____26310) attrs1
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3420_26303.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3420_26303.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3420_26303.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3420_26303.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____26304;
                        FStar_Syntax_Syntax.sigopts =
                          (uu___3420_26303.FStar_Syntax_Syntax.sigopts)
                      })) sigelts
             in
          (env1, uu____26290)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26336 = desugar_decl_aux env d  in
      match uu____26336 with
      | (env1,ses) ->
          let uu____26347 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26347)

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
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____26379 = FStar_Syntax_DsEnv.iface env  in
          if uu____26379
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26394 =
               let uu____26396 =
                 let uu____26398 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26399 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26398
                   uu____26399
                  in
               Prims.op_Negation uu____26396  in
             if uu____26394
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26413 =
                  let uu____26415 =
                    let uu____26417 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26417 lid  in
                  Prims.op_Negation uu____26415  in
                if uu____26413
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26431 =
                     let uu____26433 =
                       let uu____26435 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26435
                         lid
                        in
                     Prims.op_Negation uu____26433  in
                   if uu____26431
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26453 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26453, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26482)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26501 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____26510 =
            let uu____26515 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26515 tcs  in
          (match uu____26510 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26532 =
                   let uu____26533 =
                     let uu____26540 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26540  in
                   [uu____26533]  in
                 let uu____26553 =
                   let uu____26556 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26559 =
                     let uu____26570 =
                       let uu____26579 =
                         let uu____26580 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26580  in
                       FStar_Syntax_Syntax.as_arg uu____26579  in
                     [uu____26570]  in
                   FStar_Syntax_Util.mk_app uu____26556 uu____26559  in
                 FStar_Syntax_Util.abs uu____26532 uu____26553
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26620,id1))::uu____26622 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26625::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26629 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26629 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26635 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26635]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26656) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26666,uu____26667,uu____26668,uu____26669,uu____26670)
                     ->
                     let uu____26679 =
                       let uu____26680 =
                         let uu____26681 =
                           let uu____26688 = mkclass lid  in
                           (meths, uu____26688)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26681  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26680;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____26679]
                 | uu____26691 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26725;
                    FStar_Parser_AST.prange = uu____26726;_},uu____26727)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26737;
                    FStar_Parser_AST.prange = uu____26738;_},uu____26739)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26755;
                         FStar_Parser_AST.prange = uu____26756;_},uu____26757);
                    FStar_Parser_AST.prange = uu____26758;_},uu____26759)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26781;
                         FStar_Parser_AST.prange = uu____26782;_},uu____26783);
                    FStar_Parser_AST.prange = uu____26784;_},uu____26785)::[]
                   -> false
               | (p,uu____26814)::[] ->
                   let uu____26823 = is_app_pattern p  in
                   Prims.op_Negation uu____26823
               | uu____26825 -> false)
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
            let uu____26900 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26900 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26913 =
                     let uu____26914 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26914.FStar_Syntax_Syntax.n  in
                   match uu____26913 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26924) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____26955 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____26980  ->
                                match uu____26980 with
                                | (qs,ats) ->
                                    let uu____27007 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27007 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____26955 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27061::uu____27062 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27065 -> val_quals  in
                            let quals2 =
                              let uu____27069 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27102  ->
                                        match uu____27102 with
                                        | (uu____27116,(uu____27117,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27069
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____27137 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____27137
                              then
                                let uu____27143 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3598_27158 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3600_27160 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3600_27160.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3600_27160.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3598_27158.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3598_27158.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3598_27158.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3598_27158.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3598_27158.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3598_27158.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____27143)
                              else lbs  in
                            let names1 =
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
                                  (FStar_Syntax_Syntax.Sig_let (lbs1, names1));
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
                   | uu____27185 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27193 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27212 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27193 with
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
                       let uu___3623_27249 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3623_27249.FStar_Parser_AST.prange)
                       }
                   | uu____27256 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3627_27263 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3627_27263.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3627_27263.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____27299 id1 =
                   match uu____27299 with
                   | (env1,ses) ->
                       let main =
                         let uu____27320 =
                           let uu____27321 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____27321  in
                         FStar_Parser_AST.mk_term uu____27320
                           pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id1]  in
                       let projectee =
                         let uu____27324 = FStar_Ident.range_of_lid lid  in
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           uu____27324 FStar_Parser_AST.Expr
                          in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) main.FStar_Parser_AST.range
                           FStar_Parser_AST.Expr
                          in
                       let bv_pat =
                         let uu____27355 = FStar_Ident.range_of_id id1  in
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id1, FStar_Pervasives_Native.None))
                           uu____27355
                          in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____27373 = desugar_decl env1 id_decl  in
                       (match uu____27373 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27391 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27391 FStar_Util.set_elements
                    in
                 FStar_List.fold_left build_projection main_let bvs)
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
      | FStar_Parser_AST.Assume (id1,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
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
      | FStar_Parser_AST.Val (id1,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____27414 = close_fun env t  in
            desugar_term env uu____27414  in
          let quals1 =
            let uu____27418 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27418
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27430 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27430;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = attrs;
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])
      | FStar_Parser_AST.Exception (id1,t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term  in
                let uu____27443 =
                  let uu____27452 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27452]  in
                let uu____27471 =
                  let uu____27474 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27474
                   in
                FStar_Syntax_Util.arrow uu____27443 uu____27471
             in
          let l = FStar_Syntax_DsEnv.qualify env id1  in
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
      | FStar_Parser_AST.SubEffect l ->
          let src_ed =
            lookup_effect_lid env l.FStar_Parser_AST.msource
              d.FStar_Parser_AST.drange
             in
          let dst_ed =
            lookup_effect_lid env l.FStar_Parser_AST.mdest
              d.FStar_Parser_AST.drange
             in
          let uu____27540 =
            let uu____27542 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____27542  in
          if uu____27540
          then
            let uu____27549 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____27567 =
                    let uu____27570 =
                      let uu____27571 = desugar_term env t  in
                      ([], uu____27571)  in
                    FStar_Pervasives_Native.Some uu____27570  in
                  (uu____27567, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____27584 =
                    let uu____27587 =
                      let uu____27588 = desugar_term env wp  in
                      ([], uu____27588)  in
                    FStar_Pervasives_Native.Some uu____27587  in
                  let uu____27595 =
                    let uu____27598 =
                      let uu____27599 = desugar_term env t  in
                      ([], uu____27599)  in
                    FStar_Pervasives_Native.Some uu____27598  in
                  (uu____27584, uu____27595)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____27611 =
                    let uu____27614 =
                      let uu____27615 = desugar_term env t  in
                      ([], uu____27615)  in
                    FStar_Pervasives_Native.Some uu____27614  in
                  (FStar_Pervasives_Native.None, uu____27611)
               in
            (match uu____27549 with
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
                   let uu____27649 =
                     let uu____27652 =
                       let uu____27653 = desugar_term env t  in
                       ([], uu____27653)  in
                     FStar_Pervasives_Native.Some uu____27652  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____27649
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
             | uu____27660 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind1) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n1 = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____27673 =
            let uu____27674 =
              let uu____27675 =
                let uu____27676 =
                  let uu____27687 =
                    let uu____27688 = desugar_term env bind1  in
                    ([], uu____27688)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n1.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____27687,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____27676  in
              {
                FStar_Syntax_Syntax.sigel = uu____27675;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____27674]  in
          (env, uu____27673)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____27707 =
              let uu____27708 =
                let uu____27715 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27715, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27708  in
            {
              FStar_Syntax_Syntax.sigel = uu____27707;
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
      let uu____27742 =
        FStar_List.fold_left
          (fun uu____27762  ->
             fun d  ->
               match uu____27762 with
               | (env1,sigelts) ->
                   let uu____27782 = desugar_decl env1 d  in
                   (match uu____27782 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27742 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____27873) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27877;
               FStar_Syntax_Syntax.exports = uu____27878;
               FStar_Syntax_Syntax.is_interface = uu____27879;_},FStar_Parser_AST.Module
             (current_lid,uu____27881)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27890) ->
              let uu____27893 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27893
           in
        let uu____27898 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27940 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27940, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27962 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27962, mname, decls, false)
           in
        match uu____27898 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28004 = desugar_decls env2 decls  in
            (match uu____28004 with
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
          let uu____28072 =
            (FStar_Options.interactive ()) &&
              (let uu____28075 =
                 let uu____28077 =
                   let uu____28079 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28079  in
                 FStar_Util.get_file_extension uu____28077  in
               FStar_List.mem uu____28075 ["fsti"; "fsi"])
             in
          if uu____28072 then as_interface m else m  in
        let uu____28093 = desugar_modul_common curmod env m1  in
        match uu____28093 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28115 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28115, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28137 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28137 with
      | (env1,modul,pop_when_done) ->
          let uu____28154 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28154 with
           | (env2,modul1) ->
               ((let uu____28166 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28166
                 then
                   let uu____28169 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28169
                 else ());
                (let uu____28174 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28174, modul1))))
  
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
        (fun uu____28224  ->
           let uu____28225 = desugar_modul env modul  in
           match uu____28225 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28263  ->
           let uu____28264 = desugar_decls env decls  in
           match uu____28264 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28315  ->
             let uu____28316 = desugar_partial_modul modul env a_modul  in
             match uu____28316 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28411 ->
                  let t =
                    let uu____28421 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28421  in
                  let uu____28434 =
                    let uu____28435 = FStar_Syntax_Subst.compress t  in
                    uu____28435.FStar_Syntax_Syntax.n  in
                  (match uu____28434 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28447,uu____28448)
                       -> bs1
                   | uu____28473 -> failwith "Impossible")
               in
            let uu____28483 =
              let uu____28490 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28490
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28483 with
            | (binders,uu____28492,binders_opening) ->
                let erase_term t =
                  let uu____28500 =
                    let uu____28501 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28501  in
                  FStar_Syntax_Subst.close binders uu____28500  in
                let erase_tscheme uu____28519 =
                  match uu____28519 with
                  | (us,t) ->
                      let t1 =
                        let uu____28539 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28539 t  in
                      let uu____28542 =
                        let uu____28543 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28543  in
                      ([], uu____28542)
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
                    | uu____28566 ->
                        let bs =
                          let uu____28576 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28576  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28616 =
                          let uu____28617 =
                            let uu____28620 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28620  in
                          uu____28617.FStar_Syntax_Syntax.n  in
                        (match uu____28616 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28622,uu____28623) -> bs1
                         | uu____28648 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28656 =
                      let uu____28657 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28657  in
                    FStar_Syntax_Subst.close binders uu____28656  in
                  let uu___3900_28658 = action  in
                  let uu____28659 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28660 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3900_28658.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3900_28658.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28659;
                    FStar_Syntax_Syntax.action_typ = uu____28660
                  }  in
                let uu___3902_28661 = ed  in
                let uu____28662 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28663 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____28664 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____28665 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3902_28661.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3902_28661.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28662;
                  FStar_Syntax_Syntax.signature = uu____28663;
                  FStar_Syntax_Syntax.combinators = uu____28664;
                  FStar_Syntax_Syntax.actions = uu____28665;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3902_28661.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3909_28681 = se  in
                  let uu____28682 =
                    let uu____28683 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28683  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28682;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3909_28681.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3909_28681.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3909_28681.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3909_28681.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3909_28681.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28685 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28686 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28686 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28703 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28703
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28705 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28705)
  