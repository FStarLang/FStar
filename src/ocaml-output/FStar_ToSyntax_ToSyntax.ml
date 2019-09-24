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
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2339  ->
    match uu___3_2339 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2346 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2379  ->
    match uu____2379 with
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
      let uu____2461 =
        let uu____2478 =
          let uu____2481 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2481  in
        let uu____2482 =
          let uu____2493 =
            let uu____2502 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2502)  in
          [uu____2493]  in
        (uu____2478, uu____2482)  in
      FStar_Syntax_Syntax.Tm_app uu____2461  in
    FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None
      tm.FStar_Syntax_Syntax.pos
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2551 =
        let uu____2568 =
          let uu____2571 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2571  in
        let uu____2572 =
          let uu____2583 =
            let uu____2592 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2592)  in
          [uu____2583]  in
        (uu____2568, uu____2572)  in
      FStar_Syntax_Syntax.Tm_app uu____2551  in
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
          let uu____2655 =
            let uu____2672 =
              let uu____2675 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2675  in
            let uu____2676 =
              let uu____2687 =
                let uu____2696 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2696)  in
              let uu____2704 =
                let uu____2715 =
                  let uu____2724 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2724)  in
                [uu____2715]  in
              uu____2687 :: uu____2704  in
            (uu____2672, uu____2676)  in
          FStar_Syntax_Syntax.Tm_app uu____2655  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2784 =
        let uu____2799 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2818  ->
               match uu____2818 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2829;
                    FStar_Syntax_Syntax.index = uu____2830;
                    FStar_Syntax_Syntax.sort = t;_},uu____2832)
                   ->
                   let uu____2840 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2840) uu____2799
         in
      FStar_All.pipe_right bs uu____2784  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2856 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2874 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2902 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2923,uu____2924,bs,t,uu____2927,uu____2928)
                            ->
                            let uu____2937 = bs_univnames bs  in
                            let uu____2940 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2937 uu____2940
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2943,uu____2944,t,uu____2946,uu____2947,uu____2948)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2955 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2902 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___585_2964 = s  in
        let uu____2965 =
          let uu____2966 =
            let uu____2975 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2993,bs,t,lids1,lids2) ->
                          let uu___596_3006 = se  in
                          let uu____3007 =
                            let uu____3008 =
                              let uu____3025 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3026 =
                                let uu____3027 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3027 t  in
                              (lid, uvs, uu____3025, uu____3026, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____3008
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3007;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___596_3006.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___596_3006.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___596_3006.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___596_3006.FStar_Syntax_Syntax.sigattrs)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3041,t,tlid,n1,lids1) ->
                          let uu___606_3052 = se  in
                          let uu____3053 =
                            let uu____3054 =
                              let uu____3070 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3070, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3054  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3053;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___606_3052.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___606_3052.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___606_3052.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___606_3052.FStar_Syntax_Syntax.sigattrs)
                          }
                      | uu____3074 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2975, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2966  in
        {
          FStar_Syntax_Syntax.sigel = uu____2965;
          FStar_Syntax_Syntax.sigrng =
            (uu___585_2964.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___585_2964.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___585_2964.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___585_2964.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3081,t) ->
        let uvs =
          let uu____3084 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3084 FStar_Util.set_elements  in
        let uu___615_3089 = s  in
        let uu____3090 =
          let uu____3091 =
            let uu____3098 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3098)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3091  in
        {
          FStar_Syntax_Syntax.sigel = uu____3090;
          FStar_Syntax_Syntax.sigrng =
            (uu___615_3089.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___615_3089.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___615_3089.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___615_3089.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3122 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3125 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3132) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3165,(FStar_Util.Inl t,uu____3167),uu____3168)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3215,(FStar_Util.Inr c,uu____3217),uu____3218)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3265 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3266,(FStar_Util.Inl t,uu____3268),uu____3269) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3316,(FStar_Util.Inr c,uu____3318),uu____3319) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3366 -> empty_set  in
          FStar_Util.set_union uu____3122 uu____3125  in
        let all_lb_univs =
          let uu____3370 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3386 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3386) empty_set)
             in
          FStar_All.pipe_right uu____3370 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___670_3396 = s  in
        let uu____3397 =
          let uu____3398 =
            let uu____3405 =
              let uu____3406 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___673_3418 = lb  in
                        let uu____3419 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3422 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___673_3418.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3419;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___673_3418.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3422;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___673_3418.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___673_3418.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3406)  in
            (uu____3405, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3398  in
        {
          FStar_Syntax_Syntax.sigel = uu____3397;
          FStar_Syntax_Syntax.sigrng =
            (uu___670_3396.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___670_3396.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___670_3396.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___670_3396.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3431,fml) ->
        let uvs =
          let uu____3434 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3434 FStar_Util.set_elements  in
        let uu___681_3439 = s  in
        let uu____3440 =
          let uu____3441 =
            let uu____3448 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3448)  in
          FStar_Syntax_Syntax.Sig_assume uu____3441  in
        {
          FStar_Syntax_Syntax.sigel = uu____3440;
          FStar_Syntax_Syntax.sigrng =
            (uu___681_3439.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___681_3439.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___681_3439.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___681_3439.FStar_Syntax_Syntax.sigattrs)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3450,bs,c,flags) ->
        let uvs =
          let uu____3459 =
            let uu____3462 = bs_univnames bs  in
            let uu____3465 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3462 uu____3465  in
          FStar_All.pipe_right uu____3459 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___692_3473 = s  in
        let uu____3474 =
          let uu____3475 =
            let uu____3488 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3489 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3488, uu____3489, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3475  in
        {
          FStar_Syntax_Syntax.sigel = uu____3474;
          FStar_Syntax_Syntax.sigrng =
            (uu___692_3473.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___692_3473.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___692_3473.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___692_3473.FStar_Syntax_Syntax.sigattrs)
        }
    | uu____3492 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3500  ->
    match uu___4_3500 with
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
    | uu____3549 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = Prims.int_zero
      then u
      else
        (let uu____3570 = sum_to_universe u (n1 - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3570)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3596 =
      let uu____3597 = unparen t  in uu____3597.FStar_Parser_AST.tm  in
    match uu____3596 with
    | FStar_Parser_AST.Wild  ->
        let uu____3603 =
          let uu____3604 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3604  in
        FStar_Util.Inr uu____3603
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3617)) ->
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
        ((let uu____3649 =
            let uu____3651 = FStar_Ident.text_of_id op_plus  in
            uu____3651 = "+"  in
          ());
         (let u1 = desugar_maybe_non_constant_universe t1  in
          let u2 = desugar_maybe_non_constant_universe t2  in
          match (u1, u2) with
          | (FStar_Util.Inl n1,FStar_Util.Inl n2) -> FStar_Util.Inl (n1 + n2)
          | (FStar_Util.Inl n1,FStar_Util.Inr u) ->
              let uu____3714 = sum_to_universe u n1  in
              FStar_Util.Inr uu____3714
          | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
              let uu____3731 = sum_to_universe u n1  in
              FStar_Util.Inr uu____3731
          | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
              let uu____3747 =
                let uu____3753 =
                  let uu____3755 = FStar_Parser_AST.term_to_string t  in
                  Prims.op_Hat
                    "This universe might contain a sum of two universe variables "
                    uu____3755
                   in
                (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                  uu____3753)
                 in
              FStar_Errors.raise_error uu____3747 t.FStar_Parser_AST.range))
    | FStar_Parser_AST.App uu____3764 ->
        let rec aux t1 univargs =
          let uu____3801 =
            let uu____3802 = unparen t1  in uu____3802.FStar_Parser_AST.tm
             in
          match uu____3801 with
          | FStar_Parser_AST.App (t2,targ,uu____3810) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              ((let uu____3825 =
                  let uu____3827 = FStar_Ident.text_of_lid max_lid1  in
                  uu____3827 = "max"  in
                ());
               if
                 FStar_List.existsb
                   (fun uu___5_3843  ->
                      match uu___5_3843 with
                      | FStar_Util.Inr uu____3850 -> true
                      | uu____3853 -> false) univargs
               then
                 (let uu____3861 =
                    let uu____3862 =
                      FStar_List.map
                        (fun uu___6_3872  ->
                           match uu___6_3872 with
                           | FStar_Util.Inl n1 -> int_to_universe n1
                           | FStar_Util.Inr u -> u) univargs
                       in
                    FStar_Syntax_Syntax.U_max uu____3862  in
                  FStar_Util.Inr uu____3861)
               else
                 (let nargs =
                    FStar_List.map
                      (fun uu___7_3898  ->
                         match uu___7_3898 with
                         | FStar_Util.Inl n1 -> n1
                         | FStar_Util.Inr uu____3908 -> failwith "impossible")
                      univargs
                     in
                  let uu____3912 =
                    FStar_List.fold_left
                      (fun m  -> fun n1  -> if m > n1 then m else n1)
                      Prims.int_zero nargs
                     in
                  FStar_Util.Inl uu____3912))
          | uu____3928 ->
              let uu____3929 =
                let uu____3935 =
                  let uu____3937 =
                    let uu____3939 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3939 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3937  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3935)  in
              FStar_Errors.raise_error uu____3929 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3954 ->
        let uu____3955 =
          let uu____3961 =
            let uu____3963 =
              let uu____3965 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3965 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3963  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3961)  in
        FStar_Errors.raise_error uu____3955 t.FStar_Parser_AST.range
  
let rec (desugar_universe :
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
                   FStar_Syntax_Syntax.antiquotes = uu____4006;_});
            FStar_Syntax_Syntax.pos = uu____4007;
            FStar_Syntax_Syntax.vars = uu____4008;_})::uu____4009
        ->
        let uu____4040 =
          let uu____4046 =
            let uu____4048 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4048
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4046)  in
        FStar_Errors.raise_error uu____4040 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4054 ->
        let uu____4073 =
          let uu____4079 =
            let uu____4081 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4081
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4079)  in
        FStar_Errors.raise_error uu____4073 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4094 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4094) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4122 = FStar_List.hd fields  in
        match uu____4122 with
        | (f,uu____4132) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4144 =
                match uu____4144 with
                | (f',uu____4150) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4152 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4152
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
              (let uu____4162 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4162);
              (match () with | () -> record)))
  
let rec (desugar_data_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun env  ->
    fun p  ->
      let check_linear_pattern_variables pats r =
        let rec pat_vars p1 =
          match p1.FStar_Syntax_Syntax.v with
          | FStar_Syntax_Syntax.Pat_dot_term uu____4525 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4532 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4533 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4535,pats1) ->
              let aux out uu____4576 =
                match uu____4576 with
                | (p2,uu____4589) ->
                    let intersection =
                      let uu____4599 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4599 out  in
                    let uu____4602 = FStar_Util.set_is_empty intersection  in
                    if uu____4602
                    then
                      let uu____4607 = pat_vars p2  in
                      FStar_Util.set_union out uu____4607
                    else
                      (let duplicate_bv =
                         let uu____4613 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4613  in
                       let uu____4616 =
                         let uu____4622 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4622)
                          in
                       FStar_Errors.raise_error uu____4616 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4646 = pat_vars p1  in
            FStar_All.pipe_right uu____4646 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4674 =
                let uu____4676 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4676  in
              if uu____4674
              then ()
              else
                (let nonlinear_vars =
                   let uu____4685 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4685  in
                 let first_nonlinear_var =
                   let uu____4689 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4689  in
                 let uu____4692 =
                   let uu____4698 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4698)  in
                 FStar_Errors.raise_error uu____4692 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4726 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4726 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4743 ->
            let uu____4746 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4746 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4897 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4921 =
              let uu____4922 =
                let uu____4923 =
                  let uu____4930 =
                    let uu____4931 =
                      let uu____4937 =
                        FStar_Parser_AST.compile_op Prims.int_zero
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4937, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4931  in
                  (uu____4930, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4923  in
              {
                FStar_Parser_AST.pat = uu____4922;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4921
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4957 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4960 = aux loc env1 p2  in
              match uu____4960 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___929_5049 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___931_5054 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___931_5054.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___931_5054.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___929_5049.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___935_5056 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___937_5061 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___937_5061.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___937_5061.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___935_5056.FStar_Syntax_Syntax.p)
                        }
                    | uu____5062 when top -> p4
                    | uu____5063 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____5068 =
                    match binder with
                    | LetBinder uu____5089 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____5114 = close_fun env1 t  in
                          desugar_term env1 uu____5114  in
                        let x1 =
                          let uu___948_5116 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___948_5116.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___948_5116.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____5068 with
                   | (annots',binder1) ->
                       (loc1, env', binder1, p3,
                         (FStar_List.append annots' annots), imp))))
        | FStar_Parser_AST.PatWild aq ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5184 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____5184, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5198 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5198, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5222 = resolvex loc env1 x  in
            (match uu____5222 with
             | (loc1,env2,xbv) ->
                 let uu____5251 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5251, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5274 = resolvex loc env1 x  in
            (match uu____5274 with
             | (loc1,env2,xbv) ->
                 let uu____5303 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5303, [], imp))
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
            let uu____5318 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5318, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5348;_},args)
            ->
            let uu____5354 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5415  ->
                     match uu____5415 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5496 = aux loc1 env2 arg  in
                         (match uu____5496 with
                          | (loc2,env3,uu____5543,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5354 with
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
                 let uu____5675 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5675, annots, false))
        | FStar_Parser_AST.PatApp uu____5693 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5724 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5775  ->
                     match uu____5775 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5836 = aux loc1 env2 pat  in
                         (match uu____5836 with
                          | (loc2,env3,uu____5878,pat1,ans,uu____5881) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5724 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5978 =
                     let uu____5981 =
                       let uu____5988 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5988  in
                     let uu____5989 =
                       let uu____5990 =
                         let uu____6004 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____6004, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5990  in
                     FStar_All.pipe_left uu____5981 uu____5989  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____6038 =
                            let uu____6039 =
                              let uu____6053 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____6053, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____6039  in
                          FStar_All.pipe_left (pos_r r) uu____6038) pats1
                     uu____5978
                    in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)), pat,
                   annots, false))
        | FStar_Parser_AST.PatTuple (args,dep1) ->
            let uu____6111 =
              FStar_List.fold_left
                (fun uu____6171  ->
                   fun p2  ->
                     match uu____6171 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6253 = aux loc1 env2 p2  in
                         (match uu____6253 with
                          | (loc2,env3,uu____6300,pat,ans,uu____6303) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____6111 with
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
                   | uu____6469 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6472 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6472, annots, false))
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
                   (fun uu____6553  ->
                      match uu____6553 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6583  ->
                      match uu____6583 with
                      | (f,uu____6589) ->
                          let uu____6590 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6616  ->
                                    match uu____6616 with
                                    | (g,uu____6623) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6590 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6629,p2) ->
                               p2)))
               in
            let app =
              let uu____6636 =
                let uu____6637 =
                  let uu____6644 =
                    let uu____6645 =
                      let uu____6646 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6646  in
                    FStar_Parser_AST.mk_pattern uu____6645
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6644, args)  in
                FStar_Parser_AST.PatApp uu____6637  in
              FStar_Parser_AST.mk_pattern uu____6636
                p1.FStar_Parser_AST.prange
               in
            let uu____6649 = aux loc env1 app  in
            (match uu____6649 with
             | (env2,e,b,p2,annots,uu____6695) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6735 =
                         let uu____6736 =
                           let uu____6750 =
                             let uu___1096_6751 = fv  in
                             let uu____6752 =
                               let uu____6755 =
                                 let uu____6756 =
                                   let uu____6763 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6763)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6756
                                  in
                               FStar_Pervasives_Native.Some uu____6755  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1096_6751.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1096_6751.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6752
                             }  in
                           (uu____6750, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6736  in
                       FStar_All.pipe_left pos uu____6735
                   | uu____6789 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6875 = aux' true loc env1 p2  in
            (match uu____6875 with
             | (loc1,env2,var,p3,ans,uu____6919) ->
                 let uu____6934 =
                   FStar_List.fold_left
                     (fun uu____6983  ->
                        fun p4  ->
                          match uu____6983 with
                          | (loc2,env3,ps1) ->
                              let uu____7048 = aux' true loc2 env3 p4  in
                              (match uu____7048 with
                               | (loc3,env4,uu____7089,p5,ans1,uu____7092) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6934 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7253 ->
            let uu____7254 = aux' true loc env1 p1  in
            (match uu____7254 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7351 = aux_maybe_or env p  in
      match uu____7351 with
      | (env1,b,pats) ->
          ((let uu____7406 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7406
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
        let mklet x ty tacopt =
          let uu____7479 =
            let uu____7480 =
              let uu____7491 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7491, (ty, tacopt))  in
            LetBinder uu____7480  in
          (env, uu____7479, [])  in
        let op_to_ident x =
          let uu____7508 =
            let uu____7514 =
              FStar_Parser_AST.compile_op Prims.int_zero x.FStar_Ident.idText
                x.FStar_Ident.idRange
               in
            (uu____7514, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7508  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7536 = op_to_ident x  in
              mklet uu____7536 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7538) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7544;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7560 = op_to_ident x  in
              let uu____7561 = desugar_term env t  in
              mklet uu____7560 uu____7561 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7563);
                 FStar_Parser_AST.prange = uu____7564;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7584 = desugar_term env t  in
              mklet x uu____7584 tacopt1
          | uu____7585 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7598 = desugar_data_pat env p  in
           match uu____7598 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7627;
                      FStar_Syntax_Syntax.p = uu____7628;_},uu____7629)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7642;
                      FStar_Syntax_Syntax.p = uu____7643;_},uu____7644)::[]
                     -> []
                 | uu____7657 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    FStar_Syntax_DsEnv.env ->
      FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7665  ->
    fun env  ->
      fun pat  ->
        let uu____7669 = desugar_data_pat env pat  in
        match uu____7669 with | (env1,uu____7685,pat1) -> (env1, pat1)

and (desugar_match_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_match_pat_maybe_top false env p

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
      let uu____7707 = desugar_term_aq env e  in
      match uu____7707 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7726 = desugar_typ_aq env e  in
      match uu____7726 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7736  ->
        fun range  ->
          match uu____7736 with
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
              ((let uu____7758 =
                  let uu____7760 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7760  in
                if uu____7758
                then
                  let uu____7763 =
                    let uu____7769 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7769)  in
                  FStar_Errors.log_issue range uu____7763
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
                  let uu____7790 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7790 range  in
                let lid1 =
                  let uu____7794 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7794 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7804 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7804 range  in
                           let private_fv =
                             let uu____7806 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7806 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1266_7807 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1266_7807.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1266_7807.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7808 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7812 =
                        let uu____7818 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7818)
                         in
                      FStar_Errors.raise_error uu____7812 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7838 =
                  let uu____7845 =
                    let uu____7846 =
                      let uu____7863 =
                        let uu____7874 =
                          let uu____7883 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7883)  in
                        [uu____7874]  in
                      (lid1, uu____7863)  in
                    FStar_Syntax_Syntax.Tm_app uu____7846  in
                  FStar_Syntax_Syntax.mk uu____7845  in
                uu____7838 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7931 =
          let uu____7932 = unparen t  in uu____7932.FStar_Parser_AST.tm  in
        match uu____7931 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7933; FStar_Ident.ident = uu____7934;
              FStar_Ident.nsstr = uu____7935; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7940 ->
            let uu____7941 =
              let uu____7947 =
                let uu____7949 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____7949  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7947)  in
            FStar_Errors.raise_error uu____7941 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes

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
          let uu___1293_8036 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1293_8036.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1293_8036.FStar_Syntax_Syntax.vars)
          }  in
        let uu____8039 =
          let uu____8040 = unparen top  in uu____8040.FStar_Parser_AST.tm  in
        match uu____8039 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____8045 ->
            let uu____8054 = desugar_formula env top  in (uu____8054, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____8063 = desugar_formula env t  in (uu____8063, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8072 = desugar_formula env t  in (uu____8072, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8099 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8099, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8101 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8101, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8110 =
                let uu____8111 =
                  let uu____8118 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8118, args)  in
                FStar_Parser_AST.Op uu____8111  in
              FStar_Parser_AST.mk_term uu____8110 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8123 =
              let uu____8124 =
                let uu____8125 =
                  let uu____8132 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8132, [e])  in
                FStar_Parser_AST.Op uu____8125  in
              FStar_Parser_AST.mk_term uu____8124 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8123
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8144 = FStar_Ident.text_of_id op_star  in
             uu____8144 = "*") &&
              (let uu____8149 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____8149 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8166;_},t1::t2::[])
                  when
                  let uu____8172 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8172 FStar_Option.isNone ->
                  let uu____8179 = flatten1 t1  in
                  FStar_List.append uu____8179 [t2]
              | uu____8182 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1341_8187 = top  in
              let uu____8188 =
                let uu____8189 =
                  let uu____8200 =
                    FStar_List.map (fun _8211  -> FStar_Util.Inr _8211) terms
                     in
                  (uu____8200, rhs)  in
                FStar_Parser_AST.Sum uu____8189  in
              {
                FStar_Parser_AST.tm = uu____8188;
                FStar_Parser_AST.range =
                  (uu___1341_8187.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1341_8187.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8219 =
              let uu____8220 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8220  in
            (uu____8219, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8226 =
              let uu____8232 =
                let uu____8234 =
                  let uu____8236 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8236 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8234  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8232)  in
            FStar_Errors.raise_error uu____8226 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8251 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8251 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8258 =
                   let uu____8264 =
                     let uu____8266 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8266
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8264)
                    in
                 FStar_Errors.raise_error uu____8258
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8281 =
                     let uu____8306 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8368 = desugar_term_aq env t  in
                               match uu____8368 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8306 FStar_List.unzip  in
                   (match uu____8281 with
                    | (args1,aqs) ->
                        let uu____8501 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8501, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8518)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8535 =
              let uu___1370_8536 = top  in
              let uu____8537 =
                let uu____8538 =
                  let uu____8545 =
                    let uu___1372_8546 = top  in
                    let uu____8547 =
                      let uu____8548 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8548  in
                    {
                      FStar_Parser_AST.tm = uu____8547;
                      FStar_Parser_AST.range =
                        (uu___1372_8546.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1372_8546.FStar_Parser_AST.level)
                    }  in
                  (uu____8545, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8538  in
              {
                FStar_Parser_AST.tm = uu____8537;
                FStar_Parser_AST.range =
                  (uu___1370_8536.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1370_8536.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8535
        | FStar_Parser_AST.Construct (n1,(a,uu____8556)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8576 =
                let uu___1382_8577 = top  in
                let uu____8578 =
                  let uu____8579 =
                    let uu____8586 =
                      let uu___1384_8587 = top  in
                      let uu____8588 =
                        let uu____8589 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8589  in
                      {
                        FStar_Parser_AST.tm = uu____8588;
                        FStar_Parser_AST.range =
                          (uu___1384_8587.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1384_8587.FStar_Parser_AST.level)
                      }  in
                    (uu____8586, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8579  in
                {
                  FStar_Parser_AST.tm = uu____8578;
                  FStar_Parser_AST.range =
                    (uu___1382_8577.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1382_8577.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8576))
        | FStar_Parser_AST.Construct (n1,(a,uu____8597)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8614 =
              let uu___1393_8615 = top  in
              let uu____8616 =
                let uu____8617 =
                  let uu____8624 =
                    let uu___1395_8625 = top  in
                    let uu____8626 =
                      let uu____8627 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8627  in
                    {
                      FStar_Parser_AST.tm = uu____8626;
                      FStar_Parser_AST.range =
                        (uu___1395_8625.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1395_8625.FStar_Parser_AST.level)
                    }  in
                  (uu____8624, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8617  in
              {
                FStar_Parser_AST.tm = uu____8616;
                FStar_Parser_AST.range =
                  (uu___1393_8615.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1393_8615.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8614
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8633; FStar_Ident.ident = uu____8634;
              FStar_Ident.nsstr = uu____8635; FStar_Ident.str = "Type0";_}
            ->
            let uu____8640 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8640, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8641; FStar_Ident.ident = uu____8642;
              FStar_Ident.nsstr = uu____8643; FStar_Ident.str = "Type";_}
            ->
            let uu____8648 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8648, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8649; FStar_Ident.ident = uu____8650;
               FStar_Ident.nsstr = uu____8651; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8671 =
              let uu____8672 =
                let uu____8673 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8673  in
              mk1 uu____8672  in
            (uu____8671, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8674; FStar_Ident.ident = uu____8675;
              FStar_Ident.nsstr = uu____8676; FStar_Ident.str = "Effect";_}
            ->
            let uu____8681 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8681, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8682; FStar_Ident.ident = uu____8683;
              FStar_Ident.nsstr = uu____8684; FStar_Ident.str = "True";_}
            ->
            let uu____8689 =
              let uu____8690 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8690
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8689, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8691; FStar_Ident.ident = uu____8692;
              FStar_Ident.nsstr = uu____8693; FStar_Ident.str = "False";_}
            ->
            let uu____8698 =
              let uu____8699 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8699
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8698, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8702;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8705 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8705 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8714 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         Prims.int_one) FStar_Pervasives_Native.None
                     in
                  (uu____8714, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8716 =
                    let uu____8718 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8718 txt
                     in
                  failwith uu____8716))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8727 = desugar_name mk1 setpos env true l  in
              (uu____8727, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8736 = desugar_name mk1 setpos env true l  in
              (uu____8736, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8754 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8754 with
                | FStar_Pervasives_Native.Some uu____8764 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8772 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8772 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8790 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8811 =
                    let uu____8812 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8812  in
                  (uu____8811, noaqs)
              | uu____8818 ->
                  let uu____8826 =
                    let uu____8832 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8832)  in
                  FStar_Errors.raise_error uu____8826
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8842 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8842 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8849 =
                    let uu____8855 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8855)
                     in
                  FStar_Errors.raise_error uu____8849
                    top.FStar_Parser_AST.range
              | uu____8863 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8867 = desugar_name mk1 setpos env true lid'  in
                  (uu____8867, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8889 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8889 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8908 ->
                       let uu____8915 =
                         FStar_Util.take
                           (fun uu____8939  ->
                              match uu____8939 with
                              | (uu____8945,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8915 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8990 =
                              let uu____9015 =
                                FStar_List.map
                                  (fun uu____9058  ->
                                     match uu____9058 with
                                     | (t,imp) ->
                                         let uu____9075 =
                                           desugar_term_aq env t  in
                                         (match uu____9075 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____9015
                                FStar_List.unzip
                               in
                            (match uu____8990 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9218 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9218, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9237 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9237 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9248 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9276  ->
                 match uu___8_9276 with
                 | FStar_Util.Inr uu____9282 -> true
                 | uu____9284 -> false) binders
            ->
            let terms =
              let uu____9293 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9310  ->
                        match uu___9_9310 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9316 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9293 [t]  in
            let uu____9318 =
              let uu____9343 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9400 = desugar_typ_aq env t1  in
                        match uu____9400 with
                        | (t',aq) ->
                            let uu____9411 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9411, aq)))
                 in
              FStar_All.pipe_right uu____9343 FStar_List.unzip  in
            (match uu____9318 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9521 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9521
                    in
                 let uu____9530 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9530, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9557 =
              let uu____9574 =
                let uu____9581 =
                  let uu____9588 =
                    FStar_All.pipe_left (fun _9597  -> FStar_Util.Inl _9597)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9588]  in
                FStar_List.append binders uu____9581  in
              FStar_List.fold_left
                (fun uu____9642  ->
                   fun b  ->
                     match uu____9642 with
                     | (env1,tparams,typs) ->
                         let uu____9703 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9718 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9718)
                            in
                         (match uu____9703 with
                          | (xopt,t1) ->
                              let uu____9743 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9752 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9752)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9743 with
                               | (env2,x) ->
                                   let uu____9772 =
                                     let uu____9775 =
                                       let uu____9778 =
                                         let uu____9779 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9779
                                          in
                                       [uu____9778]  in
                                     FStar_List.append typs uu____9775  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1554_9805 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1554_9805.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1554_9805.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9772)))) (env, [], []) uu____9574
               in
            (match uu____9557 with
             | (env1,uu____9833,targs) ->
                 let tup =
                   let uu____9856 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9856
                    in
                 let uu____9857 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9857, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9876 = uncurry binders t  in
            (match uu____9876 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9920 =
                   match uu___10_9920 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9937 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9937
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9961 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9961 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9994 = aux env [] bs  in (uu____9994, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____10003 = desugar_binder env b  in
            (match uu____10003 with
             | (FStar_Pervasives_Native.None ,uu____10014) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____10029 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____10029 with
                  | ((x,uu____10045),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____10058 =
                        let uu____10059 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____10059  in
                      (uu____10058, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10138 = FStar_Util.set_is_empty i  in
                    if uu____10138
                    then
                      let uu____10143 = FStar_Util.set_union acc set1  in
                      aux uu____10143 sets2
                    else
                      (let uu____10148 =
                         let uu____10149 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10149  in
                       FStar_Pervasives_Native.Some uu____10148)
                 in
              let uu____10152 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10152 sets  in
            ((let uu____10156 = check_disjoint bvss  in
              match uu____10156 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10160 =
                    let uu____10166 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10166)
                     in
                  let uu____10170 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10160 uu____10170);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10178 =
                FStar_List.fold_left
                  (fun uu____10198  ->
                     fun pat  ->
                       match uu____10198 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10224,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10234 =
                                  let uu____10237 = free_type_vars env1 t  in
                                  FStar_List.append uu____10237 ftvs  in
                                (env1, uu____10234)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10242,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10253 =
                                  let uu____10256 = free_type_vars env1 t  in
                                  let uu____10259 =
                                    let uu____10262 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10262 ftvs  in
                                  FStar_List.append uu____10256 uu____10259
                                   in
                                (env1, uu____10253)
                            | uu____10267 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10178 with
              | (uu____10276,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10288 =
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
                    FStar_List.append uu____10288 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___11_10345 =
                    match uu___11_10345 with
                    | [] ->
                        let uu____10372 = desugar_term_aq env1 body  in
                        (match uu____10372 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10409 =
                                       let uu____10410 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10410
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10409
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
                             let uu____10479 =
                               let uu____10482 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10482  in
                             (uu____10479, aq))
                    | p::rest ->
                        let uu____10497 = desugar_binding_pat env1 p  in
                        (match uu____10497 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10531)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10546 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10555 =
                               match b with
                               | LetBinder uu____10596 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10665) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10719 =
                                           let uu____10728 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10728, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10719
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10790,uu____10791) ->
                                              let tup2 =
                                                let uu____10793 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10793
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10798 =
                                                  let uu____10805 =
                                                    let uu____10806 =
                                                      let uu____10823 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10826 =
                                                        let uu____10837 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10846 =
                                                          let uu____10857 =
                                                            let uu____10866 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10866
                                                             in
                                                          [uu____10857]  in
                                                        uu____10837 ::
                                                          uu____10846
                                                         in
                                                      (uu____10823,
                                                        uu____10826)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10806
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10805
                                                   in
                                                uu____10798
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10914 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10914
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10965,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10967,pats)) ->
                                              let tupn =
                                                let uu____11012 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____11012
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____11025 =
                                                  let uu____11026 =
                                                    let uu____11043 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____11046 =
                                                      let uu____11057 =
                                                        let uu____11068 =
                                                          let uu____11077 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____11077
                                                           in
                                                        [uu____11068]  in
                                                      FStar_List.append args
                                                        uu____11057
                                                       in
                                                    (uu____11043,
                                                      uu____11046)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11026
                                                   in
                                                mk1 uu____11025  in
                                              let p2 =
                                                let uu____11125 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11125
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11172 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10555 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11266,uu____11267,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11289 =
                let uu____11290 = unparen e  in
                uu____11290.FStar_Parser_AST.tm  in
              match uu____11289 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11300 ->
                  let uu____11301 = desugar_term_aq env e  in
                  (match uu____11301 with
                   | (head1,aq) ->
                       let uu____11314 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11314, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11321 ->
            let rec aux args aqs e =
              let uu____11398 =
                let uu____11399 = unparen e  in
                uu____11399.FStar_Parser_AST.tm  in
              match uu____11398 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11417 = desugar_term_aq env t  in
                  (match uu____11417 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11465 ->
                  let uu____11466 = desugar_term_aq env e  in
                  (match uu____11466 with
                   | (head1,aq) ->
                       let uu____11487 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11487, (join_aqs (aq :: aqs))))
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
            let uu____11550 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11550
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
            let uu____11602 = desugar_term_aq env t  in
            (match uu____11602 with
             | (tm,s) ->
                 let uu____11613 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11613, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11619 =
              let uu____11632 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11632 then desugar_typ_aq else desugar_term_aq  in
            uu____11619 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11691 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11834  ->
                        match uu____11834 with
                        | (attr_opt,(p,def)) ->
                            let uu____11892 = is_app_pattern p  in
                            if uu____11892
                            then
                              let uu____11925 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11925, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____12008 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____12008, def1)
                               | uu____12053 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12091);
                                           FStar_Parser_AST.prange =
                                             uu____12092;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12141 =
                                            let uu____12162 =
                                              let uu____12167 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12167  in
                                            (uu____12162, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12141, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12259) ->
                                        if top_level
                                        then
                                          let uu____12295 =
                                            let uu____12316 =
                                              let uu____12321 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12321  in
                                            (uu____12316, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12295, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12412 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12445 =
                FStar_List.fold_left
                  (fun uu____12518  ->
                     fun uu____12519  ->
                       match (uu____12518, uu____12519) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12627,uu____12628),uu____12629))
                           ->
                           let uu____12746 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12772 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12772 with
                                  | (env2,xx) ->
                                      let uu____12791 =
                                        let uu____12794 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12794 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12791))
                             | FStar_Util.Inr l ->
                                 let uu____12802 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12802, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12746 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12445 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12950 =
                    match uu____12950 with
                    | (attrs_opt,(uu____12986,args,result_t),def) ->
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
                                let uu____13074 = is_comp_type env1 t  in
                                if uu____13074
                                then
                                  ((let uu____13078 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13088 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13088))
                                       in
                                    match uu____13078 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13095 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13098 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13098))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13095
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
                          | uu____13109 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let body1 = desugar_term env1 def2  in
                        let lbname1 =
                          match lbname with
                          | FStar_Util.Inl x -> FStar_Util.Inl x
                          | FStar_Util.Inr l ->
                              let uu____13124 =
                                let uu____13125 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13125
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13124
                           in
                        let body2 =
                          if is_rec
                          then FStar_Syntax_Subst.close rec_bindings1 body1
                          else body1  in
                        let attrs =
                          match attrs_opt with
                          | FStar_Pervasives_Native.None  -> []
                          | FStar_Pervasives_Native.Some l ->
                              FStar_List.map (desugar_term env1) l
                           in
                        mk_lb
                          (attrs, lbname1, FStar_Syntax_Syntax.tun, body2,
                            pos)
                     in
                  let lbs1 =
                    FStar_List.map2
                      (desugar_one_def (if is_rec then env' else env))
                      fnames1 funs
                     in
                  let uu____13206 = desugar_term_aq env' body  in
                  (match uu____13206 with
                   | (body1,aq) ->
                       let uu____13219 =
                         let uu____13222 =
                           let uu____13223 =
                             let uu____13237 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13237)  in
                           FStar_Syntax_Syntax.Tm_let uu____13223  in
                         FStar_All.pipe_left mk1 uu____13222  in
                       (uu____13219, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13312 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13312 with
              | (env1,binder,pat1) ->
                  let uu____13334 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13360 = desugar_term_aq env1 t2  in
                        (match uu____13360 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13374 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13374
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13375 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13375, aq))
                    | LocalBinder (x,uu____13408) ->
                        let uu____13409 = desugar_term_aq env1 t2  in
                        (match uu____13409 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13423;
                                    FStar_Syntax_Syntax.p = uu____13424;_},uu____13425)::[]
                                   -> body1
                               | uu____13438 ->
                                   let uu____13441 =
                                     let uu____13448 =
                                       let uu____13449 =
                                         let uu____13472 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13475 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13472, uu____13475)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13449
                                        in
                                     FStar_Syntax_Syntax.mk uu____13448  in
                                   uu____13441 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13512 =
                               let uu____13515 =
                                 let uu____13516 =
                                   let uu____13530 =
                                     let uu____13533 =
                                       let uu____13534 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13534]  in
                                     FStar_Syntax_Subst.close uu____13533
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13530)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13516  in
                               FStar_All.pipe_left mk1 uu____13515  in
                             (uu____13512, aq))
                     in
                  (match uu____13334 with | (tm,aq) -> (tm, aq))
               in
            let uu____13596 = FStar_List.hd lbs  in
            (match uu____13596 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13640 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13640
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13656 =
                let uu____13657 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13657  in
              mk1 uu____13656  in
            let uu____13658 = desugar_term_aq env t1  in
            (match uu____13658 with
             | (t1',aq1) ->
                 let uu____13669 = desugar_term_aq env t2  in
                 (match uu____13669 with
                  | (t2',aq2) ->
                      let uu____13680 = desugar_term_aq env t3  in
                      (match uu____13680 with
                       | (t3',aq3) ->
                           let uu____13691 =
                             let uu____13692 =
                               let uu____13693 =
                                 let uu____13716 =
                                   let uu____13733 =
                                     let uu____13748 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____13748,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13762 =
                                     let uu____13779 =
                                       let uu____13794 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____13794,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13779]  in
                                   uu____13733 :: uu____13762  in
                                 (t1', uu____13716)  in
                               FStar_Syntax_Syntax.Tm_match uu____13693  in
                             mk1 uu____13692  in
                           (uu____13691, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13990 =
              match uu____13990 with
              | (pat,wopt,b) ->
                  let uu____14012 = desugar_match_pat env pat  in
                  (match uu____14012 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14043 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14043
                          in
                       let uu____14048 = desugar_term_aq env1 b  in
                       (match uu____14048 with
                        | (b1,aq) ->
                            let uu____14061 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14061, aq)))
               in
            let uu____14066 = desugar_term_aq env e  in
            (match uu____14066 with
             | (e1,aq) ->
                 let uu____14077 =
                   let uu____14108 =
                     let uu____14141 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14141 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14108
                     (fun uu____14359  ->
                        match uu____14359 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14077 with
                  | (brs,aqs) ->
                      let uu____14578 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14578, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14612 =
              let uu____14633 = is_comp_type env t  in
              if uu____14633
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14688 = desugar_term_aq env t  in
                 match uu____14688 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14612 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14780 = desugar_term_aq env e  in
                 (match uu____14780 with
                  | (e1,aq) ->
                      let uu____14791 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14791, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14830,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14873 = FStar_List.hd fields  in
              match uu____14873 with | (f,uu____14885) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14931  ->
                        match uu____14931 with
                        | (g,uu____14938) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14945,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14959 =
                         let uu____14965 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14965)
                          in
                       FStar_Errors.raise_error uu____14959
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
                  let uu____14976 =
                    let uu____14987 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15018  ->
                              match uu____15018 with
                              | (f,uu____15028) ->
                                  let uu____15029 =
                                    let uu____15030 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15030
                                     in
                                  (uu____15029, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14987)  in
                  FStar_Parser_AST.Construct uu____14976
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15048 =
                      let uu____15049 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15049  in
                    FStar_Parser_AST.mk_term uu____15048
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15051 =
                      let uu____15064 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15094  ->
                                match uu____15094 with
                                | (f,uu____15104) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15064)  in
                    FStar_Parser_AST.Record uu____15051  in
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
            let uu____15164 = desugar_term_aq env recterm1  in
            (match uu____15164 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15180;
                         FStar_Syntax_Syntax.vars = uu____15181;_},args)
                      ->
                      let uu____15207 =
                        let uu____15208 =
                          let uu____15209 =
                            let uu____15226 =
                              let uu____15229 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15230 =
                                let uu____15233 =
                                  let uu____15234 =
                                    let uu____15241 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15241)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15234
                                   in
                                FStar_Pervasives_Native.Some uu____15233  in
                              FStar_Syntax_Syntax.fvar uu____15229
                                FStar_Syntax_Syntax.delta_constant
                                uu____15230
                               in
                            (uu____15226, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15209  in
                        FStar_All.pipe_left mk1 uu____15208  in
                      (uu____15207, s)
                  | uu____15270 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15274 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15274 with
              | (constrname,is_rec) ->
                  let uu____15293 = desugar_term_aq env e  in
                  (match uu____15293 with
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
                       let uu____15313 =
                         let uu____15314 =
                           let uu____15315 =
                             let uu____15332 =
                               let uu____15335 =
                                 let uu____15336 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15336
                                  in
                               FStar_Syntax_Syntax.fvar uu____15335
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    Prims.int_one) qual
                                in
                             let uu____15338 =
                               let uu____15349 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15349]  in
                             (uu____15332, uu____15338)  in
                           FStar_Syntax_Syntax.Tm_app uu____15315  in
                         FStar_All.pipe_left mk1 uu____15314  in
                       (uu____15313, s))))
        | FStar_Parser_AST.NamedTyp (uu____15386,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15396 =
              let uu____15397 = FStar_Syntax_Subst.compress tm  in
              uu____15397.FStar_Syntax_Syntax.n  in
            (match uu____15396 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15405 =
                   let uu___2088_15406 =
                     let uu____15407 =
                       let uu____15409 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15409  in
                     FStar_Syntax_Util.exp_string uu____15407  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2088_15406.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2088_15406.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15405, noaqs)
             | uu____15410 ->
                 let uu____15411 =
                   let uu____15417 =
                     let uu____15419 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15419
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15417)  in
                 FStar_Errors.raise_error uu____15411
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15428 = desugar_term_aq env e  in
            (match uu____15428 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15440 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15440, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15445 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15446 =
              let uu____15447 =
                let uu____15454 = desugar_term env e  in (bv, uu____15454)
                 in
              [uu____15447]  in
            (uu____15445, uu____15446)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15479 =
              let uu____15480 =
                let uu____15481 =
                  let uu____15488 = desugar_term env e  in (uu____15488, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15481  in
              FStar_All.pipe_left mk1 uu____15480  in
            (uu____15479, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let eta_and_annot rel1 =
              let x = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
              let y = FStar_Ident.gen rel1.FStar_Parser_AST.range  in
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
              let uu____15517 =
                let uu____15518 =
                  let uu____15525 =
                    let uu____15526 =
                      let uu____15527 =
                        let uu____15536 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15549 =
                          let uu____15550 =
                            let uu____15551 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15551  in
                          FStar_Parser_AST.mk_term uu____15550
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15536, uu____15549,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15527  in
                    FStar_Parser_AST.mk_term uu____15526
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15525)  in
                FStar_Parser_AST.Abs uu____15518  in
              FStar_Parser_AST.mk_term uu____15517
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
            let last_expr =
              let uu____15566 = FStar_List.last steps  in
              match uu____15566 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____15569,uu____15570,last_expr)) -> last_expr
              | uu____15572 -> failwith "impossible: no last_expr on calc"
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
            let uu____15600 =
              FStar_List.fold_left
                (fun uu____15617  ->
                   fun uu____15618  ->
                     match (uu____15617, uu____15618) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let pf =
                           let uu____15641 =
                             let uu____15648 =
                               let uu____15655 =
                                 let uu____15662 =
                                   let uu____15669 =
                                     let uu____15674 = eta_and_annot rel2  in
                                     (uu____15674, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____15675 =
                                     let uu____15682 =
                                       let uu____15689 =
                                         let uu____15694 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____15694,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____15695 =
                                         let uu____15702 =
                                           let uu____15707 =
                                             FStar_Parser_AST.thunk just  in
                                           (uu____15707,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____15702]  in
                                       uu____15689 :: uu____15695  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____15682
                                      in
                                   uu____15669 :: uu____15675  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____15662
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____15655
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____15648
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____15641
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____15600 with
             | (e1,uu____15745) ->
                 let e2 =
                   let uu____15747 =
                     let uu____15754 =
                       let uu____15761 =
                         let uu____15768 =
                           let uu____15773 = FStar_Parser_AST.thunk e1  in
                           (uu____15773, FStar_Parser_AST.Nothing)  in
                         [uu____15768]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____15761  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____15754  in
                   FStar_Parser_AST.mkApp finish1 uu____15747
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____15790 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15791 = desugar_formula env top  in
            (uu____15791, noaqs)
        | uu____15792 ->
            let uu____15793 =
              let uu____15799 =
                let uu____15801 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____15801  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15799)  in
            FStar_Errors.raise_error uu____15793 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15811 -> false
    | uu____15821 -> true

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
           (fun uu____15859  ->
              match uu____15859 with
              | (a,imp) ->
                  let uu____15872 = desugar_term env a  in
                  arg_withimp_e imp uu____15872))

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
          let is_requires uu____15909 =
            match uu____15909 with
            | (t1,uu____15916) ->
                let uu____15917 =
                  let uu____15918 = unparen t1  in
                  uu____15918.FStar_Parser_AST.tm  in
                (match uu____15917 with
                 | FStar_Parser_AST.Requires uu____15920 -> true
                 | uu____15929 -> false)
             in
          let is_ensures uu____15941 =
            match uu____15941 with
            | (t1,uu____15948) ->
                let uu____15949 =
                  let uu____15950 = unparen t1  in
                  uu____15950.FStar_Parser_AST.tm  in
                (match uu____15949 with
                 | FStar_Parser_AST.Ensures uu____15952 -> true
                 | uu____15961 -> false)
             in
          let is_app head1 uu____15979 =
            match uu____15979 with
            | (t1,uu____15987) ->
                let uu____15988 =
                  let uu____15989 = unparen t1  in
                  uu____15989.FStar_Parser_AST.tm  in
                (match uu____15988 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15992;
                        FStar_Parser_AST.level = uu____15993;_},uu____15994,uu____15995)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15997 -> false)
             in
          let is_smt_pat uu____16009 =
            match uu____16009 with
            | (t1,uu____16016) ->
                let uu____16017 =
                  let uu____16018 = unparen t1  in
                  uu____16018.FStar_Parser_AST.tm  in
                (match uu____16017 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16022);
                               FStar_Parser_AST.range = uu____16023;
                               FStar_Parser_AST.level = uu____16024;_},uu____16025)::uu____16026::[])
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
                               FStar_Parser_AST.range = uu____16075;
                               FStar_Parser_AST.level = uu____16076;_},uu____16077)::uu____16078::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16111 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16146 = head_and_args t1  in
            match uu____16146 with
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
                     let thunk_ens uu____16239 =
                       match uu____16239 with
                       | (e,i) ->
                           let uu____16250 = FStar_Parser_AST.thunk e  in
                           (uu____16250, i)
                        in
                     let fail_lemma uu____16262 =
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
                           let uu____16368 =
                             let uu____16375 =
                               let uu____16382 = thunk_ens ens  in
                               [uu____16382; nil_pat]  in
                             req_true :: uu____16375  in
                           unit_tm :: uu____16368
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16429 =
                             let uu____16436 =
                               let uu____16443 = thunk_ens ens  in
                               [uu____16443; nil_pat]  in
                             req :: uu____16436  in
                           unit_tm :: uu____16429
                       | ens::smtpat::[] when
                           (((let uu____16492 = is_requires ens  in
                              Prims.op_Negation uu____16492) &&
                               (let uu____16495 = is_smt_pat ens  in
                                Prims.op_Negation uu____16495))
                              &&
                              (let uu____16498 = is_decreases ens  in
                               Prims.op_Negation uu____16498))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16500 =
                             let uu____16507 =
                               let uu____16514 = thunk_ens ens  in
                               [uu____16514; smtpat]  in
                             req_true :: uu____16507  in
                           unit_tm :: uu____16500
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16561 =
                             let uu____16568 =
                               let uu____16575 = thunk_ens ens  in
                               [uu____16575; nil_pat; dec]  in
                             req_true :: uu____16568  in
                           unit_tm :: uu____16561
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16635 =
                             let uu____16642 =
                               let uu____16649 = thunk_ens ens  in
                               [uu____16649; smtpat; dec]  in
                             req_true :: uu____16642  in
                           unit_tm :: uu____16635
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16709 =
                             let uu____16716 =
                               let uu____16723 = thunk_ens ens  in
                               [uu____16723; nil_pat; dec]  in
                             req :: uu____16716  in
                           unit_tm :: uu____16709
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16783 =
                             let uu____16790 =
                               let uu____16797 = thunk_ens ens  in
                               [uu____16797; smtpat]  in
                             req :: uu____16790  in
                           unit_tm :: uu____16783
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16862 =
                             let uu____16869 =
                               let uu____16876 = thunk_ens ens  in
                               [uu____16876; dec; smtpat]  in
                             req :: uu____16869  in
                           unit_tm :: uu____16862
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16938 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16938, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16966 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16966
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16969 =
                       let uu____16976 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16976, [])  in
                     (uu____16969, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16994 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16994
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16997 =
                       let uu____17004 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17004, [])  in
                     (uu____16997, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17026 =
                       let uu____17033 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17033, [])  in
                     (uu____17026, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17056 when allow_type_promotion ->
                     let default_effect =
                       let uu____17058 = FStar_Options.ml_ish ()  in
                       if uu____17058
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17064 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17064
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17071 =
                       let uu____17078 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17078, [])  in
                     (uu____17071, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17101 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17120 = pre_process_comp_typ t  in
          match uu____17120 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17172 =
                    let uu____17178 =
                      let uu____17180 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17180
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17178)
                     in
                  fail1 uu____17172)
               else ();
               (let is_universe uu____17196 =
                  match uu____17196 with
                  | (uu____17202,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17204 = FStar_Util.take is_universe args  in
                match uu____17204 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17263  ->
                           match uu____17263 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17270 =
                      let uu____17285 = FStar_List.hd args1  in
                      let uu____17294 = FStar_List.tl args1  in
                      (uu____17285, uu____17294)  in
                    (match uu____17270 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17349 =
                           let is_decrease uu____17388 =
                             match uu____17388 with
                             | (t1,uu____17399) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17410;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17411;_},uu____17412::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17451 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17349 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17568  ->
                                        match uu____17568 with
                                        | (t1,uu____17578) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17587,(arg,uu____17589)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17628 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17649 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17661 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17661
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17668 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17668
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____17678 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17678
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17685 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17685
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17692 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17692
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17699 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17699
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____17720 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17720
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
                                                    let uu____17811 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17811
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
                                              | uu____17832 -> pat  in
                                            let uu____17833 =
                                              let uu____17844 =
                                                let uu____17855 =
                                                  let uu____17864 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17864, aq)  in
                                                [uu____17855]  in
                                              ens :: uu____17844  in
                                            req :: uu____17833
                                        | uu____17905 -> rest2
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
      let connective s =
        match s with
        | "/\\" -> FStar_Pervasives_Native.Some FStar_Parser_Const.and_lid
        | "\\/" -> FStar_Pervasives_Native.Some FStar_Parser_Const.or_lid
        | "==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.imp_lid
        | "<==>" -> FStar_Pervasives_Native.Some FStar_Parser_Const.iff_lid
        | "~" -> FStar_Pervasives_Native.Some FStar_Parser_Const.not_lid
        | uu____17937 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2395_17959 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2395_17959.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2395_17959.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2402_18013 = b  in
             {
               FStar_Parser_AST.b = (uu___2402_18013.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2402_18013.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2402_18013.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18042 body1 =
          match uu____18042 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18088::uu____18089) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18107 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2421_18134 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2421_18134.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2421_18134.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18197 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18197))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18228 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18228 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2434_18238 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2434_18238.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2434_18238.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18244 =
                     let uu____18247 =
                       let uu____18248 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18248]  in
                     no_annot_abs uu____18247 body2  in
                   FStar_All.pipe_left setpos uu____18244  in
                 let uu____18269 =
                   let uu____18270 =
                     let uu____18287 =
                       let uu____18290 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18290
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____18292 =
                       let uu____18303 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18303]  in
                     (uu____18287, uu____18292)  in
                   FStar_Syntax_Syntax.Tm_app uu____18270  in
                 FStar_All.pipe_left mk1 uu____18269)
        | uu____18342 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18407 = q (rest, pats, body)  in
              let uu____18410 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18407 uu____18410
                FStar_Parser_AST.Formula
               in
            let uu____18411 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____18411 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18422 -> failwith "impossible"  in
      let uu____18426 =
        let uu____18427 = unparen f  in uu____18427.FStar_Parser_AST.tm  in
      match uu____18426 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18440,uu____18441) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18465,uu____18466) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18522 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18522
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18566 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____18566
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18630 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18635 =
        FStar_List.fold_left
          (fun uu____18668  ->
             fun b  ->
               match uu____18668 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2513_18712 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2513_18712.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2513_18712.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2513_18712.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18727 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18727 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2523_18745 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2523_18745.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2523_18745.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18746 =
                               let uu____18753 =
                                 let uu____18758 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18758)  in
                               uu____18753 :: out  in
                             (env2, uu____18746))
                    | uu____18769 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18635 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____18842 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18842)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18847 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18847)
      | FStar_Parser_AST.TVariable x ->
          let uu____18851 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18851)
      | FStar_Parser_AST.NoName t ->
          let uu____18855 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18855)
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
      fun uu___12_18863  ->
        match uu___12_18863 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18885 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18885, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18902 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18902 with
             | (env1,a1) ->
                 let uu____18919 =
                   let uu____18926 = trans_aqual env1 imp  in
                   ((let uu___2557_18932 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2557_18932.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2557_18932.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18926)
                    in
                 (uu____18919, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___13_18940  ->
      match uu___13_18940 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18944 =
            let uu____18945 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18945  in
          FStar_Pervasives_Native.Some uu____18944
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18961) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18963) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18966 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18984 = binder_ident b  in
         FStar_Common.list_of_option uu____18984) bs
  
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
               (fun uu___14_19021  ->
                  match uu___14_19021 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19026 -> false))
           in
        let quals2 q =
          let uu____19040 =
            (let uu____19044 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19044) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19040
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19061 = FStar_Ident.range_of_lid disc_name  in
                let uu____19062 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19061;
                  FStar_Syntax_Syntax.sigquals = uu____19062;
                  FStar_Syntax_Syntax.sigmeta =
                    FStar_Syntax_Syntax.default_sigmeta;
                  FStar_Syntax_Syntax.sigattrs = []
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
            let uu____19102 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19140  ->
                        match uu____19140 with
                        | (x,uu____19151) ->
                            let uu____19156 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19156 with
                             | (field_name,uu____19164) ->
                                 let only_decl =
                                   ((let uu____19169 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19169)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19171 =
                                        let uu____19173 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19173.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19171)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19191 =
                                       FStar_List.filter
                                         (fun uu___15_19195  ->
                                            match uu___15_19195 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19198 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19191
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_19213  ->
                                             match uu___16_19213 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19218 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19221 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19221;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____19228 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19228
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one
                                       in
                                    let lb =
                                      let uu____19239 =
                                        let uu____19244 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19244  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19239;
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
                                      let uu____19248 =
                                        let uu____19249 =
                                          let uu____19256 =
                                            let uu____19259 =
                                              let uu____19260 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19260
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19259]  in
                                          ((false, [lb]), uu____19256)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19249
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19248;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____19102 FStar_List.flatten
  
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
            (lid,uu____19309,t,uu____19311,n1,uu____19313) when
            let uu____19320 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____19320 ->
            let uu____19322 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____19322 with
             | (formals,uu____19340) ->
                 (match formals with
                  | [] -> []
                  | uu____19369 ->
                      let filter_records uu___17_19385 =
                        match uu___17_19385 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19388,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19400 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19402 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19402 with
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
                      let uu____19414 = FStar_Util.first_N n1 formals  in
                      (match uu____19414 with
                       | (uu____19443,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19477 -> []
  
let (mk_typ_abbrev :
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
  fun lid  ->
    fun uvs  ->
      fun typars  ->
        fun kopt  ->
          fun t  ->
            fun lids  ->
              fun quals  ->
                fun rng  ->
                  let dd =
                    let uu____19556 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19556
                    then
                      let uu____19562 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19562
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19566 =
                      let uu____19571 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19571  in
                    let uu____19572 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19578 =
                          let uu____19581 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19581  in
                        FStar_Syntax_Util.arrow typars uu____19578
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19586 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19566;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19572;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19586;
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
                    FStar_Syntax_Syntax.sigattrs = []
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
          let tycon_id uu___18_19640 =
            match uu___18_19640 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19642,uu____19643) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19653,uu____19654,uu____19655) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19665,uu____19666,uu____19667) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19697,uu____19698,uu____19699) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19745) ->
                let uu____19746 =
                  let uu____19747 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19747  in
                FStar_Parser_AST.mk_term uu____19746 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19749 =
                  let uu____19750 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19750  in
                FStar_Parser_AST.mk_term uu____19749 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19752) ->
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
              | uu____19783 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19791 =
                     let uu____19792 =
                       let uu____19799 = binder_to_term b  in
                       (out, uu____19799, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19792  in
                   FStar_Parser_AST.mk_term uu____19791
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___19_19811 =
            match uu___19_19811 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19868  ->
                       match uu____19868 with
                       | (x,t,uu____19879) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19885 =
                    let uu____19886 =
                      let uu____19887 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19887  in
                    FStar_Parser_AST.mk_term uu____19886
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19885 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19894 = binder_idents parms  in id1 ::
                    uu____19894
                   in
                (FStar_List.iter
                   (fun uu____19912  ->
                      match uu____19912 with
                      | (f,uu____19922,uu____19923) ->
                          let uu____19928 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19928
                          then
                            let uu____19933 =
                              let uu____19939 =
                                let uu____19941 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19941
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19939)
                               in
                            FStar_Errors.raise_error uu____19933
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19947 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19974  ->
                            match uu____19974 with
                            | (x,uu____19984,uu____19985) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19947)))
            | uu____20043 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___20_20083 =
            match uu___20_20083 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20107 = typars_of_binders _env binders  in
                (match uu____20107 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20143 =
                         let uu____20144 =
                           let uu____20145 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20145  in
                         FStar_Parser_AST.mk_term uu____20144
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20143 binders  in
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
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     let _env1 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     let _env2 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env'
                         id1 FStar_Syntax_Syntax.delta_constant
                        in
                     (_env1, _env2, se, tconstr))
            | uu____20156 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20199 =
              FStar_List.fold_left
                (fun uu____20233  ->
                   fun uu____20234  ->
                     match (uu____20233, uu____20234) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20303 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20303 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20199 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20394 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20394
                | uu____20395 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20403 = desugar_abstract_tc quals env [] tc  in
              (match uu____20403 with
               | (uu____20416,uu____20417,se,uu____20419) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20422,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20441 =
                                 let uu____20443 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20443  in
                               if uu____20441
                               then
                                 let uu____20446 =
                                   let uu____20452 =
                                     let uu____20454 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20454
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20452)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20446
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
                           | uu____20467 ->
                               let uu____20468 =
                                 let uu____20475 =
                                   let uu____20476 =
                                     let uu____20491 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20491)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20476
                                    in
                                 FStar_Syntax_Syntax.mk uu____20475  in
                               uu____20468 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2832_20504 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2832_20504.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2832_20504.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2832_20504.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20505 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20509 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20509
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20522 = typars_of_binders env binders  in
              (match uu____20522 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20556 =
                           FStar_Util.for_some
                             (fun uu___21_20559  ->
                                match uu___21_20559 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20562 -> false) quals
                            in
                         if uu____20556
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20570 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20570
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20575 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_20581  ->
                               match uu___22_20581 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20584 -> false))
                        in
                     if uu____20575
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20598 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20598
                     then
                       let uu____20604 =
                         let uu____20611 =
                           let uu____20612 = unparen t  in
                           uu____20612.FStar_Parser_AST.tm  in
                         match uu____20611 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20633 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20663)::args_rev ->
                                   let uu____20675 =
                                     let uu____20676 = unparen last_arg  in
                                     uu____20676.FStar_Parser_AST.tm  in
                                   (match uu____20675 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20704 -> ([], args))
                               | uu____20713 -> ([], args)  in
                             (match uu____20633 with
                              | (cattributes,args1) ->
                                  let uu____20752 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20752))
                         | uu____20763 -> (t, [])  in
                       match uu____20604 with
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
                                  (fun uu___23_20786  ->
                                     match uu___23_20786 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20789 -> true))
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
                             FStar_Syntax_Syntax.sigattrs = []
                           }
                     else
                       (let t1 = desugar_typ env' t  in
                        mk_typ_abbrev qlid [] typars kopt1 t1 [qlid] quals1
                          rng)
                      in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
                   let env2 =
                     FStar_Syntax_DsEnv.push_doc env1 qlid
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se]))
          | (FStar_Parser_AST.TyconRecord uu____20798)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20822 = tycon_record_as_variant trec  in
              (match uu____20822 with
               | (t,fs) ->
                   let uu____20839 =
                     let uu____20842 =
                       let uu____20843 =
                         let uu____20852 =
                           let uu____20855 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20855  in
                         (uu____20852, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20843  in
                     uu____20842 :: quals  in
                   desugar_tycon env d uu____20839 [t])
          | uu____20860::uu____20861 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21031 = et  in
                match uu____21031 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21261 ->
                         let trec = tc  in
                         let uu____21285 = tycon_record_as_variant trec  in
                         (match uu____21285 with
                          | (t,fs) ->
                              let uu____21345 =
                                let uu____21348 =
                                  let uu____21349 =
                                    let uu____21358 =
                                      let uu____21361 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21361  in
                                    (uu____21358, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21349
                                   in
                                uu____21348 :: quals1  in
                              collect_tcs uu____21345 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21451 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21451 with
                          | (env2,uu____21512,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21665 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21665 with
                          | (env2,uu____21726,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21854 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21904 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21904 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_22419  ->
                             match uu___25_22419 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22485,uu____22486);
                                    FStar_Syntax_Syntax.sigrng = uu____22487;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22488;
                                    FStar_Syntax_Syntax.sigmeta = uu____22489;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22490;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22554 =
                                     typars_of_binders env1 binders  in
                                   match uu____22554 with
                                   | (env2,tpars1) ->
                                       let uu____22581 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22581 with
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
                                 let uu____22610 =
                                   let uu____22629 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22629)
                                    in
                                 [uu____22610]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22689);
                                    FStar_Syntax_Syntax.sigrng = uu____22690;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22692;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22693;_},constrs,tconstr,quals1)
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
                                 let uu____22794 = push_tparams env1 tpars
                                    in
                                 (match uu____22794 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22861  ->
                                             match uu____22861 with
                                             | (x,uu____22873) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22878 =
                                        let uu____22905 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23015  ->
                                                  match uu____23015 with
                                                  | (id1,topt,doc1,of_notation)
                                                      ->
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
                                                        let uu____23075 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23075
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
                                                                uu___24_23086
                                                                 ->
                                                                match uu___24_23086
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23098
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23106 =
                                                        let uu____23125 =
                                                          let uu____23126 =
                                                            let uu____23127 =
                                                              let uu____23143
                                                                =
                                                                let uu____23144
                                                                  =
                                                                  let uu____23147
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23147
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23144
                                                                 in
                                                              (name, univs1,
                                                                uu____23143,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23127
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23126;
                                                            FStar_Syntax_Syntax.sigrng
                                                              = rng;
                                                            FStar_Syntax_Syntax.sigquals
                                                              = quals2;
                                                            FStar_Syntax_Syntax.sigmeta
                                                              =
                                                              FStar_Syntax_Syntax.default_sigmeta;
                                                            FStar_Syntax_Syntax.sigattrs
                                                              = []
                                                          }  in
                                                        ((name, doc1), tps,
                                                          uu____23125)
                                                         in
                                                      (name, uu____23106)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22905
                                         in
                                      (match uu____22878 with
                                       | (constrNames,constrs1) ->
                                           ((tname, (d.FStar_Parser_AST.doc)),
                                             [],
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
                                                 []
                                             })
                                           :: constrs1))
                             | uu____23359 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23487  ->
                             match uu____23487 with
                             | (name_doc,uu____23513,uu____23514) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23586  ->
                             match uu____23586 with
                             | (uu____23605,uu____23606,se) -> se))
                      in
                   let uu____23632 =
                     let uu____23639 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23639 rng
                      in
                   (match uu____23632 with
                    | (bundle,abbrevs) ->
                        let env2 = FStar_Syntax_DsEnv.push_sigelt env0 bundle
                           in
                        let env3 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env2 abbrevs
                           in
                        let data_ops =
                          FStar_All.pipe_right docs_tps_sigelts
                            (FStar_List.collect
                               (fun uu____23701  ->
                                  match uu____23701 with
                                  | (uu____23722,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23770,tps,k,uu____23773,constrs)
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
                                      let uu____23794 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23809 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23826,uu____23827,uu____23828,uu____23829,uu____23830)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23837
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23809
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23841 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_23848  ->
                                                          match uu___26_23848
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23850 ->
                                                              true
                                                          | uu____23860 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23841))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23794
                                  | uu____23862 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23879  ->
                                 match uu____23879 with
                                 | (lid,doc1) ->
                                     FStar_Syntax_DsEnv.push_doc env4 lid
                                       doc1) env4 name_docs
                           in
                        (env5,
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
      let uu____23924 =
        FStar_List.fold_left
          (fun uu____23959  ->
             fun b  ->
               match uu____23959 with
               | (env1,binders1) ->
                   let uu____24003 = desugar_binder env1 b  in
                   (match uu____24003 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24026 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24026 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24079 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23924 with
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
          let uu____24183 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_24190  ->
                    match uu___27_24190 with
                    | FStar_Syntax_Syntax.Reflectable uu____24192 -> true
                    | uu____24194 -> false))
             in
          if uu____24183
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24199 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24199
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
                FStar_Syntax_Syntax.sigattrs = []
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
    fun at1  ->
      fun head1  ->
        let warn1 uu____24250 =
          if warn
          then
            let uu____24252 =
              let uu____24258 =
                let uu____24260 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24260
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24258)  in
            FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos uu____24252
          else ()  in
        let uu____24266 = FStar_Syntax_Util.head_and_args at1  in
        match uu____24266 with
        | (hd1,args) ->
            let uu____24319 =
              let uu____24320 = FStar_Syntax_Subst.compress hd1  in
              uu____24320.FStar_Syntax_Syntax.n  in
            (match uu____24319 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24364)::[] ->
                      let uu____24389 =
                        let uu____24394 =
                          let uu____24403 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24403 a1  in
                        uu____24394 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24389 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24426 =
                             let uu____24432 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24432  in
                           (uu____24426, true)
                       | uu____24447 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24463 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24485 -> (FStar_Pervasives_Native.None, false))
  
let (get_fail_attr :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option)
  =
  fun warn  ->
    fun at1  ->
      let rebind res b =
        match res with
        | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some l ->
            FStar_Pervasives_Native.Some (l, b)
         in
      let uu____24602 =
        parse_attr_with_list warn at1 FStar_Parser_Const.fail_attr  in
      match uu____24602 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24651 =
               parse_attr_with_list warn at1 FStar_Parser_Const.fail_lax_attr
                in
             match uu____24651 with | (res1,uu____24673) -> rebind res1 true)
  
let rec (desugar_effect :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl ->
      FStar_Parser_AST.qualifiers ->
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
        fun eff_name  ->
          fun eff_binders  ->
            fun eff_typ  ->
              fun eff_decls  ->
                fun attrs  ->
                  let env0 = env  in
                  let monad_env =
                    FStar_Syntax_DsEnv.enter_monad_scope env eff_name  in
                  let uu____24838 = desugar_binders monad_env eff_binders  in
                  match uu____24838 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let for_free =
                        let uu____24878 =
                          let uu____24880 =
                            let uu____24889 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24889  in
                          FStar_List.length uu____24880  in
                        uu____24878 = Prims.int_one  in
                      let mandatory_members =
                        let rr_members = ["repr"; "return"; "bind"]  in
                        if for_free
                        then rr_members
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
                            (uu____24967,uu____24968,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24970,uu____24971,uu____24972),uu____24973)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____25010 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____25013 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____25025 = name_of_eff_decl decl  in
                             FStar_List.mem uu____25025 mandatory_members)
                          eff_decls
                         in
                      (match uu____25013 with
                       | (mandatory_members_decls,actions) ->
                           let uu____25044 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____25073  ->
                                     fun decl  ->
                                       match uu____25073 with
                                       | (env2,out) ->
                                           let uu____25093 =
                                             desugar_decl env2 decl  in
                                           (match uu____25093 with
                                            | (env3,ses) ->
                                                let uu____25106 =
                                                  let uu____25109 =
                                                    FStar_List.hd ses  in
                                                  uu____25109 :: out  in
                                                (env3, uu____25106)))
                                  (env1, []))
                              in
                           (match uu____25044 with
                            | (env2,decls) ->
                                let binders1 =
                                  FStar_Syntax_Subst.close_binders binders
                                   in
                                let actions_docs =
                                  FStar_All.pipe_right actions
                                    (FStar_List.map
                                       (fun d1  ->
                                          match d1.FStar_Parser_AST.d with
                                          | FStar_Parser_AST.Tycon
                                              (uu____25178,uu____25179,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____25182,
                                                 {
                                                   FStar_Parser_AST.tm =
                                                     FStar_Parser_AST.Construct
                                                     (uu____25183,(def,uu____25185)::
                                                      (cps_type,uu____25187)::[]);
                                                   FStar_Parser_AST.range =
                                                     uu____25188;
                                                   FStar_Parser_AST.level =
                                                     uu____25189;_}),doc1)::[])
                                              when Prims.op_Negation for_free
                                              ->
                                              let uu____25245 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25245 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25283 =
                                                     let uu____25284 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25285 =
                                                       let uu____25286 =
                                                         desugar_term env3
                                                           def
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25286
                                                        in
                                                     let uu____25293 =
                                                       let uu____25294 =
                                                         desugar_typ env3
                                                           cps_type
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25294
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25284;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25285;
                                                       FStar_Syntax_Syntax.action_typ
                                                         = uu____25293
                                                     }  in
                                                   (uu____25283, doc1))
                                          | FStar_Parser_AST.Tycon
                                              (uu____25303,uu____25304,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____25307,defn),doc1)::[])
                                              when for_free ->
                                              let uu____25346 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25346 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25384 =
                                                     let uu____25385 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25386 =
                                                       let uu____25387 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25387
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25385;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25386;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____25384, doc1))
                                          | uu____25396 ->
                                              FStar_Errors.raise_error
                                                (FStar_Errors.Fatal_MalformedActionDeclaration,
                                                  "Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")
                                                d1.FStar_Parser_AST.drange))
                                   in
                                let actions1 =
                                  FStar_List.map FStar_Pervasives_Native.fst
                                    actions_docs
                                   in
                                let eff_t1 =
                                  FStar_Syntax_Subst.close binders1 eff_t  in
                                let lookup1 s =
                                  let l =
                                    let uu____25432 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____25432
                                     in
                                  let uu____25434 =
                                    let uu____25435 =
                                      FStar_Syntax_DsEnv.fail_or env2
                                        (FStar_Syntax_DsEnv.try_lookup_definition
                                           env2) l
                                       in
                                    FStar_All.pipe_left
                                      (FStar_Syntax_Subst.close binders1)
                                      uu____25435
                                     in
                                  ([], uu____25434)  in
                                let mname =
                                  FStar_Syntax_DsEnv.qualify env0 eff_name
                                   in
                                let qualifiers =
                                  FStar_List.map
                                    (trans_qual d.FStar_Parser_AST.drange
                                       (FStar_Pervasives_Native.Some mname))
                                    quals
                                   in
                                let se =
                                  if for_free
                                  then
                                    let dummy_tscheme =
                                      let uu____25453 =
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                         in
                                      ([], uu____25453)  in
                                    let uu____25460 =
                                      let uu____25461 =
                                        let uu____25462 = lookup1 "repr"  in
                                        let uu____25464 = lookup1 "return"
                                           in
                                        let uu____25466 = lookup1 "bind"  in
                                        let uu____25468 =
                                          FStar_List.map (desugar_term env2)
                                            attrs
                                           in
                                        {
                                          FStar_Syntax_Syntax.cattributes =
                                            [];
                                          FStar_Syntax_Syntax.mname = mname;
                                          FStar_Syntax_Syntax.univs = [];
                                          FStar_Syntax_Syntax.binders =
                                            binders1;
                                          FStar_Syntax_Syntax.signature =
                                            ([], eff_t1);
                                          FStar_Syntax_Syntax.ret_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.bind_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.if_then_else =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.ite_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.stronger =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.close_wp =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.trivial =
                                            dummy_tscheme;
                                          FStar_Syntax_Syntax.repr =
                                            uu____25462;
                                          FStar_Syntax_Syntax.return_repr =
                                            uu____25464;
                                          FStar_Syntax_Syntax.bind_repr =
                                            uu____25466;
                                          FStar_Syntax_Syntax.actions =
                                            actions1;
                                          FStar_Syntax_Syntax.eff_attrs =
                                            uu____25468
                                        }  in
                                      FStar_Syntax_Syntax.Sig_new_effect_for_free
                                        uu____25461
                                       in
                                    {
                                      FStar_Syntax_Syntax.sigel = uu____25460;
                                      FStar_Syntax_Syntax.sigrng =
                                        (d.FStar_Parser_AST.drange);
                                      FStar_Syntax_Syntax.sigquals =
                                        qualifiers;
                                      FStar_Syntax_Syntax.sigmeta =
                                        FStar_Syntax_Syntax.default_sigmeta;
                                      FStar_Syntax_Syntax.sigattrs = []
                                    }
                                  else
                                    (let rr =
                                       FStar_Util.for_some
                                         (fun uu___28_25480  ->
                                            match uu___28_25480 with
                                            | FStar_Syntax_Syntax.Reifiable 
                                                -> true
                                            | FStar_Syntax_Syntax.Reflectable
                                                uu____25483 -> true
                                            | uu____25485 -> false)
                                         qualifiers
                                        in
                                     let un_ts =
                                       ([], FStar_Syntax_Syntax.tun)  in
                                     let uu____25500 =
                                       let uu____25501 =
                                         let uu____25502 =
                                           lookup1 "return_wp"  in
                                         let uu____25504 = lookup1 "bind_wp"
                                            in
                                         let uu____25506 =
                                           lookup1 "if_then_else"  in
                                         let uu____25508 = lookup1 "ite_wp"
                                            in
                                         let uu____25510 = lookup1 "stronger"
                                            in
                                         let uu____25512 = lookup1 "close_wp"
                                            in
                                         let uu____25514 = lookup1 "trivial"
                                            in
                                         let uu____25516 =
                                           if rr
                                           then lookup1 "repr"
                                           else ([], FStar_Syntax_Syntax.tun)
                                            in
                                         let uu____25525 =
                                           if rr
                                           then lookup1 "return"
                                           else un_ts  in
                                         let uu____25530 =
                                           if rr
                                           then lookup1 "bind"
                                           else un_ts  in
                                         let uu____25535 =
                                           FStar_List.map (desugar_term env2)
                                             attrs
                                            in
                                         {
                                           FStar_Syntax_Syntax.cattributes =
                                             [];
                                           FStar_Syntax_Syntax.mname = mname;
                                           FStar_Syntax_Syntax.univs = [];
                                           FStar_Syntax_Syntax.binders =
                                             binders1;
                                           FStar_Syntax_Syntax.signature =
                                             ([], eff_t1);
                                           FStar_Syntax_Syntax.ret_wp =
                                             uu____25502;
                                           FStar_Syntax_Syntax.bind_wp =
                                             uu____25504;
                                           FStar_Syntax_Syntax.if_then_else =
                                             uu____25506;
                                           FStar_Syntax_Syntax.ite_wp =
                                             uu____25508;
                                           FStar_Syntax_Syntax.stronger =
                                             uu____25510;
                                           FStar_Syntax_Syntax.close_wp =
                                             uu____25512;
                                           FStar_Syntax_Syntax.trivial =
                                             uu____25514;
                                           FStar_Syntax_Syntax.repr =
                                             uu____25516;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25525;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25530;
                                           FStar_Syntax_Syntax.actions =
                                             actions1;
                                           FStar_Syntax_Syntax.eff_attrs =
                                             uu____25535
                                         }  in
                                       FStar_Syntax_Syntax.Sig_new_effect
                                         uu____25501
                                        in
                                     {
                                       FStar_Syntax_Syntax.sigel =
                                         uu____25500;
                                       FStar_Syntax_Syntax.sigrng =
                                         (d.FStar_Parser_AST.drange);
                                       FStar_Syntax_Syntax.sigquals =
                                         qualifiers;
                                       FStar_Syntax_Syntax.sigmeta =
                                         FStar_Syntax_Syntax.default_sigmeta;
                                       FStar_Syntax_Syntax.sigattrs = []
                                     })
                                   in
                                let env3 =
                                  FStar_Syntax_DsEnv.push_sigelt env0 se  in
                                let env4 =
                                  FStar_Syntax_DsEnv.push_doc env3 mname
                                    d.FStar_Parser_AST.doc
                                   in
                                let env5 =
                                  FStar_All.pipe_right actions_docs
                                    (FStar_List.fold_left
                                       (fun env5  ->
                                          fun uu____25565  ->
                                            match uu____25565 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25579 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25579
                                                   in
                                                FStar_Syntax_DsEnv.push_doc
                                                  env6
                                                  a.FStar_Syntax_Syntax.action_name
                                                  doc1) env4)
                                   in
                                let env6 =
                                  push_reflect_effect env5 qualifiers mname
                                    d.FStar_Parser_AST.drange
                                   in
                                let env7 =
                                  FStar_Syntax_DsEnv.push_doc env6 mname
                                    d.FStar_Parser_AST.doc
                                   in
                                (env7, [se])))

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
                let uu____25603 = desugar_binders env1 eff_binders  in
                match uu____25603 with
                | (env2,binders) ->
                    let uu____25640 =
                      let uu____25651 = head_and_args defn  in
                      match uu____25651 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25688 ->
                                let uu____25689 =
                                  let uu____25695 =
                                    let uu____25697 =
                                      let uu____25699 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25699 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25697  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25695)
                                   in
                                FStar_Errors.raise_error uu____25689
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25705 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25735)::args_rev ->
                                let uu____25747 =
                                  let uu____25748 = unparen last_arg  in
                                  uu____25748.FStar_Parser_AST.tm  in
                                (match uu____25747 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25776 -> ([], args))
                            | uu____25785 -> ([], args)  in
                          (match uu____25705 with
                           | (cattributes,args1) ->
                               let uu____25828 = desugar_args env2 args1  in
                               let uu____25829 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25828, uu____25829))
                       in
                    (match uu____25640 with
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
                          (let uu____25869 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25869 with
                           | (ed_binders,uu____25883,ed_binders_opening) ->
                               let sub' shift_n uu____25902 =
                                 match uu____25902 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25917 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25917 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25921 =
                                       let uu____25922 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25922)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25921
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25943 =
                                   sub1 ed.FStar_Syntax_Syntax.signature  in
                                 let uu____25944 =
                                   sub1 ed.FStar_Syntax_Syntax.ret_wp  in
                                 let uu____25945 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_wp  in
                                 let uu____25946 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25947 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25948 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25949 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25950 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25951 =
                                   sub1 ed.FStar_Syntax_Syntax.repr  in
                                 let uu____25952 =
                                   sub1 ed.FStar_Syntax_Syntax.return_repr
                                    in
                                 let uu____25953 =
                                   sub1 ed.FStar_Syntax_Syntax.bind_repr  in
                                 let uu____25954 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25970 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25971 =
                                          let uu____25972 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25972
                                           in
                                        let uu____25987 =
                                          let uu____25988 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25988
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25970;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25971;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25987
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.signature =
                                     uu____25943;
                                   FStar_Syntax_Syntax.ret_wp = uu____25944;
                                   FStar_Syntax_Syntax.bind_wp = uu____25945;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25946;
                                   FStar_Syntax_Syntax.ite_wp = uu____25947;
                                   FStar_Syntax_Syntax.stronger = uu____25948;
                                   FStar_Syntax_Syntax.close_wp = uu____25949;
                                   FStar_Syntax_Syntax.trivial = uu____25950;
                                   FStar_Syntax_Syntax.repr = uu____25951;
                                   FStar_Syntax_Syntax.return_repr =
                                     uu____25952;
                                   FStar_Syntax_Syntax.bind_repr =
                                     uu____25953;
                                   FStar_Syntax_Syntax.actions = uu____25954;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let for_free =
                                   let uu____26006 =
                                     let uu____26008 =
                                       let uu____26017 =
                                         let uu____26032 =
                                           FStar_All.pipe_right
                                             ed1.FStar_Syntax_Syntax.signature
                                             FStar_Pervasives_Native.snd
                                            in
                                         FStar_All.pipe_right uu____26032
                                           FStar_Syntax_Util.arrow_formals
                                          in
                                       FStar_Pervasives_Native.fst
                                         uu____26017
                                        in
                                     FStar_List.length uu____26008  in
                                   uu____26006 = Prims.int_one  in
                                 let uu____26077 =
                                   let uu____26080 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26080 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (if for_free
                                      then
                                        FStar_Syntax_Syntax.Sig_new_effect_for_free
                                          ed1
                                      else
                                        FStar_Syntax_Syntax.Sig_new_effect
                                          ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26077;
                                   FStar_Syntax_Syntax.sigmeta =
                                     FStar_Syntax_Syntax.default_sigmeta;
                                   FStar_Syntax_Syntax.sigattrs = []
                                 }  in
                               let monad_env = env2  in
                               let env3 =
                                 FStar_Syntax_DsEnv.push_sigelt env0 se  in
                               let env4 =
                                 FStar_Syntax_DsEnv.push_doc env3 ed_lid
                                   d.FStar_Parser_AST.doc
                                  in
                               let env5 =
                                 FStar_All.pipe_right
                                   ed1.FStar_Syntax_Syntax.actions
                                   (FStar_List.fold_left
                                      (fun env5  ->
                                         fun a  ->
                                           let doc1 =
                                             FStar_Syntax_DsEnv.try_lookup_doc
                                               env5
                                               a.FStar_Syntax_Syntax.action_name
                                              in
                                           let env6 =
                                             let uu____26104 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____26104
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____26106 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26106
                                 then
                                   let reflect_lid =
                                     let uu____26113 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26113
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
                                       FStar_Syntax_Syntax.sigattrs = []
                                     }  in
                                   FStar_Syntax_DsEnv.push_sigelt env5
                                     refl_decl
                                 else env5  in
                               let env7 =
                                 FStar_Syntax_DsEnv.push_doc env6 mname
                                   d.FStar_Parser_AST.doc
                                  in
                               (env7, [se]))))

and (mk_comment_attr :
  FStar_Parser_AST.decl ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list)
  =
  fun d  ->
    let uu____26125 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____26125 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____26212 ->
              let uu____26215 =
                let uu____26217 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.of_int (80))
                  uu____26217
                 in
              Prims.op_Hat "\n  " uu____26215
          | uu____26220 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____26239  ->
               match uu____26239 with
               | (k,v1) ->
                   if (k <> "summary") && (k <> "type")
                   then
                     FStar_Pervasives_Native.Some
                       (Prims.op_Hat k (Prims.op_Hat ": " v1))
                   else FStar_Pervasives_Native.None) kv
           in
        let other1 =
          if other <> []
          then Prims.op_Hat (FStar_String.concat "\n" other) "\n"
          else ""  in
        let str =
          Prims.op_Hat summary (Prims.op_Hat pp (Prims.op_Hat other1 text))
           in
        let fv =
          let uu____26284 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____26284
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        if str = ""
        then []
        else
          (let uu____26297 =
             let arg = FStar_Syntax_Util.exp_string str  in
             let uu____26301 =
               let uu____26312 = FStar_Syntax_Syntax.as_arg arg  in
               [uu____26312]  in
             FStar_Syntax_Util.mk_app fv uu____26301  in
           [uu____26297])

and (desugar_decl_aux :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      let env0 = env  in
      let uu____26348 = desugar_decl_noattrs env d  in
      match uu____26348 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let val_attrs =
            match sigelts with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  (lbs,names1);
                FStar_Syntax_Syntax.sigrng = uu____26378;
                FStar_Syntax_Syntax.sigquals = uu____26379;
                FStar_Syntax_Syntax.sigmeta = uu____26380;
                FStar_Syntax_Syntax.sigattrs = uu____26381;_}::[] ->
                let uu____26390 =
                  FStar_All.pipe_right names1
                    (FStar_List.collect
                       (fun nm  ->
                          let uu____26400 =
                            FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                              env0 nm
                             in
                          FStar_Pervasives_Native.snd uu____26400))
                   in
                FStar_All.pipe_right uu____26390
                  (FStar_List.filter
                     (fun t  ->
                        let uu____26422 = get_fail_attr false t  in
                        FStar_Option.isNone uu____26422))
            | uu____26442 -> []  in
          let attrs2 =
            let uu____26450 = mk_comment_attr d  in
            FStar_List.append uu____26450
              (FStar_List.append attrs1 val_attrs)
             in
          let uu____26459 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = Prims.int_zero
                   then
                     let uu___3413_26469 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3413_26469.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3413_26469.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3413_26469.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3413_26469.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3415_26472 = sigelt  in
                      let uu____26473 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____26479 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____26479) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3415_26472.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3415_26472.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3415_26472.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3415_26472.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____26473
                      })) sigelts
             in
          (env1, uu____26459)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26505 = desugar_decl_aux env d  in
      match uu____26505 with
      | (env1,ses) ->
          let uu____26516 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26516)

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
                FStar_Syntax_Syntax.sigattrs = []
              }  in
            (env, [se])))
      | FStar_Parser_AST.Fsdoc uu____26544 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____26549 = FStar_Syntax_DsEnv.iface env  in
          if uu____26549
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26564 =
               let uu____26566 =
                 let uu____26568 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26569 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26568
                   uu____26569
                  in
               Prims.op_Negation uu____26566  in
             if uu____26564
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26583 =
                  let uu____26585 =
                    let uu____26587 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26587 lid  in
                  Prims.op_Negation uu____26585  in
                if uu____26583
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26601 =
                     let uu____26603 =
                       let uu____26605 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26605
                         lid
                        in
                     Prims.op_Negation uu____26603  in
                   if uu____26601
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26623 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26623, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26664,uu____26665)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26704 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26731  ->
                 match uu____26731 with | (x,uu____26739) -> x) tcs
             in
          let uu____26744 =
            let uu____26749 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26749 tcs1  in
          (match uu____26744 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26766 =
                   let uu____26767 =
                     let uu____26774 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26774  in
                   [uu____26767]  in
                 let uu____26787 =
                   let uu____26790 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26793 =
                     let uu____26804 =
                       let uu____26813 =
                         let uu____26814 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26814  in
                       FStar_Syntax_Syntax.as_arg uu____26813  in
                     [uu____26804]  in
                   FStar_Syntax_Util.mk_app uu____26790 uu____26793  in
                 FStar_Syntax_Util.abs uu____26766 uu____26787
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26854,id1))::uu____26856 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26859::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26863 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26863 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26869 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26869]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26890) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26900,uu____26901,uu____26902,uu____26903,uu____26904)
                     ->
                     let uu____26913 =
                       let uu____26914 =
                         let uu____26915 =
                           let uu____26922 = mkclass lid  in
                           (meths, uu____26922)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26915  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26914;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26913]
                 | uu____26925 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26959;
                    FStar_Parser_AST.prange = uu____26960;_},uu____26961)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26971;
                    FStar_Parser_AST.prange = uu____26972;_},uu____26973)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26989;
                         FStar_Parser_AST.prange = uu____26990;_},uu____26991);
                    FStar_Parser_AST.prange = uu____26992;_},uu____26993)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27015;
                         FStar_Parser_AST.prange = uu____27016;_},uu____27017);
                    FStar_Parser_AST.prange = uu____27018;_},uu____27019)::[]
                   -> false
               | (p,uu____27048)::[] ->
                   let uu____27057 = is_app_pattern p  in
                   Prims.op_Negation uu____27057
               | uu____27059 -> false)
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
            let uu____27134 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27134 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27147 =
                     let uu____27148 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27148.FStar_Syntax_Syntax.n  in
                   match uu____27147 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27158) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let val_quals =
                         FStar_All.pipe_right fvs
                           (FStar_List.collect
                              (fun fv  ->
                                 let uu____27199 =
                                   FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 FStar_Pervasives_Native.fst uu____27199))
                          in
                       let quals1 =
                         match quals with
                         | uu____27217::uu____27218 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____27221 -> val_quals  in
                       let quals2 =
                         let uu____27225 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____27258  ->
                                   match uu____27258 with
                                   | (uu____27272,(uu____27273,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____27225
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____27293 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____27293
                         then
                           let uu____27299 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3593_27314 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3595_27316 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3595_27316.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3595_27316.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3593_27314.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3593_27314.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3593_27314.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3593_27314.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3593_27314.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3593_27314.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____27299)
                         else lbs  in
                       let names1 =
                         FStar_All.pipe_right fvs
                           (FStar_List.map
                              (fun fv  ->
                                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v))
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
                           FStar_Syntax_Syntax.sigattrs = []
                         }  in
                       let env1 = FStar_Syntax_DsEnv.push_sigelt env s  in
                       let env2 =
                         FStar_List.fold_left
                           (fun env2  ->
                              fun id1  ->
                                FStar_Syntax_DsEnv.push_doc env2 id1
                                  d.FStar_Parser_AST.doc) env1 names1
                          in
                       (env2, [s])
                   | uu____27343 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27351 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27370 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27351 with
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
                       let uu___3620_27407 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3620_27407.FStar_Parser_AST.prange)
                       }
                   | uu____27414 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3624_27421 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3624_27421.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___3624_27421.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3624_27421.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____27457 id1 =
                   match uu____27457 with
                   | (env1,ses) ->
                       let main =
                         let uu____27478 =
                           let uu____27479 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____27479  in
                         FStar_Parser_AST.mk_term uu____27478
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let lid = FStar_Ident.lid_of_ids [id1]  in
                       let projectee =
                         FStar_Parser_AST.mk_term (FStar_Parser_AST.Var lid)
                           FStar_Range.dummyRange FStar_Parser_AST.Expr
                          in
                       let body1 =
                         FStar_Parser_AST.mk_term
                           (FStar_Parser_AST.Match
                              (main,
                                [(pat, FStar_Pervasives_Native.None,
                                   projectee)])) FStar_Range.dummyRange
                           FStar_Parser_AST.Expr
                          in
                       let bv_pat =
                         FStar_Parser_AST.mk_pattern
                           (FStar_Parser_AST.PatVar
                              (id1, FStar_Pervasives_Native.None))
                           FStar_Range.dummyRange
                          in
                       let id_decl =
                         FStar_Parser_AST.mk_decl
                           (FStar_Parser_AST.TopLevelLet
                              (FStar_Parser_AST.NoLetQualifier,
                                [(bv_pat, body1)])) FStar_Range.dummyRange []
                          in
                       let uu____27529 = desugar_decl env1 id_decl  in
                       (match uu____27529 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27547 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27547 FStar_Util.set_elements
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
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          (env, [se])
      | FStar_Parser_AST.Assume (id1,t) ->
          let f = desugar_formula env t  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let env1 =
            FStar_Syntax_DsEnv.push_doc env lid d.FStar_Parser_AST.doc  in
          (env1,
            [{
               FStar_Syntax_Syntax.sigel =
                 (FStar_Syntax_Syntax.Sig_assume (lid, [], f));
               FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
               FStar_Syntax_Syntax.sigquals =
                 [FStar_Syntax_Syntax.Assumption];
               FStar_Syntax_Syntax.sigmeta =
                 FStar_Syntax_Syntax.default_sigmeta;
               FStar_Syntax_Syntax.sigattrs = []
             }])
      | FStar_Parser_AST.Val (id1,t) ->
          let quals = d.FStar_Parser_AST.quals  in
          let t1 =
            let uu____27571 = close_fun env t  in
            desugar_term env uu____27571  in
          let quals1 =
            let uu____27575 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27575
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27587 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27587;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = attrs
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc  in
          (env2, [se])
      | FStar_Parser_AST.Exception (id1,t_opt) ->
          let t =
            match t_opt with
            | FStar_Pervasives_Native.None  ->
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_lid env)
                  FStar_Parser_Const.exn_lid
            | FStar_Pervasives_Native.Some term ->
                let t = desugar_term env term  in
                let uu____27601 =
                  let uu____27610 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27610]  in
                let uu____27629 =
                  let uu____27632 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27632
                   in
                FStar_Syntax_Util.arrow uu____27601 uu____27629
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
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let se' =
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_bundle ([se], [l]));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = qual;
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
          let env2 =
            FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc  in
          let data_ops = mk_data_projector_names [] env2 se  in
          let discs = mk_data_discriminators [] env2 [l]  in
          let env3 =
            FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2
              (FStar_List.append discs data_ops)
             in
          (env3, (FStar_List.append (se' :: discs) data_ops))
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect
          (eff_name,eff_binders,defn)) ->
          let quals = d.FStar_Parser_AST.quals  in
          desugar_redefine_effect env d trans_qual1 quals eff_name
            eff_binders defn
      | FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect
          (eff_name,eff_binders,eff_typ,eff_decls)) ->
          let quals = d.FStar_Parser_AST.quals  in
          let attrs = d.FStar_Parser_AST.attrs  in
          desugar_effect env d quals eff_name eff_binders eff_typ eff_decls
            attrs
      | FStar_Parser_AST.SubEffect l ->
          let lookup1 l1 =
            let uu____27687 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27687 with
            | FStar_Pervasives_Native.None  ->
                let uu____27690 =
                  let uu____27696 =
                    let uu____27698 =
                      let uu____27700 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____27700 " not found"  in
                    Prims.op_Hat "Effect name " uu____27698  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27696)  in
                FStar_Errors.raise_error uu____27690
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27708 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27726 =
                  let uu____27729 =
                    let uu____27730 = desugar_term env t  in
                    ([], uu____27730)  in
                  FStar_Pervasives_Native.Some uu____27729  in
                (uu____27726, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27743 =
                  let uu____27746 =
                    let uu____27747 = desugar_term env wp  in
                    ([], uu____27747)  in
                  FStar_Pervasives_Native.Some uu____27746  in
                let uu____27754 =
                  let uu____27757 =
                    let uu____27758 = desugar_term env t  in
                    ([], uu____27758)  in
                  FStar_Pervasives_Native.Some uu____27757  in
                (uu____27743, uu____27754)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27770 =
                  let uu____27773 =
                    let uu____27774 = desugar_term env t  in
                    ([], uu____27774)  in
                  FStar_Pervasives_Native.Some uu____27773  in
                (FStar_Pervasives_Native.None, uu____27770)
             in
          (match uu____27708 with
           | (lift_wp,lift) ->
               let se =
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_sub_effect
                        {
                          FStar_Syntax_Syntax.source = src;
                          FStar_Syntax_Syntax.target = dst;
                          FStar_Syntax_Syntax.lift_wp = lift_wp;
                          FStar_Syntax_Syntax.lift = lift
                        });
                   FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                   FStar_Syntax_Syntax.sigquals = [];
                   FStar_Syntax_Syntax.sigmeta =
                     FStar_Syntax_Syntax.default_sigmeta;
                   FStar_Syntax_Syntax.sigattrs = []
                 }  in
               (env, [se]))
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____27808 =
              let uu____27809 =
                let uu____27816 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27816, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27809  in
            {
              FStar_Syntax_Syntax.sigel = uu____27808;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = []
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____27843 =
        FStar_List.fold_left
          (fun uu____27863  ->
             fun d  ->
               match uu____27863 with
               | (env1,sigelts) ->
                   let uu____27883 = desugar_decl env1 d  in
                   (match uu____27883 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27843 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____27974) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27978;
               FStar_Syntax_Syntax.exports = uu____27979;
               FStar_Syntax_Syntax.is_interface = uu____27980;_},FStar_Parser_AST.Module
             (current_lid,uu____27982)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27991) ->
              let uu____27994 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27994
           in
        let uu____27999 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28041 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28041, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28063 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28063, mname, decls, false)
           in
        match uu____27999 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28105 = desugar_decls env2 decls  in
            (match uu____28105 with
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
          let uu____28173 =
            (FStar_Options.interactive ()) &&
              (let uu____28176 =
                 let uu____28178 =
                   let uu____28180 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28180  in
                 FStar_Util.get_file_extension uu____28178  in
               FStar_List.mem uu____28176 ["fsti"; "fsi"])
             in
          if uu____28173 then as_interface m else m  in
        let uu____28194 = desugar_modul_common curmod env m1  in
        match uu____28194 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28216 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28216, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28238 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28238 with
      | (env1,modul,pop_when_done) ->
          let uu____28255 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28255 with
           | (env2,modul1) ->
               ((let uu____28267 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28267
                 then
                   let uu____28270 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28270
                 else ());
                (let uu____28275 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28275, modul1))))
  
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
        (fun uu____28325  ->
           let uu____28326 = desugar_modul env modul  in
           match uu____28326 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28364  ->
           let uu____28365 = desugar_decls env decls  in
           match uu____28365 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28416  ->
             let uu____28417 = desugar_partial_modul modul env a_modul  in
             match uu____28417 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28512 ->
                  let t =
                    let uu____28522 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28522  in
                  let uu____28535 =
                    let uu____28536 = FStar_Syntax_Subst.compress t  in
                    uu____28536.FStar_Syntax_Syntax.n  in
                  (match uu____28535 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28548,uu____28549)
                       -> bs1
                   | uu____28574 -> failwith "Impossible")
               in
            let uu____28584 =
              let uu____28591 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28591
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28584 with
            | (binders,uu____28593,binders_opening) ->
                let erase_term t =
                  let uu____28601 =
                    let uu____28602 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28602  in
                  FStar_Syntax_Subst.close binders uu____28601  in
                let erase_tscheme uu____28620 =
                  match uu____28620 with
                  | (us,t) ->
                      let t1 =
                        let uu____28640 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28640 t  in
                      let uu____28643 =
                        let uu____28644 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28644  in
                      ([], uu____28643)
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
                    | uu____28667 ->
                        let bs =
                          let uu____28677 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28677  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28717 =
                          let uu____28718 =
                            let uu____28721 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28721  in
                          uu____28718.FStar_Syntax_Syntax.n  in
                        (match uu____28717 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28723,uu____28724) -> bs1
                         | uu____28749 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28757 =
                      let uu____28758 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28758  in
                    FStar_Syntax_Subst.close binders uu____28757  in
                  let uu___3882_28759 = action  in
                  let uu____28760 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28761 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3882_28759.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3882_28759.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28760;
                    FStar_Syntax_Syntax.action_typ = uu____28761
                  }  in
                let uu___3884_28762 = ed  in
                let uu____28763 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28764 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____28765 = erase_tscheme ed.FStar_Syntax_Syntax.ret_wp
                   in
                let uu____28766 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_wp  in
                let uu____28767 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28768 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28769 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28770 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28771 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28772 = erase_tscheme ed.FStar_Syntax_Syntax.repr
                   in
                let uu____28773 =
                  erase_tscheme ed.FStar_Syntax_Syntax.return_repr  in
                let uu____28774 =
                  erase_tscheme ed.FStar_Syntax_Syntax.bind_repr  in
                let uu____28775 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3884_28762.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___3884_28762.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28763;
                  FStar_Syntax_Syntax.signature = uu____28764;
                  FStar_Syntax_Syntax.ret_wp = uu____28765;
                  FStar_Syntax_Syntax.bind_wp = uu____28766;
                  FStar_Syntax_Syntax.if_then_else = uu____28767;
                  FStar_Syntax_Syntax.ite_wp = uu____28768;
                  FStar_Syntax_Syntax.stronger = uu____28769;
                  FStar_Syntax_Syntax.close_wp = uu____28770;
                  FStar_Syntax_Syntax.trivial = uu____28771;
                  FStar_Syntax_Syntax.repr = uu____28772;
                  FStar_Syntax_Syntax.return_repr = uu____28773;
                  FStar_Syntax_Syntax.bind_repr = uu____28774;
                  FStar_Syntax_Syntax.actions = uu____28775;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3884_28762.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3891_28791 = se  in
                  let uu____28792 =
                    let uu____28793 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28793  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28792;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3891_28791.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3891_28791.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3891_28791.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3891_28791.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | FStar_Syntax_Syntax.Sig_new_effect_for_free ed ->
                let se' =
                  let uu___3897_28797 = se  in
                  let uu____28798 =
                    let uu____28799 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect_for_free uu____28799
                     in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28798;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3897_28797.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3897_28797.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3897_28797.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3897_28797.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28801 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28802 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28802 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28819 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28819
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28821 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28821)
  