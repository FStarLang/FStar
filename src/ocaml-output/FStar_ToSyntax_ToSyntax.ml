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
    | "interp" -> true
    | "mrelation" -> true
    | "repr" -> true
    | "post" -> true
    | "pre" -> true
    | "wp" -> true
    | uu____3553 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = Prims.int_zero
      then u
      else
        (let uu____3574 = sum_to_universe u (n1 - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3574)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3600 =
      let uu____3601 = unparen t  in uu____3601.FStar_Parser_AST.tm  in
    match uu____3600 with
    | FStar_Parser_AST.Wild  ->
        let uu____3607 =
          let uu____3608 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3608  in
        FStar_Util.Inr uu____3607
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3621)) ->
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
             let uu____3712 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3712
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3729 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3729
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3745 =
               let uu____3751 =
                 let uu____3753 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3753
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3751)
                in
             FStar_Errors.raise_error uu____3745 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3762 ->
        let rec aux t1 univargs =
          let uu____3799 =
            let uu____3800 = unparen t1  in uu____3800.FStar_Parser_AST.tm
             in
          match uu____3799 with
          | FStar_Parser_AST.App (t2,targ,uu____3808) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3835  ->
                     match uu___5_3835 with
                     | FStar_Util.Inr uu____3842 -> true
                     | uu____3845 -> false) univargs
              then
                let uu____3853 =
                  let uu____3854 =
                    FStar_List.map
                      (fun uu___6_3864  ->
                         match uu___6_3864 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3854  in
                FStar_Util.Inr uu____3853
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3890  ->
                        match uu___7_3890 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3900 -> failwith "impossible")
                     univargs
                    in
                 let uu____3904 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3904)
          | uu____3920 ->
              let uu____3921 =
                let uu____3927 =
                  let uu____3929 =
                    let uu____3931 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3931 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3929  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3927)  in
              FStar_Errors.raise_error uu____3921 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3946 ->
        let uu____3947 =
          let uu____3953 =
            let uu____3955 =
              let uu____3957 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3957 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3955  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3953)  in
        FStar_Errors.raise_error uu____3947 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____3998;_});
            FStar_Syntax_Syntax.pos = uu____3999;
            FStar_Syntax_Syntax.vars = uu____4000;_})::uu____4001
        ->
        let uu____4032 =
          let uu____4038 =
            let uu____4040 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4040
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4038)  in
        FStar_Errors.raise_error uu____4032 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4046 ->
        let uu____4065 =
          let uu____4071 =
            let uu____4073 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4073
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4071)  in
        FStar_Errors.raise_error uu____4065 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4086 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4086) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4114 = FStar_List.hd fields  in
        match uu____4114 with
        | (f,uu____4124) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4136 =
                match uu____4136 with
                | (f',uu____4142) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4144 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4144
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
              (let uu____4154 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4154);
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
          | FStar_Syntax_Syntax.Pat_dot_term uu____4517 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_wild uu____4524 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_constant uu____4525 ->
              FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_var x ->
              FStar_Util.set_add x FStar_Syntax_Syntax.no_names
          | FStar_Syntax_Syntax.Pat_cons (uu____4527,pats1) ->
              let aux out uu____4568 =
                match uu____4568 with
                | (p2,uu____4581) ->
                    let intersection =
                      let uu____4591 = pat_vars p2  in
                      FStar_Util.set_intersect uu____4591 out  in
                    let uu____4594 = FStar_Util.set_is_empty intersection  in
                    if uu____4594
                    then
                      let uu____4599 = pat_vars p2  in
                      FStar_Util.set_union out uu____4599
                    else
                      (let duplicate_bv =
                         let uu____4605 =
                           FStar_Util.set_elements intersection  in
                         FStar_List.hd uu____4605  in
                       let uu____4608 =
                         let uu____4614 =
                           FStar_Util.format1
                             "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                             (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                            in
                         (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                           uu____4614)
                          in
                       FStar_Errors.raise_error uu____4608 r)
                 in
              FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
           in
        match pats with
        | [] -> ()
        | p1::[] ->
            let uu____4638 = pat_vars p1  in
            FStar_All.pipe_right uu____4638 (fun a1  -> ())
        | p1::ps ->
            let pvars = pat_vars p1  in
            let aux p2 =
              let uu____4666 =
                let uu____4668 = pat_vars p2  in
                FStar_Util.set_eq pvars uu____4668  in
              if uu____4666
              then ()
              else
                (let nonlinear_vars =
                   let uu____4677 = pat_vars p2  in
                   FStar_Util.set_symmetric_difference pvars uu____4677  in
                 let first_nonlinear_var =
                   let uu____4681 = FStar_Util.set_elements nonlinear_vars
                      in
                   FStar_List.hd uu____4681  in
                 let uu____4684 =
                   let uu____4690 =
                     FStar_Util.format1
                       "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                       (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                      in
                   (FStar_Errors.Fatal_IncoherentPatterns, uu____4690)  in
                 FStar_Errors.raise_error uu____4684 r)
               in
            FStar_List.iter aux ps
         in
      let resolvex l e x =
        let uu____4718 =
          FStar_All.pipe_right l
            (FStar_Util.find_opt
               (fun y  ->
                  (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                    x.FStar_Ident.idText))
           in
        match uu____4718 with
        | FStar_Pervasives_Native.Some y -> (l, e, y)
        | uu____4735 ->
            let uu____4738 = FStar_Syntax_DsEnv.push_bv e x  in
            (match uu____4738 with | (e1,x1) -> ((x1 :: l), e1, x1))
         in
      let rec aux' top loc env1 p1 =
        let pos q = FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange
           in
        let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
        let orig = p1  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr uu____4889 -> failwith "impossible"
        | FStar_Parser_AST.PatOp op ->
            let uu____4913 =
              let uu____4914 =
                let uu____4915 =
                  let uu____4922 =
                    let uu____4923 =
                      let uu____4929 =
                        FStar_Parser_AST.compile_op Prims.int_zero
                          op.FStar_Ident.idText op.FStar_Ident.idRange
                         in
                      (uu____4929, (op.FStar_Ident.idRange))  in
                    FStar_Ident.mk_ident uu____4923  in
                  (uu____4922, FStar_Pervasives_Native.None)  in
                FStar_Parser_AST.PatVar uu____4915  in
              {
                FStar_Parser_AST.pat = uu____4914;
                FStar_Parser_AST.prange = (p1.FStar_Parser_AST.prange)
              }  in
            aux loc env1 uu____4913
        | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
            ((match tacopt with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some uu____4949 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                      "Type ascriptions within patterns cannot be associated with a tactic")
                    orig.FStar_Parser_AST.prange);
             (let uu____4952 = aux loc env1 p2  in
              match uu____4952 with
              | (loc1,env',binder,p3,annots,imp) ->
                  let annot_pat_var p4 t1 =
                    match p4.FStar_Syntax_Syntax.v with
                    | FStar_Syntax_Syntax.Pat_var x ->
                        let uu___931_5041 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_var
                               (let uu___933_5046 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___933_5046.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___933_5046.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___931_5041.FStar_Syntax_Syntax.p)
                        }
                    | FStar_Syntax_Syntax.Pat_wild x ->
                        let uu___937_5048 = p4  in
                        {
                          FStar_Syntax_Syntax.v =
                            (FStar_Syntax_Syntax.Pat_wild
                               (let uu___939_5053 = x  in
                                {
                                  FStar_Syntax_Syntax.ppname =
                                    (uu___939_5053.FStar_Syntax_Syntax.ppname);
                                  FStar_Syntax_Syntax.index =
                                    (uu___939_5053.FStar_Syntax_Syntax.index);
                                  FStar_Syntax_Syntax.sort = t1
                                }));
                          FStar_Syntax_Syntax.p =
                            (uu___937_5048.FStar_Syntax_Syntax.p)
                        }
                    | uu____5054 when top -> p4
                    | uu____5055 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                            "Type ascriptions within patterns are only allowed on variables")
                          orig.FStar_Parser_AST.prange
                     in
                  let uu____5060 =
                    match binder with
                    | LetBinder uu____5081 -> failwith "impossible"
                    | LocalBinder (x,aq) ->
                        let t1 =
                          let uu____5106 = close_fun env1 t  in
                          desugar_term env1 uu____5106  in
                        let x1 =
                          let uu___950_5108 = x  in
                          {
                            FStar_Syntax_Syntax.ppname =
                              (uu___950_5108.FStar_Syntax_Syntax.ppname);
                            FStar_Syntax_Syntax.index =
                              (uu___950_5108.FStar_Syntax_Syntax.index);
                            FStar_Syntax_Syntax.sort = t1
                          }  in
                        ([(x1, t1)], (LocalBinder (x1, aq)))
                     in
                  (match uu____5060 with
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
            let uu____5176 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
            (loc, env1, (LocalBinder (x, aq1)), uu____5176, [], imp)
        | FStar_Parser_AST.PatConst c ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                FStar_Syntax_Syntax.tun
               in
            let uu____5190 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5190, [], false)
        | FStar_Parser_AST.PatTvar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5214 = resolvex loc env1 x  in
            (match uu____5214 with
             | (loc1,env2,xbv) ->
                 let uu____5243 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5243, [], imp))
        | FStar_Parser_AST.PatVar (x,aq) ->
            let imp =
              aq = (FStar_Pervasives_Native.Some FStar_Parser_AST.Implicit)
               in
            let aq1 = trans_aqual env1 aq  in
            let uu____5266 = resolvex loc env1 x  in
            (match uu____5266 with
             | (loc1,env2,xbv) ->
                 let uu____5295 =
                   FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var xbv)
                    in
                 (loc1, env2, (LocalBinder (xbv, aq1)), uu____5295, [], imp))
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
            let uu____5310 =
              FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (l1, []))
               in
            (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
              uu____5310, [], false)
        | FStar_Parser_AST.PatApp
            ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
               FStar_Parser_AST.prange = uu____5340;_},args)
            ->
            let uu____5346 =
              FStar_List.fold_right
                (fun arg  ->
                   fun uu____5407  ->
                     match uu____5407 with
                     | (loc1,env2,annots,args1) ->
                         let uu____5488 = aux loc1 env2 arg  in
                         (match uu____5488 with
                          | (loc2,env3,uu____5535,arg1,ans,imp) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((arg1, imp) :: args1)))) args
                (loc, env1, [], [])
               in
            (match uu____5346 with
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
                 let uu____5667 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____5667, annots, false))
        | FStar_Parser_AST.PatApp uu____5685 ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
              p1.FStar_Parser_AST.prange
        | FStar_Parser_AST.PatList pats ->
            let uu____5716 =
              FStar_List.fold_right
                (fun pat  ->
                   fun uu____5767  ->
                     match uu____5767 with
                     | (loc1,env2,annots,pats1) ->
                         let uu____5828 = aux loc1 env2 pat  in
                         (match uu____5828 with
                          | (loc2,env3,uu____5870,pat1,ans,uu____5873) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                (pat1 :: pats1)))) pats (loc, env1, [], [])
               in
            (match uu____5716 with
             | (loc1,env2,annots,pats1) ->
                 let pat =
                   let uu____5970 =
                     let uu____5973 =
                       let uu____5980 =
                         FStar_Range.end_range p1.FStar_Parser_AST.prange  in
                       pos_r uu____5980  in
                     let uu____5981 =
                       let uu____5982 =
                         let uu____5996 =
                           FStar_Syntax_Syntax.lid_as_fv
                             FStar_Parser_Const.nil_lid
                             FStar_Syntax_Syntax.delta_constant
                             (FStar_Pervasives_Native.Some
                                FStar_Syntax_Syntax.Data_ctor)
                            in
                         (uu____5996, [])  in
                       FStar_Syntax_Syntax.Pat_cons uu____5982  in
                     FStar_All.pipe_left uu____5973 uu____5981  in
                   FStar_List.fold_right
                     (fun hd1  ->
                        fun tl1  ->
                          let r =
                            FStar_Range.union_ranges
                              hd1.FStar_Syntax_Syntax.p
                              tl1.FStar_Syntax_Syntax.p
                             in
                          let uu____6030 =
                            let uu____6031 =
                              let uu____6045 =
                                FStar_Syntax_Syntax.lid_as_fv
                                  FStar_Parser_Const.cons_lid
                                  FStar_Syntax_Syntax.delta_constant
                                  (FStar_Pervasives_Native.Some
                                     FStar_Syntax_Syntax.Data_ctor)
                                 in
                              (uu____6045, [(hd1, false); (tl1, false)])  in
                            FStar_Syntax_Syntax.Pat_cons uu____6031  in
                          FStar_All.pipe_left (pos_r r) uu____6030) pats1
                     uu____5970
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
            let uu____6103 =
              FStar_List.fold_left
                (fun uu____6163  ->
                   fun p2  ->
                     match uu____6163 with
                     | (loc1,env2,annots,pats) ->
                         let uu____6245 = aux loc1 env2 p2  in
                         (match uu____6245 with
                          | (loc2,env3,uu____6292,pat,ans,uu____6295) ->
                              (loc2, env3, (FStar_List.append ans annots),
                                ((pat, false) :: pats)))) (loc, env1, [], [])
                args
               in
            (match uu____6103 with
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
                   | uu____6461 -> failwith "impossible"  in
                 let x =
                   FStar_Syntax_Syntax.new_bv
                     (FStar_Pervasives_Native.Some
                        (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun
                    in
                 let uu____6464 =
                   FStar_All.pipe_left pos
                     (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                    in
                 (loc1, env2,
                   (LocalBinder (x, FStar_Pervasives_Native.None)),
                   uu____6464, annots, false))
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
                   (fun uu____6545  ->
                      match uu____6545 with
                      | (f,p2) -> ((f.FStar_Ident.ident), p2)))
               in
            let args =
              FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                (FStar_List.map
                   (fun uu____6575  ->
                      match uu____6575 with
                      | (f,uu____6581) ->
                          let uu____6582 =
                            FStar_All.pipe_right fields1
                              (FStar_List.tryFind
                                 (fun uu____6608  ->
                                    match uu____6608 with
                                    | (g,uu____6615) ->
                                        f.FStar_Ident.idText =
                                          g.FStar_Ident.idText))
                             in
                          (match uu____6582 with
                           | FStar_Pervasives_Native.None  ->
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatWild
                                    FStar_Pervasives_Native.None)
                                 p1.FStar_Parser_AST.prange
                           | FStar_Pervasives_Native.Some (uu____6621,p2) ->
                               p2)))
               in
            let app =
              let uu____6628 =
                let uu____6629 =
                  let uu____6636 =
                    let uu____6637 =
                      let uu____6638 =
                        FStar_Ident.lid_of_ids
                          (FStar_List.append
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                             [record.FStar_Syntax_DsEnv.constrname])
                         in
                      FStar_Parser_AST.PatName uu____6638  in
                    FStar_Parser_AST.mk_pattern uu____6637
                      p1.FStar_Parser_AST.prange
                     in
                  (uu____6636, args)  in
                FStar_Parser_AST.PatApp uu____6629  in
              FStar_Parser_AST.mk_pattern uu____6628
                p1.FStar_Parser_AST.prange
               in
            let uu____6641 = aux loc env1 app  in
            (match uu____6641 with
             | (env2,e,b,p2,annots,uu____6687) ->
                 let p3 =
                   match p2.FStar_Syntax_Syntax.v with
                   | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                       let uu____6727 =
                         let uu____6728 =
                           let uu____6742 =
                             let uu___1098_6743 = fv  in
                             let uu____6744 =
                               let uu____6747 =
                                 let uu____6748 =
                                   let uu____6755 =
                                     FStar_All.pipe_right
                                       record.FStar_Syntax_DsEnv.fields
                                       (FStar_List.map
                                          FStar_Pervasives_Native.fst)
                                      in
                                   ((record.FStar_Syntax_DsEnv.typename),
                                     uu____6755)
                                    in
                                 FStar_Syntax_Syntax.Record_ctor uu____6748
                                  in
                               FStar_Pervasives_Native.Some uu____6747  in
                             {
                               FStar_Syntax_Syntax.fv_name =
                                 (uu___1098_6743.FStar_Syntax_Syntax.fv_name);
                               FStar_Syntax_Syntax.fv_delta =
                                 (uu___1098_6743.FStar_Syntax_Syntax.fv_delta);
                               FStar_Syntax_Syntax.fv_qual = uu____6744
                             }  in
                           (uu____6742, args1)  in
                         FStar_Syntax_Syntax.Pat_cons uu____6728  in
                       FStar_All.pipe_left pos uu____6727
                   | uu____6781 -> p2  in
                 (env2, e, b, p3, annots, false))
      
      and aux loc env1 p1 = aux' false loc env1 p1
       in
      let aux_maybe_or env1 p1 =
        let loc = []  in
        match p1.FStar_Parser_AST.pat with
        | FStar_Parser_AST.PatOr [] -> failwith "impossible"
        | FStar_Parser_AST.PatOr (p2::ps) ->
            let uu____6867 = aux' true loc env1 p2  in
            (match uu____6867 with
             | (loc1,env2,var,p3,ans,uu____6911) ->
                 let uu____6926 =
                   FStar_List.fold_left
                     (fun uu____6975  ->
                        fun p4  ->
                          match uu____6975 with
                          | (loc2,env3,ps1) ->
                              let uu____7040 = aux' true loc2 env3 p4  in
                              (match uu____7040 with
                               | (loc3,env4,uu____7081,p5,ans1,uu____7084) ->
                                   (loc3, env4, ((p5, ans1) :: ps1))))
                     (loc1, env2, []) ps
                    in
                 (match uu____6926 with
                  | (loc2,env3,ps1) ->
                      let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                      (env3, var, pats)))
        | uu____7245 ->
            let uu____7246 = aux' true loc env1 p1  in
            (match uu____7246 with
             | (loc1,env2,vars,pat,ans,b) -> (env2, vars, [(pat, ans)]))
         in
      let uu____7343 = aux_maybe_or env p  in
      match uu____7343 with
      | (env1,b,pats) ->
          ((let uu____7398 = FStar_List.map FStar_Pervasives_Native.fst pats
               in
            check_linear_pattern_variables uu____7398
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
          let uu____7471 =
            let uu____7472 =
              let uu____7483 = FStar_Syntax_DsEnv.qualify env x  in
              (uu____7483, (ty, tacopt))  in
            LetBinder uu____7472  in
          (env, uu____7471, [])  in
        let op_to_ident x =
          let uu____7500 =
            let uu____7506 =
              FStar_Parser_AST.compile_op Prims.int_zero x.FStar_Ident.idText
                x.FStar_Ident.idRange
               in
            (uu____7506, (x.FStar_Ident.idRange))  in
          FStar_Ident.mk_ident uu____7500  in
        if top
        then
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7528 = op_to_ident x  in
              mklet uu____7528 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7530) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7536;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7552 = op_to_ident x  in
              let uu____7553 = desugar_term env t  in
              mklet uu____7552 uu____7553 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7555);
                 FStar_Parser_AST.prange = uu____7556;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7576 = desugar_term env t  in
              mklet x uu____7576 tacopt1
          | uu____7577 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7590 = desugar_data_pat env p  in
           match uu____7590 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7619;
                      FStar_Syntax_Syntax.p = uu____7620;_},uu____7621)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7634;
                      FStar_Syntax_Syntax.p = uu____7635;_},uu____7636)::[]
                     -> []
                 | uu____7649 -> p1  in
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
  fun uu____7657  ->
    fun env  ->
      fun pat  ->
        let uu____7661 = desugar_data_pat env pat  in
        match uu____7661 with | (env1,uu____7677,pat1) -> (env1, pat1)

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
      let uu____7699 = desugar_term_aq env e  in
      match uu____7699 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7718 = desugar_typ_aq env e  in
      match uu____7718 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7728  ->
        fun range  ->
          match uu____7728 with
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
              ((let uu____7750 =
                  let uu____7752 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7752  in
                if uu____7750
                then
                  let uu____7755 =
                    let uu____7761 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7761)  in
                  FStar_Errors.log_issue range uu____7755
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
                  let uu____7782 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7782 range  in
                let lid1 =
                  let uu____7786 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7786 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7796 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7796 range  in
                           let private_fv =
                             let uu____7798 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7798 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1268_7799 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1268_7799.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1268_7799.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7800 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7804 =
                        let uu____7810 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7810)
                         in
                      FStar_Errors.raise_error uu____7804 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7830 =
                  let uu____7837 =
                    let uu____7838 =
                      let uu____7855 =
                        let uu____7866 =
                          let uu____7875 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7875)  in
                        [uu____7866]  in
                      (lid1, uu____7855)  in
                    FStar_Syntax_Syntax.Tm_app uu____7838  in
                  FStar_Syntax_Syntax.mk uu____7837  in
                uu____7830 FStar_Pervasives_Native.None range))

and (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____7923 =
          let uu____7924 = unparen t  in uu____7924.FStar_Parser_AST.tm  in
        match uu____7923 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____7925; FStar_Ident.ident = uu____7926;
              FStar_Ident.nsstr = uu____7927; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____7932 ->
            let uu____7933 =
              let uu____7939 =
                let uu____7941 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____7941  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____7939)  in
            FStar_Errors.raise_error uu____7933 t.FStar_Parser_AST.range
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
          let uu___1295_8028 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1295_8028.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1295_8028.FStar_Syntax_Syntax.vars)
          }  in
        let uu____8031 =
          let uu____8032 = unparen top  in uu____8032.FStar_Parser_AST.tm  in
        match uu____8031 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____8037 ->
            let uu____8046 = desugar_formula env top  in (uu____8046, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____8055 = desugar_formula env t  in (uu____8055, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____8064 = desugar_formula env t  in (uu____8064, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____8091 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____8091, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____8093 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____8093, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____8102 =
                let uu____8103 =
                  let uu____8110 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____8110, args)  in
                FStar_Parser_AST.Op uu____8103  in
              FStar_Parser_AST.mk_term uu____8102 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____8115 =
              let uu____8116 =
                let uu____8117 =
                  let uu____8124 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____8124, [e])  in
                FStar_Parser_AST.Op uu____8117  in
              FStar_Parser_AST.mk_term uu____8116 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____8115
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____8136 = FStar_Ident.text_of_id op_star  in
             uu____8136 = "*") &&
              (let uu____8141 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____8141 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8158;_},t1::t2::[])
                  when
                  let uu____8164 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8164 FStar_Option.isNone ->
                  let uu____8171 = flatten1 t1  in
                  FStar_List.append uu____8171 [t2]
              | uu____8174 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1343_8179 = top  in
              let uu____8180 =
                let uu____8181 =
                  let uu____8192 =
                    FStar_List.map (fun _8203  -> FStar_Util.Inr _8203) terms
                     in
                  (uu____8192, rhs)  in
                FStar_Parser_AST.Sum uu____8181  in
              {
                FStar_Parser_AST.tm = uu____8180;
                FStar_Parser_AST.range =
                  (uu___1343_8179.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1343_8179.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8211 =
              let uu____8212 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8212  in
            (uu____8211, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8218 =
              let uu____8224 =
                let uu____8226 =
                  let uu____8228 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8228 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8226  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8224)  in
            FStar_Errors.raise_error uu____8218 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8243 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8243 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8250 =
                   let uu____8256 =
                     let uu____8258 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8258
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8256)
                    in
                 FStar_Errors.raise_error uu____8250
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8273 =
                     let uu____8298 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8360 = desugar_term_aq env t  in
                               match uu____8360 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8298 FStar_List.unzip  in
                   (match uu____8273 with
                    | (args1,aqs) ->
                        let uu____8493 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8493, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8510)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8527 =
              let uu___1372_8528 = top  in
              let uu____8529 =
                let uu____8530 =
                  let uu____8537 =
                    let uu___1374_8538 = top  in
                    let uu____8539 =
                      let uu____8540 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8540  in
                    {
                      FStar_Parser_AST.tm = uu____8539;
                      FStar_Parser_AST.range =
                        (uu___1374_8538.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1374_8538.FStar_Parser_AST.level)
                    }  in
                  (uu____8537, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8530  in
              {
                FStar_Parser_AST.tm = uu____8529;
                FStar_Parser_AST.range =
                  (uu___1372_8528.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1372_8528.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8527
        | FStar_Parser_AST.Construct (n1,(a,uu____8548)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8568 =
                let uu___1384_8569 = top  in
                let uu____8570 =
                  let uu____8571 =
                    let uu____8578 =
                      let uu___1386_8579 = top  in
                      let uu____8580 =
                        let uu____8581 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8581  in
                      {
                        FStar_Parser_AST.tm = uu____8580;
                        FStar_Parser_AST.range =
                          (uu___1386_8579.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1386_8579.FStar_Parser_AST.level)
                      }  in
                    (uu____8578, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8571  in
                {
                  FStar_Parser_AST.tm = uu____8570;
                  FStar_Parser_AST.range =
                    (uu___1384_8569.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1384_8569.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8568))
        | FStar_Parser_AST.Construct (n1,(a,uu____8589)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8606 =
              let uu___1395_8607 = top  in
              let uu____8608 =
                let uu____8609 =
                  let uu____8616 =
                    let uu___1397_8617 = top  in
                    let uu____8618 =
                      let uu____8619 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8619  in
                    {
                      FStar_Parser_AST.tm = uu____8618;
                      FStar_Parser_AST.range =
                        (uu___1397_8617.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1397_8617.FStar_Parser_AST.level)
                    }  in
                  (uu____8616, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8609  in
              {
                FStar_Parser_AST.tm = uu____8608;
                FStar_Parser_AST.range =
                  (uu___1395_8607.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1395_8607.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8606
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8625; FStar_Ident.ident = uu____8626;
              FStar_Ident.nsstr = uu____8627; FStar_Ident.str = "Type0";_}
            ->
            let uu____8632 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8632, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8633; FStar_Ident.ident = uu____8634;
              FStar_Ident.nsstr = uu____8635; FStar_Ident.str = "Type";_}
            ->
            let uu____8640 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8640, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8641; FStar_Ident.ident = uu____8642;
               FStar_Ident.nsstr = uu____8643; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8663 =
              let uu____8664 =
                let uu____8665 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8665  in
              mk1 uu____8664  in
            (uu____8663, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8666; FStar_Ident.ident = uu____8667;
              FStar_Ident.nsstr = uu____8668; FStar_Ident.str = "Effect";_}
            ->
            let uu____8673 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8673, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8674; FStar_Ident.ident = uu____8675;
              FStar_Ident.nsstr = uu____8676; FStar_Ident.str = "True";_}
            ->
            let uu____8681 =
              let uu____8682 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8682
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8681, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8683; FStar_Ident.ident = uu____8684;
              FStar_Ident.nsstr = uu____8685; FStar_Ident.str = "False";_}
            ->
            let uu____8690 =
              let uu____8691 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8691
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8690, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8694;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8697 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8697 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8706 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         Prims.int_one) FStar_Pervasives_Native.None
                     in
                  (uu____8706, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8708 =
                    let uu____8710 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8710 txt
                     in
                  failwith uu____8708))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8719 = desugar_name mk1 setpos env true l  in
              (uu____8719, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8728 = desugar_name mk1 setpos env true l  in
              (uu____8728, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8746 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8746 with
                | FStar_Pervasives_Native.Some uu____8756 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8764 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8764 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8782 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8803 =
                    let uu____8804 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8804  in
                  (uu____8803, noaqs)
              | uu____8810 ->
                  let uu____8818 =
                    let uu____8824 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8824)  in
                  FStar_Errors.raise_error uu____8818
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8834 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8834 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8841 =
                    let uu____8847 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8847)
                     in
                  FStar_Errors.raise_error uu____8841
                    top.FStar_Parser_AST.range
              | uu____8855 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8859 = desugar_name mk1 setpos env true lid'  in
                  (uu____8859, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8881 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8881 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8900 ->
                       let uu____8907 =
                         FStar_Util.take
                           (fun uu____8931  ->
                              match uu____8931 with
                              | (uu____8937,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8907 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8982 =
                              let uu____9007 =
                                FStar_List.map
                                  (fun uu____9050  ->
                                     match uu____9050 with
                                     | (t,imp) ->
                                         let uu____9067 =
                                           desugar_term_aq env t  in
                                         (match uu____9067 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____9007
                                FStar_List.unzip
                               in
                            (match uu____8982 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9210 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9210, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9229 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9229 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9240 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9268  ->
                 match uu___8_9268 with
                 | FStar_Util.Inr uu____9274 -> true
                 | uu____9276 -> false) binders
            ->
            let terms =
              let uu____9285 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9302  ->
                        match uu___9_9302 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9308 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9285 [t]  in
            let uu____9310 =
              let uu____9335 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9392 = desugar_typ_aq env t1  in
                        match uu____9392 with
                        | (t',aq) ->
                            let uu____9403 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9403, aq)))
                 in
              FStar_All.pipe_right uu____9335 FStar_List.unzip  in
            (match uu____9310 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9513 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9513
                    in
                 let uu____9522 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9522, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9549 =
              let uu____9566 =
                let uu____9573 =
                  let uu____9580 =
                    FStar_All.pipe_left (fun _9589  -> FStar_Util.Inl _9589)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9580]  in
                FStar_List.append binders uu____9573  in
              FStar_List.fold_left
                (fun uu____9634  ->
                   fun b  ->
                     match uu____9634 with
                     | (env1,tparams,typs) ->
                         let uu____9695 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9710 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9710)
                            in
                         (match uu____9695 with
                          | (xopt,t1) ->
                              let uu____9735 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9744 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9744)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9735 with
                               | (env2,x) ->
                                   let uu____9764 =
                                     let uu____9767 =
                                       let uu____9770 =
                                         let uu____9771 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9771
                                          in
                                       [uu____9770]  in
                                     FStar_List.append typs uu____9767  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1556_9797 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1556_9797.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1556_9797.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9764)))) (env, [], []) uu____9566
               in
            (match uu____9549 with
             | (env1,uu____9825,targs) ->
                 let tup =
                   let uu____9848 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9848
                    in
                 let uu____9849 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9849, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9868 = uncurry binders t  in
            (match uu____9868 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9912 =
                   match uu___10_9912 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9929 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9929
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9953 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9953 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9986 = aux env [] bs  in (uu____9986, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9995 = desugar_binder env b  in
            (match uu____9995 with
             | (FStar_Pervasives_Native.None ,uu____10006) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____10021 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____10021 with
                  | ((x,uu____10037),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____10050 =
                        let uu____10051 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____10051  in
                      (uu____10050, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss =
              FStar_List.map (gather_pattern_bound_vars false) binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____10130 = FStar_Util.set_is_empty i  in
                    if uu____10130
                    then
                      let uu____10135 = FStar_Util.set_union acc set1  in
                      aux uu____10135 sets2
                    else
                      (let uu____10140 =
                         let uu____10141 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____10141  in
                       FStar_Pervasives_Native.Some uu____10140)
                 in
              let uu____10144 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____10144 sets  in
            ((let uu____10148 = check_disjoint bvss  in
              match uu____10148 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____10152 =
                    let uu____10158 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____10158)
                     in
                  let uu____10162 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____10152 uu____10162);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10170 =
                FStar_List.fold_left
                  (fun uu____10190  ->
                     fun pat  ->
                       match uu____10190 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10216,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10226 =
                                  let uu____10229 = free_type_vars env1 t  in
                                  FStar_List.append uu____10229 ftvs  in
                                (env1, uu____10226)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10234,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10245 =
                                  let uu____10248 = free_type_vars env1 t  in
                                  let uu____10251 =
                                    let uu____10254 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10254 ftvs  in
                                  FStar_List.append uu____10248 uu____10251
                                   in
                                (env1, uu____10245)
                            | uu____10259 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10170 with
              | (uu____10268,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10280 =
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
                    FStar_List.append uu____10280 binders1  in
                  let rec aux env1 bs sc_pat_opt uu___11_10337 =
                    match uu___11_10337 with
                    | [] ->
                        let uu____10364 = desugar_term_aq env1 body  in
                        (match uu____10364 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10401 =
                                       let uu____10402 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10402
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10401
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
                             let uu____10471 =
                               let uu____10474 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10474  in
                             (uu____10471, aq))
                    | p::rest ->
                        let uu____10489 = desugar_binding_pat env1 p  in
                        (match uu____10489 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10523)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10538 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10547 =
                               match b with
                               | LetBinder uu____10588 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10657) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10711 =
                                           let uu____10720 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10720, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10711
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10782,uu____10783) ->
                                              let tup2 =
                                                let uu____10785 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10785
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10790 =
                                                  let uu____10797 =
                                                    let uu____10798 =
                                                      let uu____10815 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10818 =
                                                        let uu____10829 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10838 =
                                                          let uu____10849 =
                                                            let uu____10858 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10858
                                                             in
                                                          [uu____10849]  in
                                                        uu____10829 ::
                                                          uu____10838
                                                         in
                                                      (uu____10815,
                                                        uu____10818)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10798
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10797
                                                   in
                                                uu____10790
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10906 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10906
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10957,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10959,pats)) ->
                                              let tupn =
                                                let uu____11004 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____11004
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____11017 =
                                                  let uu____11018 =
                                                    let uu____11035 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____11038 =
                                                      let uu____11049 =
                                                        let uu____11060 =
                                                          let uu____11069 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____11069
                                                           in
                                                        [uu____11060]  in
                                                      FStar_List.append args
                                                        uu____11049
                                                       in
                                                    (uu____11035,
                                                      uu____11038)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____11018
                                                   in
                                                mk1 uu____11017  in
                                              let p2 =
                                                let uu____11117 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats [(p1, false)])))
                                                  uu____11117
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____11164 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10547 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11258,uu____11259,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11281 =
                let uu____11282 = unparen e  in
                uu____11282.FStar_Parser_AST.tm  in
              match uu____11281 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11292 ->
                  let uu____11293 = desugar_term_aq env e  in
                  (match uu____11293 with
                   | (head1,aq) ->
                       let uu____11306 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11306, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11313 ->
            let rec aux args aqs e =
              let uu____11390 =
                let uu____11391 = unparen e  in
                uu____11391.FStar_Parser_AST.tm  in
              match uu____11390 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11409 = desugar_term_aq env t  in
                  (match uu____11409 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11457 ->
                  let uu____11458 = desugar_term_aq env e  in
                  (match uu____11458 with
                   | (head1,aq) ->
                       let uu____11479 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11479, (join_aqs (aq :: aqs))))
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
            let uu____11542 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11542
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
            let uu____11594 = desugar_term_aq env t  in
            (match uu____11594 with
             | (tm,s) ->
                 let uu____11605 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11605, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11611 =
              let uu____11624 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11624 then desugar_typ_aq else desugar_term_aq  in
            uu____11611 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11683 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11826  ->
                        match uu____11826 with
                        | (attr_opt,(p,def)) ->
                            let uu____11884 = is_app_pattern p  in
                            if uu____11884
                            then
                              let uu____11917 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11917, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____12000 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____12000, def1)
                               | uu____12045 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____12083);
                                           FStar_Parser_AST.prange =
                                             uu____12084;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____12133 =
                                            let uu____12154 =
                                              let uu____12159 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12159  in
                                            (uu____12154, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____12133, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12251) ->
                                        if top_level
                                        then
                                          let uu____12287 =
                                            let uu____12308 =
                                              let uu____12313 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12313  in
                                            (uu____12308, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12287, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12404 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12437 =
                FStar_List.fold_left
                  (fun uu____12510  ->
                     fun uu____12511  ->
                       match (uu____12510, uu____12511) with
                       | ((env1,fnames,rec_bindings),(_attr_opt,(f,uu____12619,uu____12620),uu____12621))
                           ->
                           let uu____12738 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12764 =
                                   FStar_Syntax_DsEnv.push_bv env1 x  in
                                 (match uu____12764 with
                                  | (env2,xx) ->
                                      let uu____12783 =
                                        let uu____12786 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12786 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12783))
                             | FStar_Util.Inr l ->
                                 let uu____12794 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (uu____12794, (FStar_Util.Inr l),
                                   rec_bindings)
                              in
                           (match uu____12738 with
                            | (env2,lbname,rec_bindings1) ->
                                (env2, (lbname :: fnames), rec_bindings1)))
                  (env, [], []) funs
                 in
              match uu____12437 with
              | (env',fnames,rec_bindings) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let desugar_one_def env1 lbname uu____12942 =
                    match uu____12942 with
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
                                let uu____13066 = is_comp_type env1 t  in
                                if uu____13066
                                then
                                  ((let uu____13070 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13080 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13080))
                                       in
                                    match uu____13070 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13087 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13090 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13090))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13087
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
                          | uu____13101 ->
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
                              let uu____13116 =
                                let uu____13117 =
                                  FStar_Syntax_Util.incr_delta_qualifier
                                    body1
                                   in
                                FStar_Syntax_Syntax.lid_as_fv l uu____13117
                                  FStar_Pervasives_Native.None
                                 in
                              FStar_Util.Inr uu____13116
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
                  let uu____13198 = desugar_term_aq env' body  in
                  (match uu____13198 with
                   | (body1,aq) ->
                       let uu____13211 =
                         let uu____13214 =
                           let uu____13215 =
                             let uu____13229 =
                               FStar_Syntax_Subst.close rec_bindings1 body1
                                in
                             ((is_rec, lbs1), uu____13229)  in
                           FStar_Syntax_Syntax.Tm_let uu____13215  in
                         FStar_All.pipe_left mk1 uu____13214  in
                       (uu____13211, aq))
               in
            let ds_non_rec attrs_opt pat t1 t2 =
              let attrs =
                match attrs_opt with
                | FStar_Pervasives_Native.None  -> []
                | FStar_Pervasives_Native.Some l ->
                    FStar_List.map (desugar_term env) l
                 in
              let t11 = desugar_term env t1  in
              let uu____13304 =
                desugar_binding_pat_maybe_top top_level env pat  in
              match uu____13304 with
              | (env1,binder,pat1) ->
                  let uu____13326 =
                    match binder with
                    | LetBinder (l,(t,_tacopt)) ->
                        let uu____13352 = desugar_term_aq env1 t2  in
                        (match uu____13352 with
                         | (body1,aq) ->
                             let fv =
                               let uu____13366 =
                                 FStar_Syntax_Util.incr_delta_qualifier t11
                                  in
                               FStar_Syntax_Syntax.lid_as_fv l uu____13366
                                 FStar_Pervasives_Native.None
                                in
                             let uu____13367 =
                               FStar_All.pipe_left mk1
                                 (FStar_Syntax_Syntax.Tm_let
                                    ((false,
                                       [mk_lb
                                          (attrs, (FStar_Util.Inr fv), t,
                                            t11,
                                            (t11.FStar_Syntax_Syntax.pos))]),
                                      body1))
                                in
                             (uu____13367, aq))
                    | LocalBinder (x,uu____13400) ->
                        let uu____13401 = desugar_term_aq env1 t2  in
                        (match uu____13401 with
                         | (body1,aq) ->
                             let body2 =
                               match pat1 with
                               | [] -> body1
                               | ({
                                    FStar_Syntax_Syntax.v =
                                      FStar_Syntax_Syntax.Pat_wild
                                      uu____13415;
                                    FStar_Syntax_Syntax.p = uu____13416;_},uu____13417)::[]
                                   -> body1
                               | uu____13430 ->
                                   let uu____13433 =
                                     let uu____13440 =
                                       let uu____13441 =
                                         let uu____13464 =
                                           FStar_Syntax_Syntax.bv_to_name x
                                            in
                                         let uu____13467 =
                                           desugar_disjunctive_pattern pat1
                                             FStar_Pervasives_Native.None
                                             body1
                                            in
                                         (uu____13464, uu____13467)  in
                                       FStar_Syntax_Syntax.Tm_match
                                         uu____13441
                                        in
                                     FStar_Syntax_Syntax.mk uu____13440  in
                                   uu____13433 FStar_Pervasives_Native.None
                                     top.FStar_Parser_AST.range
                                in
                             let uu____13504 =
                               let uu____13507 =
                                 let uu____13508 =
                                   let uu____13522 =
                                     let uu____13525 =
                                       let uu____13526 =
                                         FStar_Syntax_Syntax.mk_binder x  in
                                       [uu____13526]  in
                                     FStar_Syntax_Subst.close uu____13525
                                       body2
                                      in
                                   ((false,
                                      [mk_lb
                                         (attrs, (FStar_Util.Inl x),
                                           (x.FStar_Syntax_Syntax.sort), t11,
                                           (t11.FStar_Syntax_Syntax.pos))]),
                                     uu____13522)
                                    in
                                 FStar_Syntax_Syntax.Tm_let uu____13508  in
                               FStar_All.pipe_left mk1 uu____13507  in
                             (uu____13504, aq))
                     in
                  (match uu____13326 with | (tm,aq) -> (tm, aq))
               in
            let uu____13588 = FStar_List.hd lbs  in
            (match uu____13588 with
             | (attrs,(head_pat,defn)) ->
                 let uu____13632 = is_rec || (is_app_pattern head_pat)  in
                 if uu____13632
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____13648 =
                let uu____13649 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____13649  in
              mk1 uu____13648  in
            let uu____13650 = desugar_term_aq env t1  in
            (match uu____13650 with
             | (t1',aq1) ->
                 let uu____13661 = desugar_term_aq env t2  in
                 (match uu____13661 with
                  | (t2',aq2) ->
                      let uu____13672 = desugar_term_aq env t3  in
                      (match uu____13672 with
                       | (t3',aq3) ->
                           let uu____13683 =
                             let uu____13684 =
                               let uu____13685 =
                                 let uu____13708 =
                                   let uu____13725 =
                                     let uu____13740 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____13740,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____13754 =
                                     let uu____13771 =
                                       let uu____13786 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____13786,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____13771]  in
                                   uu____13725 :: uu____13754  in
                                 (t1', uu____13708)  in
                               FStar_Syntax_Syntax.Tm_match uu____13685  in
                             mk1 uu____13684  in
                           (uu____13683, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____13982 =
              match uu____13982 with
              | (pat,wopt,b) ->
                  let uu____14004 = desugar_match_pat env pat  in
                  (match uu____14004 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14035 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14035
                          in
                       let uu____14040 = desugar_term_aq env1 b  in
                       (match uu____14040 with
                        | (b1,aq) ->
                            let uu____14053 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14053, aq)))
               in
            let uu____14058 = desugar_term_aq env e  in
            (match uu____14058 with
             | (e1,aq) ->
                 let uu____14069 =
                   let uu____14100 =
                     let uu____14133 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14133 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14100
                     (fun uu____14351  ->
                        match uu____14351 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14069 with
                  | (brs,aqs) ->
                      let uu____14570 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____14570, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____14604 =
              let uu____14625 = is_comp_type env t  in
              if uu____14625
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____14680 = desugar_term_aq env t  in
                 match uu____14680 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____14604 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____14772 = desugar_term_aq env e  in
                 (match uu____14772 with
                  | (e1,aq) ->
                      let uu____14783 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____14783, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____14822,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____14865 = FStar_List.hd fields  in
              match uu____14865 with | (f,uu____14877) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____14923  ->
                        match uu____14923 with
                        | (g,uu____14930) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____14937,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____14951 =
                         let uu____14957 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____14957)
                          in
                       FStar_Errors.raise_error uu____14951
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
                  let uu____14968 =
                    let uu____14979 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15010  ->
                              match uu____15010 with
                              | (f,uu____15020) ->
                                  let uu____15021 =
                                    let uu____15022 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15022
                                     in
                                  (uu____15021, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____14979)  in
                  FStar_Parser_AST.Construct uu____14968
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15040 =
                      let uu____15041 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15041  in
                    FStar_Parser_AST.mk_term uu____15040
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15043 =
                      let uu____15056 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15086  ->
                                match uu____15086 with
                                | (f,uu____15096) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15056)  in
                    FStar_Parser_AST.Record uu____15043  in
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
            let uu____15156 = desugar_term_aq env recterm1  in
            (match uu____15156 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15172;
                         FStar_Syntax_Syntax.vars = uu____15173;_},args)
                      ->
                      let uu____15199 =
                        let uu____15200 =
                          let uu____15201 =
                            let uu____15218 =
                              let uu____15221 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15222 =
                                let uu____15225 =
                                  let uu____15226 =
                                    let uu____15233 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15233)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15226
                                   in
                                FStar_Pervasives_Native.Some uu____15225  in
                              FStar_Syntax_Syntax.fvar uu____15221
                                FStar_Syntax_Syntax.delta_constant
                                uu____15222
                               in
                            (uu____15218, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15201  in
                        FStar_All.pipe_left mk1 uu____15200  in
                      (uu____15199, s)
                  | uu____15262 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15266 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15266 with
              | (constrname,is_rec) ->
                  let uu____15285 = desugar_term_aq env e  in
                  (match uu____15285 with
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
                       let uu____15305 =
                         let uu____15306 =
                           let uu____15307 =
                             let uu____15324 =
                               let uu____15327 =
                                 let uu____15328 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15328
                                  in
                               FStar_Syntax_Syntax.fvar uu____15327
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    Prims.int_one) qual
                                in
                             let uu____15330 =
                               let uu____15341 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15341]  in
                             (uu____15324, uu____15330)  in
                           FStar_Syntax_Syntax.Tm_app uu____15307  in
                         FStar_All.pipe_left mk1 uu____15306  in
                       (uu____15305, s))))
        | FStar_Parser_AST.NamedTyp (uu____15378,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15388 =
              let uu____15389 = FStar_Syntax_Subst.compress tm  in
              uu____15389.FStar_Syntax_Syntax.n  in
            (match uu____15388 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15397 =
                   let uu___2090_15398 =
                     let uu____15399 =
                       let uu____15401 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15401  in
                     FStar_Syntax_Util.exp_string uu____15399  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2090_15398.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2090_15398.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15397, noaqs)
             | uu____15402 ->
                 let uu____15403 =
                   let uu____15409 =
                     let uu____15411 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15411
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15409)  in
                 FStar_Errors.raise_error uu____15403
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15420 = desugar_term_aq env e  in
            (match uu____15420 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15432 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15432, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____15437 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____15438 =
              let uu____15439 =
                let uu____15446 = desugar_term env e  in (bv, uu____15446)
                 in
              [uu____15439]  in
            (uu____15437, uu____15438)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____15471 =
              let uu____15472 =
                let uu____15473 =
                  let uu____15480 = desugar_term env e  in (uu____15480, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____15473  in
              FStar_All.pipe_left mk1 uu____15472  in
            (uu____15471, noaqs)
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
              let uu____15509 =
                let uu____15510 =
                  let uu____15517 =
                    let uu____15518 =
                      let uu____15519 =
                        let uu____15528 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____15541 =
                          let uu____15542 =
                            let uu____15543 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____15543  in
                          FStar_Parser_AST.mk_term uu____15542
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____15528, uu____15541,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____15519  in
                    FStar_Parser_AST.mk_term uu____15518
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____15517)  in
                FStar_Parser_AST.Abs uu____15510  in
              FStar_Parser_AST.mk_term uu____15509
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
              let uu____15558 = FStar_List.last steps  in
              match uu____15558 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____15561,uu____15562,last_expr)) -> last_expr
              | uu____15564 -> failwith "impossible: no last_expr on calc"
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
            let uu____15592 =
              FStar_List.fold_left
                (fun uu____15609  ->
                   fun uu____15610  ->
                     match (uu____15609, uu____15610) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let pf =
                           let uu____15633 =
                             let uu____15640 =
                               let uu____15647 =
                                 let uu____15654 =
                                   let uu____15661 =
                                     let uu____15666 = eta_and_annot rel2  in
                                     (uu____15666, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____15667 =
                                     let uu____15674 =
                                       let uu____15681 =
                                         let uu____15686 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____15686,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____15687 =
                                         let uu____15694 =
                                           let uu____15699 =
                                             FStar_Parser_AST.thunk just  in
                                           (uu____15699,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____15694]  in
                                       uu____15681 :: uu____15687  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____15674
                                      in
                                   uu____15661 :: uu____15667  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____15654
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____15647
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____15640
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____15633
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____15592 with
             | (e1,uu____15737) ->
                 let e2 =
                   let uu____15739 =
                     let uu____15746 =
                       let uu____15753 =
                         let uu____15760 =
                           let uu____15765 = FStar_Parser_AST.thunk e1  in
                           (uu____15765, FStar_Parser_AST.Nothing)  in
                         [uu____15760]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____15753  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____15746  in
                   FStar_Parser_AST.mkApp finish1 uu____15739
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____15782 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____15783 = desugar_formula env top  in
            (uu____15783, noaqs)
        | uu____15784 ->
            let uu____15785 =
              let uu____15791 =
                let uu____15793 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____15793  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____15791)  in
            FStar_Errors.raise_error uu____15785 top.FStar_Parser_AST.range

and (not_ascribed : FStar_Parser_AST.term -> Prims.bool) =
  fun t  ->
    match t.FStar_Parser_AST.tm with
    | FStar_Parser_AST.Ascribed uu____15803 -> false
    | uu____15813 -> true

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
           (fun uu____15851  ->
              match uu____15851 with
              | (a,imp) ->
                  let uu____15864 = desugar_term env a  in
                  arg_withimp_e imp uu____15864))

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
          let is_requires uu____15901 =
            match uu____15901 with
            | (t1,uu____15908) ->
                let uu____15909 =
                  let uu____15910 = unparen t1  in
                  uu____15910.FStar_Parser_AST.tm  in
                (match uu____15909 with
                 | FStar_Parser_AST.Requires uu____15912 -> true
                 | uu____15921 -> false)
             in
          let is_ensures uu____15933 =
            match uu____15933 with
            | (t1,uu____15940) ->
                let uu____15941 =
                  let uu____15942 = unparen t1  in
                  uu____15942.FStar_Parser_AST.tm  in
                (match uu____15941 with
                 | FStar_Parser_AST.Ensures uu____15944 -> true
                 | uu____15953 -> false)
             in
          let is_app head1 uu____15971 =
            match uu____15971 with
            | (t1,uu____15979) ->
                let uu____15980 =
                  let uu____15981 = unparen t1  in
                  uu____15981.FStar_Parser_AST.tm  in
                (match uu____15980 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____15984;
                        FStar_Parser_AST.level = uu____15985;_},uu____15986,uu____15987)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____15989 -> false)
             in
          let is_smt_pat uu____16001 =
            match uu____16001 with
            | (t1,uu____16008) ->
                let uu____16009 =
                  let uu____16010 = unparen t1  in
                  uu____16010.FStar_Parser_AST.tm  in
                (match uu____16009 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16014);
                               FStar_Parser_AST.range = uu____16015;
                               FStar_Parser_AST.level = uu____16016;_},uu____16017)::uu____16018::[])
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
                               FStar_Parser_AST.range = uu____16067;
                               FStar_Parser_AST.level = uu____16068;_},uu____16069)::uu____16070::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16103 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16138 = head_and_args t1  in
            match uu____16138 with
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
                     let thunk_ens uu____16231 =
                       match uu____16231 with
                       | (e,i) ->
                           let uu____16242 = FStar_Parser_AST.thunk e  in
                           (uu____16242, i)
                        in
                     let fail_lemma uu____16254 =
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
                           let uu____16360 =
                             let uu____16367 =
                               let uu____16374 = thunk_ens ens  in
                               [uu____16374; nil_pat]  in
                             req_true :: uu____16367  in
                           unit_tm :: uu____16360
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____16421 =
                             let uu____16428 =
                               let uu____16435 = thunk_ens ens  in
                               [uu____16435; nil_pat]  in
                             req :: uu____16428  in
                           unit_tm :: uu____16421
                       | ens::smtpat::[] when
                           (((let uu____16484 = is_requires ens  in
                              Prims.op_Negation uu____16484) &&
                               (let uu____16487 = is_smt_pat ens  in
                                Prims.op_Negation uu____16487))
                              &&
                              (let uu____16490 = is_decreases ens  in
                               Prims.op_Negation uu____16490))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____16492 =
                             let uu____16499 =
                               let uu____16506 = thunk_ens ens  in
                               [uu____16506; smtpat]  in
                             req_true :: uu____16499  in
                           unit_tm :: uu____16492
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____16553 =
                             let uu____16560 =
                               let uu____16567 = thunk_ens ens  in
                               [uu____16567; nil_pat; dec]  in
                             req_true :: uu____16560  in
                           unit_tm :: uu____16553
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16627 =
                             let uu____16634 =
                               let uu____16641 = thunk_ens ens  in
                               [uu____16641; smtpat; dec]  in
                             req_true :: uu____16634  in
                           unit_tm :: uu____16627
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____16701 =
                             let uu____16708 =
                               let uu____16715 = thunk_ens ens  in
                               [uu____16715; nil_pat; dec]  in
                             req :: uu____16708  in
                           unit_tm :: uu____16701
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____16775 =
                             let uu____16782 =
                               let uu____16789 = thunk_ens ens  in
                               [uu____16789; smtpat]  in
                             req :: uu____16782  in
                           unit_tm :: uu____16775
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____16854 =
                             let uu____16861 =
                               let uu____16868 = thunk_ens ens  in
                               [uu____16868; dec; smtpat]  in
                             req :: uu____16861  in
                           unit_tm :: uu____16854
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____16930 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____16930, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16958 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16958
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____16961 =
                       let uu____16968 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16968, [])  in
                     (uu____16961, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____16986 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____16986
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____16989 =
                       let uu____16996 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____16996, [])  in
                     (uu____16989, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17018 =
                       let uu____17025 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17025, [])  in
                     (uu____17018, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17048 when allow_type_promotion ->
                     let default_effect =
                       let uu____17050 = FStar_Options.ml_ish ()  in
                       if uu____17050
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17056 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17056
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17063 =
                       let uu____17070 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17070, [])  in
                     (uu____17063, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17093 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17112 = pre_process_comp_typ t  in
          match uu____17112 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17164 =
                    let uu____17170 =
                      let uu____17172 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17172
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17170)
                     in
                  fail1 uu____17164)
               else ();
               (let is_universe uu____17188 =
                  match uu____17188 with
                  | (uu____17194,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17196 = FStar_Util.take is_universe args  in
                match uu____17196 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17255  ->
                           match uu____17255 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17262 =
                      let uu____17277 = FStar_List.hd args1  in
                      let uu____17286 = FStar_List.tl args1  in
                      (uu____17277, uu____17286)  in
                    (match uu____17262 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17341 =
                           let is_decrease uu____17380 =
                             match uu____17380 with
                             | (t1,uu____17391) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____17402;
                                         FStar_Syntax_Syntax.vars =
                                           uu____17403;_},uu____17404::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____17443 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17341 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____17560  ->
                                        match uu____17560 with
                                        | (t1,uu____17570) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____17579,(arg,uu____17581)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____17620 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____17641 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____17653 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____17653
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____17660 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____17660
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____17670 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17670
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____17677 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____17677
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____17684 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____17684
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____17691 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____17691
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____17712 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____17712
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
                                                    let uu____17803 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____17803
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
                                              | uu____17824 -> pat  in
                                            let uu____17825 =
                                              let uu____17836 =
                                                let uu____17847 =
                                                  let uu____17856 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____17856, aq)  in
                                                [uu____17847]  in
                                              ens :: uu____17836  in
                                            req :: uu____17825
                                        | uu____17897 -> rest2
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
        | uu____17929 -> FStar_Pervasives_Native.None  in
      let mk1 t =
        FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None
          f.FStar_Parser_AST.range
         in
      let setpos t =
        let uu___2397_17951 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2397_17951.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2397_17951.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2404_18005 = b  in
             {
               FStar_Parser_AST.b = (uu___2404_18005.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2404_18005.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2404_18005.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18034 body1 =
          match uu____18034 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18080::uu____18081) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18099 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2423_18126 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2423_18126.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2423_18126.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18189 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18189))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18220 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18220 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2436_18230 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2436_18230.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2436_18230.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18236 =
                     let uu____18239 =
                       let uu____18240 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18240]  in
                     no_annot_abs uu____18239 body2  in
                   FStar_All.pipe_left setpos uu____18236  in
                 let uu____18261 =
                   let uu____18262 =
                     let uu____18279 =
                       let uu____18282 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18282
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____18284 =
                       let uu____18295 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18295]  in
                     (uu____18279, uu____18284)  in
                   FStar_Syntax_Syntax.Tm_app uu____18262  in
                 FStar_All.pipe_left mk1 uu____18261)
        | uu____18334 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____18399 = q (rest, pats, body)  in
              let uu____18402 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____18399 uu____18402
                FStar_Parser_AST.Formula
               in
            let uu____18403 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____18403 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____18414 -> failwith "impossible"  in
      let uu____18418 =
        let uu____18419 = unparen f  in uu____18419.FStar_Parser_AST.tm  in
      match uu____18418 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____18432,uu____18433) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____18457,uu____18458) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18514 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____18514
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____18558 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____18558
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____18622 -> desugar_term env f

and (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____18627 =
        FStar_List.fold_left
          (fun uu____18660  ->
             fun b  ->
               match uu____18660 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2515_18704 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2515_18704.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2515_18704.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2515_18704.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____18719 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____18719 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2525_18737 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2525_18737.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2525_18737.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____18738 =
                               let uu____18745 =
                                 let uu____18750 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____18750)  in
                               uu____18745 :: out  in
                             (env2, uu____18738))
                    | uu____18761 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____18627 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))

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
          let uu____18834 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18834)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____18839 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____18839)
      | FStar_Parser_AST.TVariable x ->
          let uu____18843 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____18843)
      | FStar_Parser_AST.NoName t ->
          let uu____18847 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____18847)
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
      fun uu___12_18855  ->
        match uu___12_18855 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____18877 = FStar_Syntax_Syntax.null_binder k  in
            (uu____18877, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18894 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18894 with
             | (env1,a1) ->
                 let uu____18911 =
                   let uu____18918 = trans_aqual env1 imp  in
                   ((let uu___2559_18924 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2559_18924.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2559_18924.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____18918)
                    in
                 (uu____18911, env1))

and (trans_aqual :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___13_18932  ->
      match uu___13_18932 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____18936 =
            let uu____18937 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____18937  in
          FStar_Pervasives_Native.Some uu____18936
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____18953) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____18955) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____18958 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____18976 = binder_ident b  in
         FStar_Common.list_of_option uu____18976) bs
  
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
               (fun uu___14_19013  ->
                  match uu___14_19013 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19018 -> false))
           in
        let quals2 q =
          let uu____19032 =
            (let uu____19036 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19036) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19032
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19053 = FStar_Ident.range_of_lid disc_name  in
                let uu____19054 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19053;
                  FStar_Syntax_Syntax.sigquals = uu____19054;
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
            let uu____19094 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19132  ->
                        match uu____19132 with
                        | (x,uu____19143) ->
                            let uu____19148 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19148 with
                             | (field_name,uu____19156) ->
                                 let only_decl =
                                   ((let uu____19161 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19161)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19163 =
                                        let uu____19165 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19165.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19163)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19183 =
                                       FStar_List.filter
                                         (fun uu___15_19187  ->
                                            match uu___15_19187 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19190 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19183
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___16_19205  ->
                                             match uu___16_19205 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19210 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19213 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19213;
                                     FStar_Syntax_Syntax.sigquals = quals1;
                                     FStar_Syntax_Syntax.sigmeta =
                                       FStar_Syntax_Syntax.default_sigmeta;
                                     FStar_Syntax_Syntax.sigattrs = []
                                   }  in
                                 if only_decl
                                 then [decl]
                                 else
                                   (let dd =
                                      let uu____19220 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19220
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one
                                       in
                                    let lb =
                                      let uu____19231 =
                                        let uu____19236 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19236  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19231;
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
                                      let uu____19240 =
                                        let uu____19241 =
                                          let uu____19248 =
                                            let uu____19251 =
                                              let uu____19252 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19252
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19251]  in
                                          ((false, [lb]), uu____19248)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19241
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19240;
                                        FStar_Syntax_Syntax.sigrng = p;
                                        FStar_Syntax_Syntax.sigquals = quals1;
                                        FStar_Syntax_Syntax.sigmeta =
                                          FStar_Syntax_Syntax.default_sigmeta;
                                        FStar_Syntax_Syntax.sigattrs = []
                                      }  in
                                    if no_decl then [impl] else [decl; impl]))))
               in
            FStar_All.pipe_right uu____19094 FStar_List.flatten
  
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
            (lid,uu____19301,t,uu____19303,n1,uu____19305) when
            let uu____19312 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____19312 ->
            let uu____19314 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____19314 with
             | (formals,uu____19332) ->
                 (match formals with
                  | [] -> []
                  | uu____19361 ->
                      let filter_records uu___17_19377 =
                        match uu___17_19377 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____19380,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____19392 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____19394 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____19394 with
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
                      let uu____19406 = FStar_Util.first_N n1 formals  in
                      (match uu____19406 with
                       | (uu____19435,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____19469 -> []
  
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
                    let uu____19548 =
                      FStar_All.pipe_right quals
                        (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                       in
                    if uu____19548
                    then
                      let uu____19554 =
                        FStar_Syntax_Util.incr_delta_qualifier t  in
                      FStar_Syntax_Syntax.Delta_abstract uu____19554
                    else FStar_Syntax_Util.incr_delta_qualifier t  in
                  let lb =
                    let uu____19558 =
                      let uu____19563 =
                        FStar_Syntax_Syntax.lid_as_fv lid dd
                          FStar_Pervasives_Native.None
                         in
                      FStar_Util.Inr uu____19563  in
                    let uu____19564 =
                      if FStar_Util.is_some kopt
                      then
                        let uu____19570 =
                          let uu____19573 =
                            FStar_All.pipe_right kopt FStar_Util.must  in
                          FStar_Syntax_Syntax.mk_Total uu____19573  in
                        FStar_Syntax_Util.arrow typars uu____19570
                      else FStar_Syntax_Syntax.tun  in
                    let uu____19578 = no_annot_abs typars t  in
                    {
                      FStar_Syntax_Syntax.lbname = uu____19558;
                      FStar_Syntax_Syntax.lbunivs = uvs;
                      FStar_Syntax_Syntax.lbtyp = uu____19564;
                      FStar_Syntax_Syntax.lbeff =
                        FStar_Parser_Const.effect_Tot_lid;
                      FStar_Syntax_Syntax.lbdef = uu____19578;
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
          let tycon_id uu___18_19632 =
            match uu___18_19632 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____19634,uu____19635) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____19645,uu____19646,uu____19647) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____19657,uu____19658,uu____19659) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____19689,uu____19690,uu____19691) -> id1
             in
          let binder_to_term b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____19737) ->
                let uu____19738 =
                  let uu____19739 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19739  in
                FStar_Parser_AST.mk_term uu____19738 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____19741 =
                  let uu____19742 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____19742  in
                FStar_Parser_AST.mk_term uu____19741 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____19744) ->
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
              | uu____19775 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____19783 =
                     let uu____19784 =
                       let uu____19791 = binder_to_term b  in
                       (out, uu____19791, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____19784  in
                   FStar_Parser_AST.mk_term uu____19783
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___19_19803 =
            match uu___19_19803 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____19860  ->
                       match uu____19860 with
                       | (x,t,uu____19871) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____19877 =
                    let uu____19878 =
                      let uu____19879 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____19879  in
                    FStar_Parser_AST.mk_term uu____19878
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____19877 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____19886 = binder_idents parms  in id1 ::
                    uu____19886
                   in
                (FStar_List.iter
                   (fun uu____19904  ->
                      match uu____19904 with
                      | (f,uu____19914,uu____19915) ->
                          let uu____19920 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____19920
                          then
                            let uu____19925 =
                              let uu____19931 =
                                let uu____19933 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____19933
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____19931)
                               in
                            FStar_Errors.raise_error uu____19925
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____19939 =
                    FStar_All.pipe_right fields
                      (FStar_List.map
                         (fun uu____19966  ->
                            match uu____19966 with
                            | (x,uu____19976,uu____19977) -> x))
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp),
                           FStar_Pervasives_Native.None, false)])),
                    uu____19939)))
            | uu____20035 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___20_20075 =
            match uu___20_20075 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20099 = typars_of_binders _env binders  in
                (match uu____20099 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20135 =
                         let uu____20136 =
                           let uu____20137 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20137  in
                         FStar_Parser_AST.mk_term uu____20136
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20135 binders  in
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
            | uu____20148 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20191 =
              FStar_List.fold_left
                (fun uu____20225  ->
                   fun uu____20226  ->
                     match (uu____20225, uu____20226) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20295 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20295 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20191 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____20386 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____20386
                | uu____20387 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____20395 = desugar_abstract_tc quals env [] tc  in
              (match uu____20395 with
               | (uu____20408,uu____20409,se,uu____20411) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____20414,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____20433 =
                                 let uu____20435 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____20435  in
                               if uu____20433
                               then
                                 let uu____20438 =
                                   let uu____20444 =
                                     let uu____20446 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____20446
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____20444)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____20438
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
                           | uu____20459 ->
                               let uu____20460 =
                                 let uu____20467 =
                                   let uu____20468 =
                                     let uu____20483 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____20483)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____20468
                                    in
                                 FStar_Syntax_Syntax.mk uu____20467  in
                               uu____20460 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2834_20496 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2834_20496.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2834_20496.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2834_20496.FStar_Syntax_Syntax.sigattrs)
                         }
                     | uu____20497 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   let env2 =
                     let uu____20501 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     FStar_Syntax_DsEnv.push_doc env1 uu____20501
                       d.FStar_Parser_AST.doc
                      in
                   (env2, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____20514 = typars_of_binders env binders  in
              (match uu____20514 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____20548 =
                           FStar_Util.for_some
                             (fun uu___21_20551  ->
                                match uu___21_20551 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____20554 -> false) quals
                            in
                         if uu____20548
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____20562 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____20562
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____20567 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___22_20573  ->
                               match uu___22_20573 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____20576 -> false))
                        in
                     if uu____20567
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____20590 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____20590
                     then
                       let uu____20596 =
                         let uu____20603 =
                           let uu____20604 = unparen t  in
                           uu____20604.FStar_Parser_AST.tm  in
                         match uu____20603 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____20625 =
                               match FStar_List.rev args with
                               | (last_arg,uu____20655)::args_rev ->
                                   let uu____20667 =
                                     let uu____20668 = unparen last_arg  in
                                     uu____20668.FStar_Parser_AST.tm  in
                                   (match uu____20667 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____20696 -> ([], args))
                               | uu____20705 -> ([], args)  in
                             (match uu____20625 with
                              | (cattributes,args1) ->
                                  let uu____20744 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____20744))
                         | uu____20755 -> (t, [])  in
                       match uu____20596 with
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
                                  (fun uu___23_20778  ->
                                     match uu___23_20778 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____20781 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____20790)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____20814 = tycon_record_as_variant trec  in
              (match uu____20814 with
               | (t,fs) ->
                   let uu____20831 =
                     let uu____20834 =
                       let uu____20835 =
                         let uu____20844 =
                           let uu____20847 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____20847  in
                         (uu____20844, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____20835  in
                     uu____20834 :: quals  in
                   desugar_tycon env d uu____20831 [t])
          | uu____20852::uu____20853 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21023 = et  in
                match uu____21023 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21253 ->
                         let trec = tc  in
                         let uu____21277 = tycon_record_as_variant trec  in
                         (match uu____21277 with
                          | (t,fs) ->
                              let uu____21337 =
                                let uu____21340 =
                                  let uu____21341 =
                                    let uu____21350 =
                                      let uu____21353 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21353  in
                                    (uu____21350, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21341
                                   in
                                uu____21340 :: quals1  in
                              collect_tcs uu____21337 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____21443 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21443 with
                          | (env2,uu____21504,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____21657 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____21657 with
                          | (env2,uu____21718,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____21846 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____21896 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____21896 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let docs_tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___25_22411  ->
                             match uu___25_22411 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22477,uu____22478);
                                    FStar_Syntax_Syntax.sigrng = uu____22479;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22480;
                                    FStar_Syntax_Syntax.sigmeta = uu____22481;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22482;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____22546 =
                                     typars_of_binders env1 binders  in
                                   match uu____22546 with
                                   | (env2,tpars1) ->
                                       let uu____22573 =
                                         push_tparams env2 tpars1  in
                                       (match uu____22573 with
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
                                 let uu____22602 =
                                   let uu____22621 =
                                     mk_typ_abbrev id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ((id1, (d.FStar_Parser_AST.doc)), [],
                                     uu____22621)
                                    in
                                 [uu____22602]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____22681);
                                    FStar_Syntax_Syntax.sigrng = uu____22682;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____22684;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22685;_},constrs,tconstr,quals1)
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
                                 let uu____22786 = push_tparams env1 tpars
                                    in
                                 (match uu____22786 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____22853  ->
                                             match uu____22853 with
                                             | (x,uu____22865) ->
                                                 (x,
                                                   (FStar_Pervasives_Native.Some
                                                      (FStar_Syntax_Syntax.Implicit
                                                         true)))) tps
                                         in
                                      let tot_tconstr = mk_tot tconstr  in
                                      let uu____22870 =
                                        let uu____22897 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23007  ->
                                                  match uu____23007 with
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
                                                        let uu____23067 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23067
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
                                                                uu___24_23078
                                                                 ->
                                                                match uu___24_23078
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23090
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23098 =
                                                        let uu____23117 =
                                                          let uu____23118 =
                                                            let uu____23119 =
                                                              let uu____23135
                                                                =
                                                                let uu____23136
                                                                  =
                                                                  let uu____23139
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23139
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23136
                                                                 in
                                                              (name, univs1,
                                                                uu____23135,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23119
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23118;
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
                                                          uu____23117)
                                                         in
                                                      (name, uu____23098)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____22897
                                         in
                                      (match uu____22870 with
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
                             | uu____23351 -> failwith "impossible"))
                      in
                   let name_docs =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23479  ->
                             match uu____23479 with
                             | (name_doc,uu____23505,uu____23506) -> name_doc))
                      in
                   let sigelts =
                     FStar_All.pipe_right docs_tps_sigelts
                       (FStar_List.map
                          (fun uu____23578  ->
                             match uu____23578 with
                             | (uu____23597,uu____23598,se) -> se))
                      in
                   let uu____23624 =
                     let uu____23631 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23631 rng
                      in
                   (match uu____23624 with
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
                               (fun uu____23693  ->
                                  match uu____23693 with
                                  | (uu____23714,tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23762,tps,k,uu____23765,constrs)
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
                                      let uu____23786 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23801 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23818,uu____23819,uu____23820,uu____23821,uu____23822)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23829
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23801
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23833 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___26_23840  ->
                                                          match uu___26_23840
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23842 ->
                                                              true
                                                          | uu____23852 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23833))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23786
                                  | uu____23854 -> []))
                           in
                        let ops = FStar_List.append discs data_ops  in
                        let env4 =
                          FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt
                            env3 ops
                           in
                        let env5 =
                          FStar_List.fold_left
                            (fun acc  ->
                               fun uu____23871  ->
                                 match uu____23871 with
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
      let uu____23916 =
        FStar_List.fold_left
          (fun uu____23951  ->
             fun b  ->
               match uu____23951 with
               | (env1,binders1) ->
                   let uu____23995 = desugar_binder env1 b  in
                   (match uu____23995 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24018 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24018 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24071 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____23916 with
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
          let uu____24175 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___27_24182  ->
                    match uu___27_24182 with
                    | FStar_Syntax_Syntax.Reflectable uu____24184 -> true
                    | uu____24186 -> false))
             in
          if uu____24175
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24191 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24191
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
        let warn1 uu____24242 =
          if warn
          then
            let uu____24244 =
              let uu____24250 =
                let uu____24252 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24252
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24250)  in
            FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos uu____24244
          else ()  in
        let uu____24258 = FStar_Syntax_Util.head_and_args at1  in
        match uu____24258 with
        | (hd1,args) ->
            let uu____24311 =
              let uu____24312 = FStar_Syntax_Subst.compress hd1  in
              uu____24312.FStar_Syntax_Syntax.n  in
            (match uu____24311 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24356)::[] ->
                      let uu____24381 =
                        let uu____24386 =
                          let uu____24395 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24395 a1  in
                        uu____24386 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24381 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24418 =
                             let uu____24424 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24424  in
                           (uu____24418, true)
                       | uu____24439 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24455 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24477 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24594 =
        parse_attr_with_list warn at1 FStar_Parser_Const.fail_attr  in
      match uu____24594 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24643 =
               parse_attr_with_list warn at1 FStar_Parser_Const.fail_lax_attr
                in
             match uu____24643 with | (res1,uu____24665) -> rebind res1 true)
  
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
                  let uu____24830 = desugar_binders monad_env eff_binders  in
                  match uu____24830 with
                  | (env1,binders) ->
                      let eff_t = desugar_term env1 eff_typ  in
                      let mandatory_members =
                        let rr_members =
                          ["repr";
                          "return";
                          "bind";
                          "wp_type";
                          "interp";
                          "mrelation"]  in
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
                            (uu____24913,uu____24914,(FStar_Parser_AST.TyconAbbrev
                                                      (name,uu____24916,uu____24917,uu____24918),uu____24919)::[])
                            -> FStar_Ident.text_of_id name
                        | uu____24956 ->
                            failwith "Malformed effect member declaration."
                         in
                      let uu____24959 =
                        FStar_List.partition
                          (fun decl  ->
                             let uu____24971 = name_of_eff_decl decl  in
                             FStar_List.mem uu____24971 mandatory_members)
                          eff_decls
                         in
                      (match uu____24959 with
                       | (mandatory_members_decls,actions) ->
                           let uu____24990 =
                             FStar_All.pipe_right mandatory_members_decls
                               (FStar_List.fold_left
                                  (fun uu____25019  ->
                                     fun decl  ->
                                       match uu____25019 with
                                       | (env2,out) ->
                                           let uu____25039 =
                                             desugar_decl env2 decl  in
                                           (match uu____25039 with
                                            | (env3,ses) ->
                                                let uu____25052 =
                                                  let uu____25055 =
                                                    FStar_List.hd ses  in
                                                  uu____25055 :: out  in
                                                (env3, uu____25052)))
                                  (env1, []))
                              in
                           (match uu____24990 with
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
                                              (uu____25118,uu____25119,
                                               (FStar_Parser_AST.TyconAbbrev
                                                (name,action_params,uu____25122,defn),doc1)::[])
                                              ->
                                              let uu____25161 =
                                                desugar_binders env2
                                                  action_params
                                                 in
                                              (match uu____25161 with
                                               | (env3,action_params1) ->
                                                   let action_params2 =
                                                     FStar_Syntax_Subst.close_binders
                                                       action_params1
                                                      in
                                                   let uu____25199 =
                                                     let uu____25200 =
                                                       FStar_Syntax_DsEnv.qualify
                                                         env3 name
                                                        in
                                                     let uu____25201 =
                                                       let uu____25202 =
                                                         desugar_term env3
                                                           defn
                                                          in
                                                       FStar_Syntax_Subst.close
                                                         (FStar_List.append
                                                            binders1
                                                            action_params2)
                                                         uu____25202
                                                        in
                                                     {
                                                       FStar_Syntax_Syntax.action_name
                                                         = uu____25200;
                                                       FStar_Syntax_Syntax.action_unqualified_name
                                                         = name;
                                                       FStar_Syntax_Syntax.action_univs
                                                         = [];
                                                       FStar_Syntax_Syntax.action_params
                                                         = action_params2;
                                                       FStar_Syntax_Syntax.action_defn
                                                         = uu____25201;
                                                       FStar_Syntax_Syntax.action_typ
                                                         =
                                                         FStar_Syntax_Syntax.tun
                                                     }  in
                                                   (uu____25199, doc1))
                                          | uu____25211 ->
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
                                let lookup_or_dummy s =
                                  let l =
                                    let uu____25249 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____25249
                                     in
                                  let t =
                                    let uu____25254 =
                                      FStar_Syntax_DsEnv.try_lookup_definition
                                        env2 l
                                       in
                                    match uu____25254 with
                                    | FStar_Pervasives_Native.None  ->
                                        FStar_Syntax_Syntax.mk
                                          FStar_Syntax_Syntax.Tm_unknown
                                          FStar_Pervasives_Native.None
                                          FStar_Range.dummyRange
                                    | FStar_Pervasives_Native.Some t ->
                                        FStar_Syntax_Subst.close binders1 t
                                     in
                                  ([], t)  in
                                let lookup_or_none s =
                                  let l =
                                    let uu____25281 =
                                      FStar_Ident.mk_ident
                                        (s, (d.FStar_Parser_AST.drange))
                                       in
                                    FStar_Syntax_DsEnv.qualify env2
                                      uu____25281
                                     in
                                  let uu____25283 =
                                    FStar_Syntax_DsEnv.try_lookup_definition
                                      env2 l
                                     in
                                  match uu____25283 with
                                  | FStar_Pervasives_Native.None  ->
                                      FStar_Pervasives_Native.None
                                  | FStar_Pervasives_Native.Some t ->
                                      let uu____25301 =
                                        let uu____25308 =
                                          FStar_Syntax_Subst.close binders1 t
                                           in
                                        ([], uu____25308)  in
                                      FStar_Pervasives_Native.Some
                                        uu____25301
                                   in
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
                                  let rr =
                                    FStar_Util.for_some
                                      (fun uu___28_25325  ->
                                         match uu___28_25325 with
                                         | FStar_Syntax_Syntax.Reifiable  ->
                                             true
                                         | FStar_Syntax_Syntax.Reflectable
                                             uu____25328 -> true
                                         | uu____25330 -> false) qualifiers
                                     in
                                  let uu____25332 =
                                    let uu____25333 =
                                      let uu____25334 =
                                        let uu____25335 =
                                          let uu____25336 =
                                            lookup_or_dummy "wp_type"  in
                                          FStar_All.pipe_left
                                            FStar_Pervasives_Native.snd
                                            uu____25336
                                           in
                                        let uu____25358 =
                                          lookup_or_dummy "return_wp"  in
                                        let uu____25360 =
                                          lookup_or_dummy "bind_wp"  in
                                        {
                                          FStar_Syntax_Syntax.monad_m =
                                            uu____25335;
                                          FStar_Syntax_Syntax.monad_ret =
                                            uu____25358;
                                          FStar_Syntax_Syntax.monad_bind =
                                            uu____25360
                                        }  in
                                      let uu____25362 =
                                        lookup_or_dummy "if_then_else"  in
                                      let uu____25364 =
                                        lookup_or_dummy "ite_wp"  in
                                      let uu____25366 =
                                        lookup_or_dummy "stronger"  in
                                      let uu____25368 =
                                        lookup_or_dummy "close_wp"  in
                                      let uu____25370 =
                                        lookup_or_dummy "trivial"  in
                                      let uu____25372 =
                                        let uu____25373 =
                                          let uu____25374 =
                                            lookup_or_dummy "repr"  in
                                          FStar_All.pipe_left
                                            FStar_Pervasives_Native.snd
                                            uu____25374
                                           in
                                        let uu____25396 =
                                          lookup_or_dummy "return"  in
                                        let uu____25398 =
                                          lookup_or_dummy "bind"  in
                                        {
                                          FStar_Syntax_Syntax.monad_m =
                                            uu____25373;
                                          FStar_Syntax_Syntax.monad_ret =
                                            uu____25396;
                                          FStar_Syntax_Syntax.monad_bind =
                                            uu____25398
                                        }  in
                                      let uu____25400 =
                                        lookup_or_none "interp"  in
                                      let uu____25404 =
                                        lookup_or_none "mrelation"  in
                                      let uu____25408 =
                                        FStar_List.map (desugar_term env2)
                                          attrs
                                         in
                                      {
                                        FStar_Syntax_Syntax.cattributes = [];
                                        FStar_Syntax_Syntax.mname = mname;
                                        FStar_Syntax_Syntax.univs = [];
                                        FStar_Syntax_Syntax.binders =
                                          binders1;
                                        FStar_Syntax_Syntax.spec =
                                          uu____25334;
                                        FStar_Syntax_Syntax.signature =
                                          eff_t1;
                                        FStar_Syntax_Syntax.if_then_else =
                                          uu____25362;
                                        FStar_Syntax_Syntax.ite_wp =
                                          uu____25364;
                                        FStar_Syntax_Syntax.stronger =
                                          uu____25366;
                                        FStar_Syntax_Syntax.close_wp =
                                          uu____25368;
                                        FStar_Syntax_Syntax.trivial =
                                          uu____25370;
                                        FStar_Syntax_Syntax.repr =
                                          uu____25372;
                                        FStar_Syntax_Syntax.elaborated =
                                          false;
                                        FStar_Syntax_Syntax.spec_dm4f = false;
                                        FStar_Syntax_Syntax.interp =
                                          uu____25400;
                                        FStar_Syntax_Syntax.mrelation =
                                          uu____25404;
                                        FStar_Syntax_Syntax.actions =
                                          actions1;
                                        FStar_Syntax_Syntax.eff_attrs =
                                          uu____25408
                                      }  in
                                    FStar_Syntax_Syntax.Sig_new_effect
                                      uu____25333
                                     in
                                  {
                                    FStar_Syntax_Syntax.sigel = uu____25332;
                                    FStar_Syntax_Syntax.sigrng =
                                      (d.FStar_Parser_AST.drange);
                                    FStar_Syntax_Syntax.sigquals = qualifiers;
                                    FStar_Syntax_Syntax.sigmeta =
                                      FStar_Syntax_Syntax.default_sigmeta;
                                    FStar_Syntax_Syntax.sigattrs = []
                                  }  in
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
                                          fun uu____25436  ->
                                            match uu____25436 with
                                            | (a,doc1) ->
                                                let env6 =
                                                  let uu____25450 =
                                                    FStar_Syntax_Util.action_as_lb
                                                      mname a
                                                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                     in
                                                  FStar_Syntax_DsEnv.push_sigelt
                                                    env5 uu____25450
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
                let uu____25474 = desugar_binders env1 eff_binders  in
                match uu____25474 with
                | (env2,binders) ->
                    let uu____25511 =
                      let uu____25522 = head_and_args defn  in
                      match uu____25522 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25559 ->
                                let uu____25560 =
                                  let uu____25566 =
                                    let uu____25568 =
                                      let uu____25570 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25570 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25568  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25566)
                                   in
                                FStar_Errors.raise_error uu____25560
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25576 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25606)::args_rev ->
                                let uu____25618 =
                                  let uu____25619 = unparen last_arg  in
                                  uu____25619.FStar_Parser_AST.tm  in
                                (match uu____25618 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25647 -> ([], args))
                            | uu____25656 -> ([], args)  in
                          (match uu____25576 with
                           | (cattributes,args1) ->
                               let uu____25699 = desugar_args env2 args1  in
                               let uu____25700 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25699, uu____25700))
                       in
                    (match uu____25511 with
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
                          (let uu____25740 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25740 with
                           | (ed_binders,uu____25754,ed_binders_opening) ->
                               let sub' shift_n uu____25773 =
                                 match uu____25773 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25788 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25788 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25792 =
                                       let uu____25793 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25793)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25792
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25814 =
                                   let uu____25815 =
                                     let uu____25816 =
                                       sub1
                                         ([],
                                           ((ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m))
                                        in
                                     FStar_Pervasives_Native.snd uu____25816
                                      in
                                   let uu____25831 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                                      in
                                   let uu____25832 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                                      in
                                   {
                                     FStar_Syntax_Syntax.monad_m =
                                       uu____25815;
                                     FStar_Syntax_Syntax.monad_ret =
                                       uu____25831;
                                     FStar_Syntax_Syntax.monad_bind =
                                       uu____25832
                                   }  in
                                 let uu____25833 =
                                   let uu____25834 =
                                     sub1
                                       ([],
                                         (ed.FStar_Syntax_Syntax.signature))
                                      in
                                   FStar_Pervasives_Native.snd uu____25834
                                    in
                                 let uu____25849 =
                                   sub1 ed.FStar_Syntax_Syntax.if_then_else
                                    in
                                 let uu____25850 =
                                   sub1 ed.FStar_Syntax_Syntax.ite_wp  in
                                 let uu____25851 =
                                   sub1 ed.FStar_Syntax_Syntax.stronger  in
                                 let uu____25852 =
                                   sub1 ed.FStar_Syntax_Syntax.close_wp  in
                                 let uu____25853 =
                                   sub1 ed.FStar_Syntax_Syntax.trivial  in
                                 let uu____25854 =
                                   let uu____25855 =
                                     let uu____25856 =
                                       sub1
                                         ([],
                                           ((ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m))
                                        in
                                     FStar_Pervasives_Native.snd uu____25856
                                      in
                                   let uu____25871 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                                      in
                                   let uu____25872 =
                                     sub1
                                       (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                                      in
                                   {
                                     FStar_Syntax_Syntax.monad_m =
                                       uu____25855;
                                     FStar_Syntax_Syntax.monad_ret =
                                       uu____25871;
                                     FStar_Syntax_Syntax.monad_bind =
                                       uu____25872
                                   }  in
                                 let uu____25873 =
                                   FStar_Util.map_opt
                                     ed.FStar_Syntax_Syntax.interp sub1
                                    in
                                 let uu____25876 =
                                   FStar_Util.map_opt
                                     ed.FStar_Syntax_Syntax.mrelation sub1
                                    in
                                 let uu____25879 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____25895 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____25896 =
                                          let uu____25897 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25897
                                           in
                                        let uu____25912 =
                                          let uu____25913 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____25913
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____25895;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____25896;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____25912
                                        }) ed.FStar_Syntax_Syntax.actions
                                    in
                                 {
                                   FStar_Syntax_Syntax.cattributes =
                                     cattributes;
                                   FStar_Syntax_Syntax.mname = mname;
                                   FStar_Syntax_Syntax.univs =
                                     (ed.FStar_Syntax_Syntax.univs);
                                   FStar_Syntax_Syntax.binders = binders1;
                                   FStar_Syntax_Syntax.spec = uu____25814;
                                   FStar_Syntax_Syntax.signature =
                                     uu____25833;
                                   FStar_Syntax_Syntax.if_then_else =
                                     uu____25849;
                                   FStar_Syntax_Syntax.ite_wp = uu____25850;
                                   FStar_Syntax_Syntax.stronger = uu____25851;
                                   FStar_Syntax_Syntax.close_wp = uu____25852;
                                   FStar_Syntax_Syntax.trivial = uu____25853;
                                   FStar_Syntax_Syntax.repr = uu____25854;
                                   FStar_Syntax_Syntax.elaborated =
                                     (ed.FStar_Syntax_Syntax.elaborated);
                                   FStar_Syntax_Syntax.spec_dm4f =
                                     (ed.FStar_Syntax_Syntax.spec_dm4f);
                                   FStar_Syntax_Syntax.interp = uu____25873;
                                   FStar_Syntax_Syntax.mrelation =
                                     uu____25876;
                                   FStar_Syntax_Syntax.actions = uu____25879;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____25929 =
                                   let uu____25932 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____25932 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____25929;
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
                                             let uu____25953 =
                                               FStar_Syntax_Util.action_as_lb
                                                 mname a
                                                 (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                in
                                             FStar_Syntax_DsEnv.push_sigelt
                                               env5 uu____25953
                                              in
                                           FStar_Syntax_DsEnv.push_doc env6
                                             a.FStar_Syntax_Syntax.action_name
                                             doc1) env4)
                                  in
                               let env6 =
                                 let uu____25955 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____25955
                                 then
                                   let reflect_lid =
                                     let uu____25962 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____25962
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
    let uu____25974 =
      match d.FStar_Parser_AST.doc with
      | FStar_Pervasives_Native.None  -> ("", [])
      | FStar_Pervasives_Native.Some fsdoc -> fsdoc  in
    match uu____25974 with
    | (text,kv) ->
        let summary =
          match FStar_List.assoc "summary" kv with
          | FStar_Pervasives_Native.None  -> ""
          | FStar_Pervasives_Native.Some s ->
              Prims.op_Hat "  " (Prims.op_Hat s "\n")
           in
        let pp =
          match FStar_List.assoc "type" kv with
          | FStar_Pervasives_Native.Some uu____26061 ->
              let uu____26064 =
                let uu____26066 =
                  FStar_Parser_ToDocument.signature_to_document d  in
                FStar_Pprint.pretty_string 0.95 (Prims.of_int (80))
                  uu____26066
                 in
              Prims.op_Hat "\n  " uu____26064
          | uu____26069 -> ""  in
        let other =
          FStar_List.filter_map
            (fun uu____26088  ->
               match uu____26088 with
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
          let uu____26133 = FStar_Ident.lid_of_str "FStar.Pervasives.Comment"
             in
          FStar_Syntax_Syntax.fvar uu____26133
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        if str = ""
        then []
        else
          (let uu____26146 =
             let arg = FStar_Syntax_Util.exp_string str  in
             let uu____26150 =
               let uu____26161 = FStar_Syntax_Syntax.as_arg arg  in
               [uu____26161]  in
             FStar_Syntax_Util.mk_app fv uu____26150  in
           [uu____26146])

and (desugar_decl_aux :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts))
  =
  fun env  ->
    fun d  ->
      let env0 = env  in
      let uu____26197 = desugar_decl_noattrs env d  in
      match uu____26197 with
      | (env1,sigelts) ->
          let attrs = d.FStar_Parser_AST.attrs  in
          let attrs1 = FStar_List.map (desugar_term env1) attrs  in
          let val_attrs =
            match sigelts with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  (lbs,names1);
                FStar_Syntax_Syntax.sigrng = uu____26227;
                FStar_Syntax_Syntax.sigquals = uu____26228;
                FStar_Syntax_Syntax.sigmeta = uu____26229;
                FStar_Syntax_Syntax.sigattrs = uu____26230;_}::[] ->
                let uu____26239 =
                  FStar_All.pipe_right names1
                    (FStar_List.collect
                       (fun nm  ->
                          let uu____26249 =
                            FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                              env0 nm
                             in
                          FStar_Pervasives_Native.snd uu____26249))
                   in
                FStar_All.pipe_right uu____26239
                  (FStar_List.filter
                     (fun t  ->
                        let uu____26271 = get_fail_attr false t  in
                        FStar_Option.isNone uu____26271))
            | uu____26291 -> []  in
          let attrs2 =
            let uu____26299 = mk_comment_attr d  in
            FStar_List.append uu____26299
              (FStar_List.append attrs1 val_attrs)
             in
          let uu____26308 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = Prims.int_zero
                   then
                     let uu___3386_26318 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3386_26318.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3386_26318.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3386_26318.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3386_26318.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs2
                     }
                   else
                     (let uu___3388_26321 = sigelt  in
                      let uu____26322 =
                        FStar_List.filter
                          (fun at1  ->
                             let uu____26328 = get_fail_attr false at1  in
                             FStar_Option.isNone uu____26328) attrs2
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3388_26321.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3388_26321.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3388_26321.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3388_26321.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____26322
                      })) sigelts
             in
          (env1, uu____26308)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26354 = desugar_decl_aux env d  in
      match uu____26354 with
      | (env1,ses) ->
          let uu____26365 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26365)

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
      | FStar_Parser_AST.Fsdoc uu____26393 -> (env, [])
      | FStar_Parser_AST.TopLevelModule id1 -> (env, [])
      | FStar_Parser_AST.Open lid ->
          let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in (env1, [])
      | FStar_Parser_AST.Friend lid ->
          let uu____26398 = FStar_Syntax_DsEnv.iface env  in
          if uu____26398
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26413 =
               let uu____26415 =
                 let uu____26417 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26418 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26417
                   uu____26418
                  in
               Prims.op_Negation uu____26415  in
             if uu____26413
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26432 =
                  let uu____26434 =
                    let uu____26436 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26436 lid  in
                  Prims.op_Negation uu____26434  in
                if uu____26432
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26450 =
                     let uu____26452 =
                       let uu____26454 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26454
                         lid
                        in
                     Prims.op_Negation uu____26452  in
                   if uu____26450
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26472 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26472, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26513,uu____26514)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26553 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let tcs1 =
            FStar_List.map
              (fun uu____26580  ->
                 match uu____26580 with | (x,uu____26588) -> x) tcs
             in
          let uu____26593 =
            let uu____26598 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26598 tcs1  in
          (match uu____26593 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26615 =
                   let uu____26616 =
                     let uu____26623 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26623  in
                   [uu____26616]  in
                 let uu____26636 =
                   let uu____26639 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26642 =
                     let uu____26653 =
                       let uu____26662 =
                         let uu____26663 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26663  in
                       FStar_Syntax_Syntax.as_arg uu____26662  in
                     [uu____26653]  in
                   FStar_Syntax_Util.mk_app uu____26639 uu____26642  in
                 FStar_Syntax_Util.abs uu____26615 uu____26636
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26703,id1))::uu____26705 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26708::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26712 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26712 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26718 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26718]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26739) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26749,uu____26750,uu____26751,uu____26752,uu____26753)
                     ->
                     let uu____26762 =
                       let uu____26763 =
                         let uu____26764 =
                           let uu____26771 = mkclass lid  in
                           (meths, uu____26771)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26764  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26763;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = []
                       }  in
                     [uu____26762]
                 | uu____26774 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26808;
                    FStar_Parser_AST.prange = uu____26809;_},uu____26810)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26820;
                    FStar_Parser_AST.prange = uu____26821;_},uu____26822)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26838;
                         FStar_Parser_AST.prange = uu____26839;_},uu____26840);
                    FStar_Parser_AST.prange = uu____26841;_},uu____26842)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26864;
                         FStar_Parser_AST.prange = uu____26865;_},uu____26866);
                    FStar_Parser_AST.prange = uu____26867;_},uu____26868)::[]
                   -> false
               | (p,uu____26897)::[] ->
                   let uu____26906 = is_app_pattern p  in
                   Prims.op_Negation uu____26906
               | uu____26908 -> false)
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
            let uu____26983 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26983 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26996 =
                     let uu____26997 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26997.FStar_Syntax_Syntax.n  in
                   match uu____26996 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27007) ->
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
                                 let uu____27048 =
                                   FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                     env
                                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                    in
                                 FStar_Pervasives_Native.fst uu____27048))
                          in
                       let quals1 =
                         match quals with
                         | uu____27066::uu____27067 ->
                             FStar_List.map
                               (trans_qual1 FStar_Pervasives_Native.None)
                               quals
                         | uu____27070 -> val_quals  in
                       let quals2 =
                         let uu____27074 =
                           FStar_All.pipe_right lets1
                             (FStar_Util.for_some
                                (fun uu____27107  ->
                                   match uu____27107 with
                                   | (uu____27121,(uu____27122,t)) ->
                                       t.FStar_Parser_AST.level =
                                         FStar_Parser_AST.Formula))
                            in
                         if uu____27074
                         then FStar_Syntax_Syntax.Logic :: quals1
                         else quals1  in
                       let lbs1 =
                         let uu____27142 =
                           FStar_All.pipe_right quals2
                             (FStar_List.contains
                                FStar_Syntax_Syntax.Abstract)
                            in
                         if uu____27142
                         then
                           let uu____27148 =
                             FStar_All.pipe_right
                               (FStar_Pervasives_Native.snd lbs)
                               (FStar_List.map
                                  (fun lb  ->
                                     let fv =
                                       FStar_Util.right
                                         lb.FStar_Syntax_Syntax.lbname
                                        in
                                     let uu___3566_27163 = lb  in
                                     {
                                       FStar_Syntax_Syntax.lbname =
                                         (FStar_Util.Inr
                                            (let uu___3568_27165 = fv  in
                                             {
                                               FStar_Syntax_Syntax.fv_name =
                                                 (uu___3568_27165.FStar_Syntax_Syntax.fv_name);
                                               FStar_Syntax_Syntax.fv_delta =
                                                 (FStar_Syntax_Syntax.Delta_abstract
                                                    (fv.FStar_Syntax_Syntax.fv_delta));
                                               FStar_Syntax_Syntax.fv_qual =
                                                 (uu___3568_27165.FStar_Syntax_Syntax.fv_qual)
                                             }));
                                       FStar_Syntax_Syntax.lbunivs =
                                         (uu___3566_27163.FStar_Syntax_Syntax.lbunivs);
                                       FStar_Syntax_Syntax.lbtyp =
                                         (uu___3566_27163.FStar_Syntax_Syntax.lbtyp);
                                       FStar_Syntax_Syntax.lbeff =
                                         (uu___3566_27163.FStar_Syntax_Syntax.lbeff);
                                       FStar_Syntax_Syntax.lbdef =
                                         (uu___3566_27163.FStar_Syntax_Syntax.lbdef);
                                       FStar_Syntax_Syntax.lbattrs =
                                         (uu___3566_27163.FStar_Syntax_Syntax.lbattrs);
                                       FStar_Syntax_Syntax.lbpos =
                                         (uu___3566_27163.FStar_Syntax_Syntax.lbpos)
                                     }))
                              in
                           ((FStar_Pervasives_Native.fst lbs), uu____27148)
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
                   | uu____27192 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27200 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27219 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27200 with
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
                       let uu___3593_27256 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3593_27256.FStar_Parser_AST.prange)
                       }
                   | uu____27263 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3597_27270 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3597_27270.FStar_Parser_AST.drange);
                        FStar_Parser_AST.doc =
                          (uu___3597_27270.FStar_Parser_AST.doc);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3597_27270.FStar_Parser_AST.attrs)
                      })
                    in
                 let build_projection uu____27306 id1 =
                   match uu____27306 with
                   | (env1,ses) ->
                       let main =
                         let uu____27327 =
                           let uu____27328 =
                             FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                           FStar_Parser_AST.Var uu____27328  in
                         FStar_Parser_AST.mk_term uu____27327
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
                       let uu____27378 = desugar_decl env1 id_decl  in
                       (match uu____27378 with
                        | (env2,ses') -> (env2, (FStar_List.append ses ses')))
                    in
                 let bvs =
                   let uu____27396 = gather_pattern_bound_vars true pat  in
                   FStar_All.pipe_right uu____27396 FStar_Util.set_elements
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
            let uu____27420 = close_fun env t  in
            desugar_term env uu____27420  in
          let quals1 =
            let uu____27424 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27424
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27436 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27436;
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
                let uu____27450 =
                  let uu____27459 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27459]  in
                let uu____27478 =
                  let uu____27481 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27481
                   in
                FStar_Syntax_Util.arrow uu____27450 uu____27478
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
            let uu____27536 =
              FStar_Syntax_DsEnv.try_lookup_effect_name env l1  in
            match uu____27536 with
            | FStar_Pervasives_Native.None  ->
                let uu____27539 =
                  let uu____27545 =
                    let uu____27547 =
                      let uu____27549 = FStar_Syntax_Print.lid_to_string l1
                         in
                      Prims.op_Hat uu____27549 " not found"  in
                    Prims.op_Hat "Effect name " uu____27547  in
                  (FStar_Errors.Fatal_EffectNotFound, uu____27545)  in
                FStar_Errors.raise_error uu____27539
                  d.FStar_Parser_AST.drange
            | FStar_Pervasives_Native.Some l2 -> l2  in
          let src = lookup1 l.FStar_Parser_AST.msource  in
          let dst = lookup1 l.FStar_Parser_AST.mdest  in
          let uu____27557 =
            match l.FStar_Parser_AST.lift_op with
            | FStar_Parser_AST.NonReifiableLift t ->
                let uu____27575 =
                  let uu____27578 =
                    let uu____27579 = desugar_term env t  in
                    ([], uu____27579)  in
                  FStar_Pervasives_Native.Some uu____27578  in
                (uu____27575, FStar_Pervasives_Native.None)
            | FStar_Parser_AST.ReifiableLift (wp,t) ->
                let uu____27592 =
                  let uu____27595 =
                    let uu____27596 = desugar_term env wp  in
                    ([], uu____27596)  in
                  FStar_Pervasives_Native.Some uu____27595  in
                let uu____27603 =
                  let uu____27606 =
                    let uu____27607 = desugar_term env t  in
                    ([], uu____27607)  in
                  FStar_Pervasives_Native.Some uu____27606  in
                (uu____27592, uu____27603)
            | FStar_Parser_AST.LiftForFree t ->
                let uu____27619 =
                  let uu____27622 =
                    let uu____27623 = desugar_term env t  in
                    ([], uu____27623)  in
                  FStar_Pervasives_Native.Some uu____27622  in
                (FStar_Pervasives_Native.None, uu____27619)
             in
          (match uu____27557 with
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
            let uu____27657 =
              let uu____27658 =
                let uu____27665 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27665, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27658  in
            {
              FStar_Syntax_Syntax.sigel = uu____27657;
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
      let uu____27692 =
        FStar_List.fold_left
          (fun uu____27712  ->
             fun d  ->
               match uu____27712 with
               | (env1,sigelts) ->
                   let uu____27732 = desugar_decl env1 d  in
                   (match uu____27732 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27692 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____27823) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____27827;
               FStar_Syntax_Syntax.exports = uu____27828;
               FStar_Syntax_Syntax.is_interface = uu____27829;_},FStar_Parser_AST.Module
             (current_lid,uu____27831)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____27840) ->
              let uu____27843 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____27843
           in
        let uu____27848 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____27890 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27890, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____27912 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____27912, mname, decls, false)
           in
        match uu____27848 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____27954 = desugar_decls env2 decls  in
            (match uu____27954 with
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
          let uu____28022 =
            (FStar_Options.interactive ()) &&
              (let uu____28025 =
                 let uu____28027 =
                   let uu____28029 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28029  in
                 FStar_Util.get_file_extension uu____28027  in
               FStar_List.mem uu____28025 ["fsti"; "fsi"])
             in
          if uu____28022 then as_interface m else m  in
        let uu____28043 = desugar_modul_common curmod env m1  in
        match uu____28043 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28065 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28065, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28087 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28087 with
      | (env1,modul,pop_when_done) ->
          let uu____28104 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28104 with
           | (env2,modul1) ->
               ((let uu____28116 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28116
                 then
                   let uu____28119 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28119
                 else ());
                (let uu____28124 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28124, modul1))))
  
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
        (fun uu____28174  ->
           let uu____28175 = desugar_modul env modul  in
           match uu____28175 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28213  ->
           let uu____28214 = desugar_decls env decls  in
           match uu____28214 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28265  ->
             let uu____28266 = desugar_partial_modul modul env a_modul  in
             match uu____28266 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28361 ->
                  let t =
                    let uu____28371 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28371  in
                  let uu____28384 =
                    let uu____28385 = FStar_Syntax_Subst.compress t  in
                    uu____28385.FStar_Syntax_Syntax.n  in
                  (match uu____28384 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28397,uu____28398)
                       -> bs1
                   | uu____28423 -> failwith "Impossible")
               in
            let uu____28433 =
              let uu____28440 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28440
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28433 with
            | (binders,uu____28442,binders_opening) ->
                let erase_term t =
                  let uu____28450 =
                    let uu____28451 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28451  in
                  FStar_Syntax_Subst.close binders uu____28450  in
                let erase_tscheme uu____28469 =
                  match uu____28469 with
                  | (us,t) ->
                      let t1 =
                        let uu____28489 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28489 t  in
                      let uu____28492 =
                        let uu____28493 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28493  in
                      ([], uu____28492)
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
                    | uu____28516 ->
                        let bs =
                          let uu____28526 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28526  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28566 =
                          let uu____28567 =
                            let uu____28570 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28570  in
                          uu____28567.FStar_Syntax_Syntax.n  in
                        (match uu____28566 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28572,uu____28573) -> bs1
                         | uu____28598 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28606 =
                      let uu____28607 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28607  in
                    FStar_Syntax_Subst.close binders uu____28606  in
                  let uu___3855_28608 = action  in
                  let uu____28609 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28610 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3855_28608.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3855_28608.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28609;
                    FStar_Syntax_Syntax.action_typ = uu____28610
                  }  in
                let uu___3857_28611 = ed  in
                let uu____28612 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28613 =
                  let uu____28614 =
                    erase_term
                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_m
                     in
                  let uu____28615 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_ret
                     in
                  let uu____28616 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.spec).FStar_Syntax_Syntax.monad_bind
                     in
                  {
                    FStar_Syntax_Syntax.monad_m = uu____28614;
                    FStar_Syntax_Syntax.monad_ret = uu____28615;
                    FStar_Syntax_Syntax.monad_bind = uu____28616
                  }  in
                let uu____28617 = erase_term ed.FStar_Syntax_Syntax.signature
                   in
                let uu____28618 =
                  erase_tscheme ed.FStar_Syntax_Syntax.if_then_else  in
                let uu____28619 = erase_tscheme ed.FStar_Syntax_Syntax.ite_wp
                   in
                let uu____28620 =
                  erase_tscheme ed.FStar_Syntax_Syntax.stronger  in
                let uu____28621 =
                  erase_tscheme ed.FStar_Syntax_Syntax.close_wp  in
                let uu____28622 =
                  erase_tscheme ed.FStar_Syntax_Syntax.trivial  in
                let uu____28623 =
                  let uu____28624 =
                    erase_term
                      (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_m
                     in
                  let uu____28625 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_ret
                     in
                  let uu____28626 =
                    erase_tscheme
                      (ed.FStar_Syntax_Syntax.repr).FStar_Syntax_Syntax.monad_bind
                     in
                  {
                    FStar_Syntax_Syntax.monad_m = uu____28624;
                    FStar_Syntax_Syntax.monad_ret = uu____28625;
                    FStar_Syntax_Syntax.monad_bind = uu____28626
                  }  in
                let uu____28627 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3857_28611.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.mname =
                    (uu___3857_28611.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28612;
                  FStar_Syntax_Syntax.spec = uu____28613;
                  FStar_Syntax_Syntax.signature = uu____28617;
                  FStar_Syntax_Syntax.if_then_else = uu____28618;
                  FStar_Syntax_Syntax.ite_wp = uu____28619;
                  FStar_Syntax_Syntax.stronger = uu____28620;
                  FStar_Syntax_Syntax.close_wp = uu____28621;
                  FStar_Syntax_Syntax.trivial = uu____28622;
                  FStar_Syntax_Syntax.repr = uu____28623;
                  FStar_Syntax_Syntax.elaborated =
                    (uu___3857_28611.FStar_Syntax_Syntax.elaborated);
                  FStar_Syntax_Syntax.spec_dm4f =
                    (uu___3857_28611.FStar_Syntax_Syntax.spec_dm4f);
                  FStar_Syntax_Syntax.interp =
                    (uu___3857_28611.FStar_Syntax_Syntax.interp);
                  FStar_Syntax_Syntax.mrelation =
                    (uu___3857_28611.FStar_Syntax_Syntax.mrelation);
                  FStar_Syntax_Syntax.actions = uu____28627;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3857_28611.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3864_28643 = se  in
                  let uu____28644 =
                    let uu____28645 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28645  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28644;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3864_28643.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3864_28643.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3864_28643.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3864_28643.FStar_Syntax_Syntax.sigattrs)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28647 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28648 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28648 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28665 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28665
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28667 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28667)
  