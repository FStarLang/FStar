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
                 let uu___202_844 = t  in
                 {
                   FStar_Syntax_Syntax.n =
                     (uu___202_844.FStar_Syntax_Syntax.n);
                   FStar_Syntax_Syntax.pos = (op.FStar_Ident.idRange);
                   FStar_Syntax_Syntax.vars =
                     (uu___202_844.FStar_Syntax_Syntax.vars)
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
  FStar_Ident.ident FStar_Util.set ->
    FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set)
  =
  fun acc  ->
    fun p  ->
      let gather_pattern_bound_vars_from_list =
        FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc  in
      match p.FStar_Parser_AST.pat with
      | FStar_Parser_AST.PatWild uu____2099 -> acc
      | FStar_Parser_AST.PatConst uu____2102 -> acc
      | FStar_Parser_AST.PatName uu____2103 -> acc
      | FStar_Parser_AST.PatOp uu____2104 -> acc
      | FStar_Parser_AST.PatApp (phead,pats) ->
          gather_pattern_bound_vars_from_list (phead :: pats)
      | FStar_Parser_AST.PatTvar (x,uu____2112) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatVar (x,uu____2118) -> FStar_Util.set_add x acc
      | FStar_Parser_AST.PatList pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatTuple (pats,uu____2127) ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatOr pats ->
          gather_pattern_bound_vars_from_list pats
      | FStar_Parser_AST.PatRecord guarded_pats ->
          let uu____2144 =
            FStar_List.map FStar_Pervasives_Native.snd guarded_pats  in
          gather_pattern_bound_vars_from_list uu____2144
      | FStar_Parser_AST.PatAscribed (pat,uu____2152) ->
          gather_pattern_bound_vars_maybe_top acc pat
  
let (gather_pattern_bound_vars :
  FStar_Parser_AST.pattern -> FStar_Ident.ident FStar_Util.set) =
  let acc =
    FStar_Util.new_set
      (fun id1  ->
         fun id2  ->
           if id1.FStar_Ident.idText = id2.FStar_Ident.idText
           then Prims.int_zero
           else Prims.int_one)
     in
  fun p  -> gather_pattern_bound_vars_maybe_top acc p 
type bnd =
  | LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) 
  | LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) 
let (uu___is_LocalBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalBinder _0 -> true | uu____2225 -> false
  
let (__proj__LocalBinder__item___0 :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun projectee  -> match projectee with | LocalBinder _0 -> _0 
let (uu___is_LetBinder : bnd -> Prims.bool) =
  fun projectee  ->
    match projectee with | LetBinder _0 -> true | uu____2266 -> false
  
let (__proj__LetBinder__item___0 :
  bnd ->
    (FStar_Ident.lident * (FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)))
  = fun projectee  -> match projectee with | LetBinder _0 -> _0 
let (is_implicit : bnd -> Prims.bool) =
  fun b  ->
    match b with
    | LocalBinder
        (uu____2314,FStar_Pervasives_Native.Some
         (FStar_Syntax_Syntax.Implicit uu____2315))
        -> true
    | uu____2318 -> false
  
let (binder_of_bnd :
  bnd -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)) =
  fun uu___3_2329  ->
    match uu___3_2329 with
    | LocalBinder (a,aq) -> (a, aq)
    | uu____2336 -> failwith "Impossible"
  
let (mk_lb :
  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list *
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax *
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)
    -> FStar_Syntax_Syntax.letbinding)
  =
  fun uu____2369  ->
    match uu____2369 with
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
      let uu____2451 =
        let uu____2468 =
          let uu____2471 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid
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
  
let (mk_ref_alloc :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun tm  ->
    let tm' =
      let uu____2541 =
        let uu____2558 =
          let uu____2561 =
            FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Syntax_Syntax.fv_to_tm uu____2561  in
        let uu____2562 =
          let uu____2573 =
            let uu____2582 = FStar_Syntax_Syntax.as_implicit false  in
            (tm, uu____2582)  in
          [uu____2573]  in
        (uu____2558, uu____2562)  in
      FStar_Syntax_Syntax.Tm_app uu____2541  in
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
          let uu____2645 =
            let uu____2662 =
              let uu____2665 =
                FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid
                  FStar_Syntax_Syntax.delta_constant
                  FStar_Pervasives_Native.None
                 in
              FStar_Syntax_Syntax.fv_to_tm uu____2665  in
            let uu____2666 =
              let uu____2677 =
                let uu____2686 = FStar_Syntax_Syntax.as_implicit false  in
                (t1, uu____2686)  in
              let uu____2694 =
                let uu____2705 =
                  let uu____2714 = FStar_Syntax_Syntax.as_implicit false  in
                  (t2, uu____2714)  in
                [uu____2705]  in
              uu____2677 :: uu____2694  in
            (uu____2662, uu____2666)  in
          FStar_Syntax_Syntax.Tm_app uu____2645  in
        FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos
  
let rec (generalize_annotated_univs :
  FStar_Syntax_Syntax.sigelt -> FStar_Syntax_Syntax.sigelt) =
  fun s  ->
    let bs_univnames bs =
      let uu____2774 =
        let uu____2789 =
          FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name  in
        FStar_List.fold_left
          (fun uvs  ->
             fun uu____2808  ->
               match uu____2808 with
               | ({ FStar_Syntax_Syntax.ppname = uu____2819;
                    FStar_Syntax_Syntax.index = uu____2820;
                    FStar_Syntax_Syntax.sort = t;_},uu____2822)
                   ->
                   let uu____2830 = FStar_Syntax_Free.univnames t  in
                   FStar_Util.set_union uvs uu____2830) uu____2789
         in
      FStar_All.pipe_right bs uu____2774  in
    let empty_set = FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name
       in
    match s.FStar_Syntax_Syntax.sigel with
    | FStar_Syntax_Syntax.Sig_inductive_typ uu____2846 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_datacon uu____2864 ->
        failwith
          "Impossible: collect_annotated_universes: bare data/type constructor"
    | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
        let uvs =
          let uu____2892 =
            FStar_All.pipe_right sigs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun se  ->
                      let se_univs =
                        match se.FStar_Syntax_Syntax.sigel with
                        | FStar_Syntax_Syntax.Sig_inductive_typ
                            (uu____2913,uu____2914,bs,t,uu____2917,uu____2918)
                            ->
                            let uu____2927 = bs_univnames bs  in
                            let uu____2930 = FStar_Syntax_Free.univnames t
                               in
                            FStar_Util.set_union uu____2927 uu____2930
                        | FStar_Syntax_Syntax.Sig_datacon
                            (uu____2933,uu____2934,t,uu____2936,uu____2937,uu____2938)
                            -> FStar_Syntax_Free.univnames t
                        | uu____2945 ->
                            failwith
                              "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                         in
                      FStar_Util.set_union uvs se_univs) empty_set)
             in
          FStar_All.pipe_right uu____2892 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___589_2954 = s  in
        let uu____2955 =
          let uu____2956 =
            let uu____2965 =
              FStar_All.pipe_right sigs
                (FStar_List.map
                   (fun se  ->
                      match se.FStar_Syntax_Syntax.sigel with
                      | FStar_Syntax_Syntax.Sig_inductive_typ
                          (lid,uu____2983,bs,t,lids1,lids2) ->
                          let uu___600_2996 = se  in
                          let uu____2997 =
                            let uu____2998 =
                              let uu____3015 =
                                FStar_Syntax_Subst.subst_binders usubst bs
                                 in
                              let uu____3016 =
                                let uu____3017 =
                                  FStar_Syntax_Subst.shift_subst
                                    (FStar_List.length bs) usubst
                                   in
                                FStar_Syntax_Subst.subst uu____3017 t  in
                              (lid, uvs, uu____3015, uu____3016, lids1,
                                lids2)
                               in
                            FStar_Syntax_Syntax.Sig_inductive_typ uu____2998
                             in
                          {
                            FStar_Syntax_Syntax.sigel = uu____2997;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___600_2996.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___600_2996.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___600_2996.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___600_2996.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___600_2996.FStar_Syntax_Syntax.sigopts)
                          }
                      | FStar_Syntax_Syntax.Sig_datacon
                          (lid,uu____3031,t,tlid,n1,lids1) ->
                          let uu___610_3042 = se  in
                          let uu____3043 =
                            let uu____3044 =
                              let uu____3060 =
                                FStar_Syntax_Subst.subst usubst t  in
                              (lid, uvs, uu____3060, tlid, n1, lids1)  in
                            FStar_Syntax_Syntax.Sig_datacon uu____3044  in
                          {
                            FStar_Syntax_Syntax.sigel = uu____3043;
                            FStar_Syntax_Syntax.sigrng =
                              (uu___610_3042.FStar_Syntax_Syntax.sigrng);
                            FStar_Syntax_Syntax.sigquals =
                              (uu___610_3042.FStar_Syntax_Syntax.sigquals);
                            FStar_Syntax_Syntax.sigmeta =
                              (uu___610_3042.FStar_Syntax_Syntax.sigmeta);
                            FStar_Syntax_Syntax.sigattrs =
                              (uu___610_3042.FStar_Syntax_Syntax.sigattrs);
                            FStar_Syntax_Syntax.sigopts =
                              (uu___610_3042.FStar_Syntax_Syntax.sigopts)
                          }
                      | uu____3064 ->
                          failwith
                            "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
               in
            (uu____2965, lids)  in
          FStar_Syntax_Syntax.Sig_bundle uu____2956  in
        {
          FStar_Syntax_Syntax.sigel = uu____2955;
          FStar_Syntax_Syntax.sigrng =
            (uu___589_2954.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___589_2954.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___589_2954.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___589_2954.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___589_2954.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3071,t) ->
        let uvs =
          let uu____3074 = FStar_Syntax_Free.univnames t  in
          FStar_All.pipe_right uu____3074 FStar_Util.set_elements  in
        let uu___619_3079 = s  in
        let uu____3080 =
          let uu____3081 =
            let uu____3088 = FStar_Syntax_Subst.close_univ_vars uvs t  in
            (lid, uvs, uu____3088)  in
          FStar_Syntax_Syntax.Sig_declare_typ uu____3081  in
        {
          FStar_Syntax_Syntax.sigel = uu____3080;
          FStar_Syntax_Syntax.sigrng =
            (uu___619_3079.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___619_3079.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___619_3079.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___619_3079.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___619_3079.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
        let lb_univnames lb =
          let uu____3112 =
            FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
          let uu____3115 =
            match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3122) ->
                let uvs1 = bs_univnames bs  in
                let uvs2 =
                  match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3155,(FStar_Util.Inl t,uu____3157),uu____3158)
                      -> FStar_Syntax_Free.univnames t
                  | FStar_Syntax_Syntax.Tm_ascribed
                      (uu____3205,(FStar_Util.Inr c,uu____3207),uu____3208)
                      -> FStar_Syntax_Free.univnames_comp c
                  | uu____3255 -> empty_set  in
                FStar_Util.set_union uvs1 uvs2
            | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3257) -> bs_univnames bs
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3278,(FStar_Util.Inl t,uu____3280),uu____3281) ->
                FStar_Syntax_Free.univnames t
            | FStar_Syntax_Syntax.Tm_ascribed
                (uu____3328,(FStar_Util.Inr c,uu____3330),uu____3331) ->
                FStar_Syntax_Free.univnames_comp c
            | uu____3378 -> empty_set  in
          FStar_Util.set_union uu____3112 uu____3115  in
        let all_lb_univs =
          let uu____3382 =
            FStar_All.pipe_right lbs
              (FStar_List.fold_left
                 (fun uvs  ->
                    fun lb  ->
                      let uu____3398 = lb_univnames lb  in
                      FStar_Util.set_union uvs uu____3398) empty_set)
             in
          FStar_All.pipe_right uu____3382 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
        let uu___678_3408 = s  in
        let uu____3409 =
          let uu____3410 =
            let uu____3417 =
              let uu____3418 =
                FStar_All.pipe_right lbs
                  (FStar_List.map
                     (fun lb  ->
                        let uu___681_3430 = lb  in
                        let uu____3431 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbtyp
                           in
                        let uu____3434 =
                          FStar_Syntax_Subst.subst usubst
                            lb.FStar_Syntax_Syntax.lbdef
                           in
                        {
                          FStar_Syntax_Syntax.lbname =
                            (uu___681_3430.FStar_Syntax_Syntax.lbname);
                          FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                          FStar_Syntax_Syntax.lbtyp = uu____3431;
                          FStar_Syntax_Syntax.lbeff =
                            (uu___681_3430.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef = uu____3434;
                          FStar_Syntax_Syntax.lbattrs =
                            (uu___681_3430.FStar_Syntax_Syntax.lbattrs);
                          FStar_Syntax_Syntax.lbpos =
                            (uu___681_3430.FStar_Syntax_Syntax.lbpos)
                        }))
                 in
              (b, uu____3418)  in
            (uu____3417, lids)  in
          FStar_Syntax_Syntax.Sig_let uu____3410  in
        {
          FStar_Syntax_Syntax.sigel = uu____3409;
          FStar_Syntax_Syntax.sigrng =
            (uu___678_3408.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___678_3408.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___678_3408.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___678_3408.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___678_3408.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_assume (lid,uu____3443,fml) ->
        let uvs =
          let uu____3446 = FStar_Syntax_Free.univnames fml  in
          FStar_All.pipe_right uu____3446 FStar_Util.set_elements  in
        let uu___689_3451 = s  in
        let uu____3452 =
          let uu____3453 =
            let uu____3460 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
            (lid, uvs, uu____3460)  in
          FStar_Syntax_Syntax.Sig_assume uu____3453  in
        {
          FStar_Syntax_Syntax.sigel = uu____3452;
          FStar_Syntax_Syntax.sigrng =
            (uu___689_3451.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___689_3451.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___689_3451.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___689_3451.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___689_3451.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3462,bs,c,flags) ->
        let uvs =
          let uu____3471 =
            let uu____3474 = bs_univnames bs  in
            let uu____3477 = FStar_Syntax_Free.univnames_comp c  in
            FStar_Util.set_union uu____3474 uu____3477  in
          FStar_All.pipe_right uu____3471 FStar_Util.set_elements  in
        let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
        let uu___700_3485 = s  in
        let uu____3486 =
          let uu____3487 =
            let uu____3500 = FStar_Syntax_Subst.subst_binders usubst bs  in
            let uu____3501 = FStar_Syntax_Subst.subst_comp usubst c  in
            (lid, uvs, uu____3500, uu____3501, flags)  in
          FStar_Syntax_Syntax.Sig_effect_abbrev uu____3487  in
        {
          FStar_Syntax_Syntax.sigel = uu____3486;
          FStar_Syntax_Syntax.sigrng =
            (uu___700_3485.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___700_3485.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___700_3485.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___700_3485.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___700_3485.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_fail (errs,lax1,ses) ->
        let uu___707_3519 = s  in
        let uu____3520 =
          let uu____3521 =
            let uu____3534 = FStar_List.map generalize_annotated_univs ses
               in
            (errs, lax1, uu____3534)  in
          FStar_Syntax_Syntax.Sig_fail uu____3521  in
        {
          FStar_Syntax_Syntax.sigel = uu____3520;
          FStar_Syntax_Syntax.sigrng =
            (uu___707_3519.FStar_Syntax_Syntax.sigrng);
          FStar_Syntax_Syntax.sigquals =
            (uu___707_3519.FStar_Syntax_Syntax.sigquals);
          FStar_Syntax_Syntax.sigmeta =
            (uu___707_3519.FStar_Syntax_Syntax.sigmeta);
          FStar_Syntax_Syntax.sigattrs =
            (uu___707_3519.FStar_Syntax_Syntax.sigattrs);
          FStar_Syntax_Syntax.sigopts =
            (uu___707_3519.FStar_Syntax_Syntax.sigopts)
        }
    | FStar_Syntax_Syntax.Sig_new_effect uu____3543 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3544 -> s
    | FStar_Syntax_Syntax.Sig_main uu____3545 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3546 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3557 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3564 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3572  ->
    match uu___4_3572 with
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
    | uu____3621 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = Prims.int_zero
      then u
      else
        (let uu____3642 = sum_to_universe u (n1 - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3642)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3668 =
      let uu____3669 = unparen t  in uu____3669.FStar_Parser_AST.tm  in
    match uu____3668 with
    | FStar_Parser_AST.Wild  ->
        let uu____3675 =
          let uu____3676 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3676  in
        FStar_Util.Inr uu____3675
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3689)) ->
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
             let uu____3780 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3780
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3797 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3797
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3813 =
               let uu____3819 =
                 let uu____3821 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3821
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3819)
                in
             FStar_Errors.raise_error uu____3813 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3830 ->
        let rec aux t1 univargs =
          let uu____3867 =
            let uu____3868 = unparen t1  in uu____3868.FStar_Parser_AST.tm
             in
          match uu____3867 with
          | FStar_Parser_AST.App (t2,targ,uu____3876) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3903  ->
                     match uu___5_3903 with
                     | FStar_Util.Inr uu____3910 -> true
                     | uu____3913 -> false) univargs
              then
                let uu____3921 =
                  let uu____3922 =
                    FStar_List.map
                      (fun uu___6_3932  ->
                         match uu___6_3932 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3922  in
                FStar_Util.Inr uu____3921
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3958  ->
                        match uu___7_3958 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3968 -> failwith "impossible")
                     univargs
                    in
                 let uu____3972 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3972)
          | uu____3988 ->
              let uu____3989 =
                let uu____3995 =
                  let uu____3997 =
                    let uu____3999 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3999 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3997  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3995)  in
              FStar_Errors.raise_error uu____3989 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____4014 ->
        let uu____4015 =
          let uu____4021 =
            let uu____4023 =
              let uu____4025 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____4025 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____4023  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____4021)  in
        FStar_Errors.raise_error uu____4015 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____4066;_});
            FStar_Syntax_Syntax.pos = uu____4067;
            FStar_Syntax_Syntax.vars = uu____4068;_})::uu____4069
        ->
        let uu____4100 =
          let uu____4106 =
            let uu____4108 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4108
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4106)  in
        FStar_Errors.raise_error uu____4100 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4114 ->
        let uu____4133 =
          let uu____4139 =
            let uu____4141 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4141
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4139)  in
        FStar_Errors.raise_error uu____4133 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4154 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4154) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4182 = FStar_List.hd fields  in
        match uu____4182 with
        | (f,uu____4192) ->
            let record =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
               in
            let check_field uu____4203 =
              match uu____4203 with
              | (f',uu____4209) ->
                  let uu____4210 =
                    FStar_Syntax_DsEnv.belongs_to_record env f' record  in
                  if uu____4210
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
                         msg) rg)
               in
            ((let uu____4220 = FStar_List.tl fields  in
              FStar_List.iter check_field uu____4220);
             (match () with | () -> record))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4268 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4275 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4276 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4278,pats1) ->
            let aux out uu____4319 =
              match uu____4319 with
              | (p1,uu____4332) ->
                  let intersection =
                    let uu____4342 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4342 out  in
                  let uu____4345 = FStar_Util.set_is_empty intersection  in
                  if uu____4345
                  then
                    let uu____4350 = pat_vars p1  in
                    FStar_Util.set_union out uu____4350
                  else
                    (let duplicate_bv =
                       let uu____4356 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4356  in
                     let uu____4359 =
                       let uu____4365 =
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4365)
                        in
                     FStar_Errors.raise_error uu____4359 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4389 = pat_vars p  in
          FStar_All.pipe_right uu____4389 (fun a1  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4417 =
              let uu____4419 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4419  in
            if uu____4417
            then ()
            else
              (let nonlinear_vars =
                 let uu____4428 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4428  in
               let first_nonlinear_var =
                 let uu____4432 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4432  in
               let uu____4435 =
                 let uu____4441 =
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4441)  in
               FStar_Errors.raise_error uu____4435 r)
             in
          FStar_List.iter aux ps
  
let rec (desugar_data_pat :
  Prims.bool ->
    env_t ->
      FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  =
  fun top_level_ascr_allowed  ->
    fun env  ->
      fun p  ->
        let resolvex l e x =
          let uu____4756 =
            FStar_Util.find_opt
              (fun y  ->
                 (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                   x.FStar_Ident.idText) l
             in
          match uu____4756 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4773 ->
              let uu____4776 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4776 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4917 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4939 =
                  let uu____4945 =
                    FStar_Parser_AST.compile_op Prims.int_zero
                      op.FStar_Ident.idText op.FStar_Ident.idRange
                     in
                  (uu____4945, (op.FStar_Ident.idRange))  in
                FStar_Ident.mk_ident uu____4939  in
              let p2 =
                let uu___932_4950 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___932_4950.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4967 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4970 = aux loc env1 p2  in
                match uu____4970 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5026 =
                      match binder with
                      | LetBinder uu____5047 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5072 = close_fun env1 t  in
                            desugar_term env1 uu____5072  in
                          let x1 =
                            let uu___958_5074 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___958_5074.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___958_5074.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5026 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5120 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5121 -> ()
                           | uu____5122 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5123 ->
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
              let uu____5141 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5141, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5154 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5154, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5172 = resolvex loc env1 x  in
              (match uu____5172 with
               | (loc1,env2,xbv) ->
                   let uu____5204 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5204, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5222 = resolvex loc env1 x  in
              (match uu____5222 with
               | (loc1,env2,xbv) ->
                   let uu____5254 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5254, []))
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
              let uu____5268 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5268, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5296;_},args)
              ->
              let uu____5302 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5363  ->
                       match uu____5363 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5444 = aux loc1 env2 arg  in
                           (match uu____5444 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5302 with
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
                   let uu____5616 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5616, annots))
          | FStar_Parser_AST.PatApp uu____5632 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5660 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5710  ->
                       match uu____5710 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5771 = aux loc1 env2 pat  in
                           (match uu____5771 with
                            | (loc2,env3,uu____5810,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5660 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5904 =
                       let uu____5907 =
                         let uu____5914 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5914  in
                       let uu____5915 =
                         let uu____5916 =
                           let uu____5930 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5930, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5916  in
                       FStar_All.pipe_left uu____5907 uu____5915  in
                     FStar_List.fold_right
                       (fun hd1  ->
                          fun tl1  ->
                            let r =
                              FStar_Range.union_ranges
                                hd1.FStar_Syntax_Syntax.p
                                tl1.FStar_Syntax_Syntax.p
                               in
                            let uu____5964 =
                              let uu____5965 =
                                let uu____5979 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5979, [(hd1, false); (tl1, false)])
                                 in
                              FStar_Syntax_Syntax.Pat_cons uu____5965  in
                            FStar_All.pipe_left (pos_r r) uu____5964) pats1
                       uu____5904
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
          | FStar_Parser_AST.PatTuple (args,dep1) ->
              let uu____6035 =
                FStar_List.fold_left
                  (fun uu____6094  ->
                     fun p2  ->
                       match uu____6094 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6176 = aux loc1 env2 p2  in
                           (match uu____6176 with
                            | (loc2,env3,uu____6220,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6035 with
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
                     | uu____6383 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6386 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6386, annots))
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
                     (fun uu____6462  ->
                        match uu____6462 with
                        | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6492  ->
                        match uu____6492 with
                        | (f,uu____6498) ->
                            let uu____6499 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6525  ->
                                      match uu____6525 with
                                      | (g,uu____6532) ->
                                          f.FStar_Ident.idText =
                                            g.FStar_Ident.idText))
                               in
                            (match uu____6499 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6538,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6545 =
                  let uu____6546 =
                    let uu____6553 =
                      let uu____6554 =
                        let uu____6555 =
                          FStar_Ident.lid_of_ids
                            (FStar_List.append
                               (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                               [record.FStar_Syntax_DsEnv.constrname])
                           in
                        FStar_Parser_AST.PatName uu____6555  in
                      FStar_Parser_AST.mk_pattern uu____6554
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6553, args)  in
                  FStar_Parser_AST.PatApp uu____6546  in
                FStar_Parser_AST.mk_pattern uu____6545
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6558 = aux loc env1 app  in
              (match uu____6558 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6635 =
                           let uu____6636 =
                             let uu____6650 =
                               let uu___1108_6651 = fv  in
                               let uu____6652 =
                                 let uu____6655 =
                                   let uu____6656 =
                                     let uu____6663 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6663)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6656
                                    in
                                 FStar_Pervasives_Native.Some uu____6655  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1108_6651.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1108_6651.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6652
                               }  in
                             (uu____6650, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6636  in
                         FStar_All.pipe_left pos uu____6635
                     | uu____6689 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6773 = aux' true loc env1 p2  in
              (match uu____6773 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6826 =
                     FStar_List.fold_left
                       (fun uu____6874  ->
                          fun p4  ->
                            match uu____6874 with
                            | (loc2,env3,ps1) ->
                                let uu____6939 = aux' true loc2 env3 p4  in
                                (match uu____6939 with
                                 | (loc3,env4,uu____6977,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6826 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7138 ->
              let uu____7139 = aux' true loc env1 p1  in
              (match uu____7139 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7230 = aux_maybe_or env p  in
        match uu____7230 with
        | (env1,b,pats) ->
            ((let uu____7285 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7285
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
            let uu____7359 =
              let uu____7360 =
                let uu____7371 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7371, (ty, tacopt))  in
              LetBinder uu____7360  in
            (env, uu____7359, [])  in
          let op_to_ident x =
            let uu____7388 =
              let uu____7394 =
                FStar_Parser_AST.compile_op Prims.int_zero
                  x.FStar_Ident.idText x.FStar_Ident.idRange
                 in
              (uu____7394, (x.FStar_Ident.idRange))  in
            FStar_Ident.mk_ident uu____7388  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7407 = op_to_ident x  in
              mklet uu____7407 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7409) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7415;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7431 = op_to_ident x  in
              let uu____7432 = desugar_term env t  in
              mklet uu____7431 uu____7432 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7434);
                 FStar_Parser_AST.prange = uu____7435;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7455 = desugar_term env t  in
              mklet x uu____7455 tacopt1
          | uu____7456 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7469 = desugar_data_pat true env p  in
           match uu____7469 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7499;
                      FStar_Syntax_Syntax.p = uu____7500;_},uu____7501)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7514;
                      FStar_Syntax_Syntax.p = uu____7515;_},uu____7516)::[]
                     -> []
                 | uu____7529 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7537  ->
    fun env  ->
      fun pat  ->
        let uu____7541 = desugar_data_pat false env pat  in
        match uu____7541 with | (env1,uu____7558,pat1) -> (env1, pat1)

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
      let uu____7580 = desugar_term_aq env e  in
      match uu____7580 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7599 = desugar_typ_aq env e  in
      match uu____7599 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7609  ->
        fun range  ->
          match uu____7609 with
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
              ((let uu____7631 =
                  let uu____7633 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7633  in
                if uu____7631
                then
                  let uu____7636 =
                    let uu____7642 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7642)  in
                  FStar_Errors.log_issue range uu____7636
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
                  let uu____7663 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7663 range  in
                let lid1 =
                  let uu____7667 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7667 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7677 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7677 range  in
                           let private_fv =
                             let uu____7679 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7679 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1275_7680 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1275_7680.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1275_7680.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7681 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7685 =
                        let uu____7691 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7691)
                         in
                      FStar_Errors.raise_error uu____7685 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7711 =
                  let uu____7718 =
                    let uu____7719 =
                      let uu____7736 =
                        let uu____7747 =
                          let uu____7756 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7756)  in
                        [uu____7747]  in
                      (lid1, uu____7736)  in
                    FStar_Syntax_Syntax.Tm_app uu____7719  in
                  FStar_Syntax_Syntax.mk uu____7718  in
                uu____7711 FStar_Pervasives_Native.None range))

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
          let uu___1291_7875 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1291_7875.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1291_7875.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7878 =
          let uu____7879 = unparen top  in uu____7879.FStar_Parser_AST.tm  in
        match uu____7878 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7884 ->
            let uu____7893 = desugar_formula env top  in (uu____7893, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7902 = desugar_formula env t  in (uu____7902, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7911 = desugar_formula env t  in (uu____7911, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7938 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7938, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7940 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7940, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7949 =
                let uu____7950 =
                  let uu____7957 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7957, args)  in
                FStar_Parser_AST.Op uu____7950  in
              FStar_Parser_AST.mk_term uu____7949 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7962 =
              let uu____7963 =
                let uu____7964 =
                  let uu____7971 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7971, [e])  in
                FStar_Parser_AST.Op uu____7964  in
              FStar_Parser_AST.mk_term uu____7963 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7962
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7983 = FStar_Ident.text_of_id op_star  in
             uu____7983 = "*") &&
              (let uu____7988 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____7988 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____8005;_},t1::t2::[])
                  when
                  let uu____8011 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____8011 FStar_Option.isNone ->
                  let uu____8018 = flatten1 t1  in
                  FStar_List.append uu____8018 [t2]
              | uu____8021 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1339_8026 = top  in
              let uu____8027 =
                let uu____8028 =
                  let uu____8039 =
                    FStar_List.map (fun _8050  -> FStar_Util.Inr _8050) terms
                     in
                  (uu____8039, rhs)  in
                FStar_Parser_AST.Sum uu____8028  in
              {
                FStar_Parser_AST.tm = uu____8027;
                FStar_Parser_AST.range =
                  (uu___1339_8026.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1339_8026.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8058 =
              let uu____8059 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8059  in
            (uu____8058, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8065 =
              let uu____8071 =
                let uu____8073 =
                  let uu____8075 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8075 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8073  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8071)  in
            FStar_Errors.raise_error uu____8065 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8090 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8090 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8097 =
                   let uu____8103 =
                     let uu____8105 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8105
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8103)
                    in
                 FStar_Errors.raise_error uu____8097
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8120 =
                     let uu____8145 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8207 = desugar_term_aq env t  in
                               match uu____8207 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8145 FStar_List.unzip  in
                   (match uu____8120 with
                    | (args1,aqs) ->
                        let uu____8340 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8340, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8357)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8374 =
              let uu___1368_8375 = top  in
              let uu____8376 =
                let uu____8377 =
                  let uu____8384 =
                    let uu___1370_8385 = top  in
                    let uu____8386 =
                      let uu____8387 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8387  in
                    {
                      FStar_Parser_AST.tm = uu____8386;
                      FStar_Parser_AST.range =
                        (uu___1370_8385.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1370_8385.FStar_Parser_AST.level)
                    }  in
                  (uu____8384, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8377  in
              {
                FStar_Parser_AST.tm = uu____8376;
                FStar_Parser_AST.range =
                  (uu___1368_8375.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1368_8375.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8374
        | FStar_Parser_AST.Construct (n1,(a,uu____8395)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8415 =
                let uu___1380_8416 = top  in
                let uu____8417 =
                  let uu____8418 =
                    let uu____8425 =
                      let uu___1382_8426 = top  in
                      let uu____8427 =
                        let uu____8428 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8428  in
                      {
                        FStar_Parser_AST.tm = uu____8427;
                        FStar_Parser_AST.range =
                          (uu___1382_8426.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1382_8426.FStar_Parser_AST.level)
                      }  in
                    (uu____8425, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8418  in
                {
                  FStar_Parser_AST.tm = uu____8417;
                  FStar_Parser_AST.range =
                    (uu___1380_8416.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1380_8416.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8415))
        | FStar_Parser_AST.Construct (n1,(a,uu____8436)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8453 =
              let uu___1391_8454 = top  in
              let uu____8455 =
                let uu____8456 =
                  let uu____8463 =
                    let uu___1393_8464 = top  in
                    let uu____8465 =
                      let uu____8466 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8466  in
                    {
                      FStar_Parser_AST.tm = uu____8465;
                      FStar_Parser_AST.range =
                        (uu___1393_8464.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1393_8464.FStar_Parser_AST.level)
                    }  in
                  (uu____8463, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8456  in
              {
                FStar_Parser_AST.tm = uu____8455;
                FStar_Parser_AST.range =
                  (uu___1391_8454.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1391_8454.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8453
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8472; FStar_Ident.ident = uu____8473;
              FStar_Ident.nsstr = uu____8474; FStar_Ident.str = "Type0";_}
            ->
            let uu____8479 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8479, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8480; FStar_Ident.ident = uu____8481;
              FStar_Ident.nsstr = uu____8482; FStar_Ident.str = "Type";_}
            ->
            let uu____8487 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8487, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8488; FStar_Ident.ident = uu____8489;
               FStar_Ident.nsstr = uu____8490; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8510 =
              let uu____8511 =
                let uu____8512 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8512  in
              mk1 uu____8511  in
            (uu____8510, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8513; FStar_Ident.ident = uu____8514;
              FStar_Ident.nsstr = uu____8515; FStar_Ident.str = "Effect";_}
            ->
            let uu____8520 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8520, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8521; FStar_Ident.ident = uu____8522;
              FStar_Ident.nsstr = uu____8523; FStar_Ident.str = "True";_}
            ->
            let uu____8528 =
              let uu____8529 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8529
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8528, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8530; FStar_Ident.ident = uu____8531;
              FStar_Ident.nsstr = uu____8532; FStar_Ident.str = "False";_}
            ->
            let uu____8537 =
              let uu____8538 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8538
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8537, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8541;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            let uu____8543 =
              FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
            (match uu____8543 with
             | FStar_Pervasives_Native.Some ed ->
                 let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                 let uu____8552 =
                   FStar_Syntax_Syntax.fvar lid
                     (FStar_Syntax_Syntax.Delta_constant_at_level
                        Prims.int_one) FStar_Pervasives_Native.None
                    in
                 (uu____8552, noaqs)
             | FStar_Pervasives_Native.None  ->
                 let uu____8554 =
                   let uu____8556 = FStar_Ident.text_of_lid eff_name  in
                   FStar_Util.format2
                     "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                     uu____8556 txt
                    in
                 failwith uu____8554)
        | FStar_Parser_AST.Var l ->
            let uu____8564 = desugar_name mk1 setpos env true l  in
            (uu____8564, noaqs)
        | FStar_Parser_AST.Name l ->
            let uu____8572 = desugar_name mk1 setpos env true l  in
            (uu____8572, noaqs)
        | FStar_Parser_AST.Projector (l,i) ->
            let name =
              let uu____8589 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8589 with
              | FStar_Pervasives_Native.Some uu____8599 ->
                  FStar_Pervasives_Native.Some (true, l)
              | FStar_Pervasives_Native.None  ->
                  let uu____8607 =
                    FStar_Syntax_DsEnv.try_lookup_root_effect_name env l  in
                  (match uu____8607 with
                   | FStar_Pervasives_Native.Some new_name ->
                       FStar_Pervasives_Native.Some (false, new_name)
                   | uu____8625 -> FStar_Pervasives_Native.None)
               in
            (match name with
             | FStar_Pervasives_Native.Some (resolve,new_name) ->
                 let uu____8646 =
                   let uu____8647 =
                     FStar_Syntax_Util.mk_field_projector_name_from_ident
                       new_name i
                      in
                   desugar_name mk1 setpos env resolve uu____8647  in
                 (uu____8646, noaqs)
             | uu____8653 ->
                 let uu____8661 =
                   let uu____8667 =
                     FStar_Util.format1
                       "Data constructor or effect %s not found"
                       l.FStar_Ident.str
                      in
                   (FStar_Errors.Fatal_EffectNotFound, uu____8667)  in
                 FStar_Errors.raise_error uu____8661
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Discrim lid ->
            let uu____8676 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
               in
            (match uu____8676 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8683 =
                   let uu____8689 =
                     FStar_Util.format1 "Data constructor %s not found"
                       lid.FStar_Ident.str
                      in
                   (FStar_Errors.Fatal_DataContructorNotFound, uu____8689)
                    in
                 FStar_Errors.raise_error uu____8683
                   top.FStar_Parser_AST.range
             | uu____8697 ->
                 let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                 let uu____8701 = desugar_name mk1 setpos env true lid'  in
                 (uu____8701, noaqs))
        | FStar_Parser_AST.Construct (l,args) ->
            let uu____8722 = FStar_Syntax_DsEnv.try_lookup_datacon env l  in
            (match uu____8722 with
             | FStar_Pervasives_Native.Some head1 ->
                 let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                 (match args with
                  | [] -> (head2, noaqs)
                  | uu____8741 ->
                      let uu____8748 =
                        FStar_Util.take
                          (fun uu____8772  ->
                             match uu____8772 with
                             | (uu____8778,imp) ->
                                 imp = FStar_Parser_AST.UnivApp) args
                         in
                      (match uu____8748 with
                       | (universes,args1) ->
                           let universes1 =
                             FStar_List.map
                               (fun x  ->
                                  desugar_universe
                                    (FStar_Pervasives_Native.fst x))
                               universes
                              in
                           let uu____8823 =
                             let uu____8848 =
                               FStar_List.map
                                 (fun uu____8891  ->
                                    match uu____8891 with
                                    | (t,imp) ->
                                        let uu____8908 =
                                          desugar_term_aq env t  in
                                        (match uu____8908 with
                                         | (te,aq) ->
                                             ((arg_withimp_e imp te), aq)))
                                 args1
                                in
                             FStar_All.pipe_right uu____8848 FStar_List.unzip
                              in
                           (match uu____8823 with
                            | (args2,aqs) ->
                                let head3 =
                                  if universes1 = []
                                  then head2
                                  else
                                    mk1
                                      (FStar_Syntax_Syntax.Tm_uinst
                                         (head2, universes1))
                                   in
                                let uu____9051 =
                                  mk1
                                    (FStar_Syntax_Syntax.Tm_app
                                       (head3, args2))
                                   in
                                (uu____9051, (join_aqs aqs)))))
             | FStar_Pervasives_Native.None  ->
                 let err =
                   let uu____9070 =
                     FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                   match uu____9070 with
                   | FStar_Pervasives_Native.None  ->
                       (FStar_Errors.Fatal_ConstructorNotFound,
                         (Prims.op_Hat "Constructor "
                            (Prims.op_Hat l.FStar_Ident.str " not found")))
                   | FStar_Pervasives_Native.Some uu____9081 ->
                       (FStar_Errors.Fatal_UnexpectedEffect,
                         (Prims.op_Hat "Effect "
                            (Prims.op_Hat l.FStar_Ident.str
                               " used at an unexpected position")))
                    in
                 FStar_Errors.raise_error err top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9109  ->
                 match uu___8_9109 with
                 | FStar_Util.Inr uu____9115 -> true
                 | uu____9117 -> false) binders
            ->
            let terms =
              let uu____9126 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9143  ->
                        match uu___9_9143 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9149 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9126 [t]  in
            let uu____9151 =
              let uu____9176 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9233 = desugar_typ_aq env t1  in
                        match uu____9233 with
                        | (t',aq) ->
                            let uu____9244 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9244, aq)))
                 in
              FStar_All.pipe_right uu____9176 FStar_List.unzip  in
            (match uu____9151 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9354 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9354
                    in
                 let uu____9363 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9363, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9390 =
              let uu____9407 =
                let uu____9414 =
                  let uu____9421 =
                    FStar_All.pipe_left (fun _9430  -> FStar_Util.Inl _9430)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9421]  in
                FStar_List.append binders uu____9414  in
              FStar_List.fold_left
                (fun uu____9475  ->
                   fun b  ->
                     match uu____9475 with
                     | (env1,tparams,typs) ->
                         let uu____9536 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9551 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9551)
                            in
                         (match uu____9536 with
                          | (xopt,t1) ->
                              let uu____9576 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9585 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9585)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9576 with
                               | (env2,x) ->
                                   let uu____9605 =
                                     let uu____9608 =
                                       let uu____9611 =
                                         let uu____9612 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9612
                                          in
                                       [uu____9611]  in
                                     FStar_List.append typs uu____9608  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1547_9638 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1547_9638.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1547_9638.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9605)))) (env, [], []) uu____9407
               in
            (match uu____9390 with
             | (env1,uu____9666,targs) ->
                 let tup =
                   let uu____9689 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9689
                    in
                 let uu____9690 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9690, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9709 = uncurry binders t  in
            (match uu____9709 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9753 =
                   match uu___10_9753 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9770 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9770
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9794 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9794 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9827 = aux env [] bs  in (uu____9827, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9836 = desugar_binder env b  in
            (match uu____9836 with
             | (FStar_Pervasives_Native.None ,uu____9847) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9862 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9862 with
                  | ((x,uu____9878),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9891 =
                        let uu____9892 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9892  in
                      (uu____9891, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9970 = FStar_Util.set_is_empty i  in
                    if uu____9970
                    then
                      let uu____9975 = FStar_Util.set_union acc set1  in
                      aux uu____9975 sets2
                    else
                      (let uu____9980 =
                         let uu____9981 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9981  in
                       FStar_Pervasives_Native.Some uu____9980)
                 in
              let uu____9984 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9984 sets  in
            ((let uu____9988 = check_disjoint bvss  in
              match uu____9988 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9992 =
                    let uu____9998 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9998)
                     in
                  let uu____10002 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9992 uu____10002);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____10010 =
                FStar_List.fold_left
                  (fun uu____10030  ->
                     fun pat  ->
                       match uu____10030 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10056,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10066 =
                                  let uu____10069 = free_type_vars env1 t  in
                                  FStar_List.append uu____10069 ftvs  in
                                (env1, uu____10066)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10074,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10085 =
                                  let uu____10088 = free_type_vars env1 t  in
                                  let uu____10091 =
                                    let uu____10094 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10094 ftvs  in
                                  FStar_List.append uu____10088 uu____10091
                                   in
                                (env1, uu____10085)
                            | uu____10099 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____10010 with
              | (uu____10108,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10120 =
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
                    FStar_List.append uu____10120 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10200 = desugar_term_aq env1 body  in
                        (match uu____10200 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10235 =
                                       let uu____10236 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10236
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10235
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
                             let uu____10305 =
                               let uu____10306 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10306  in
                             (uu____10305, aq))
                    | p::rest ->
                        let uu____10319 = desugar_binding_pat env1 p  in
                        (match uu____10319 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10351)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10366 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10375 =
                               match b with
                               | LetBinder uu____10416 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10485) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10539 =
                                           let uu____10548 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10548, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10539
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10610,uu____10611) ->
                                              let tup2 =
                                                let uu____10613 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10613
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10618 =
                                                  let uu____10625 =
                                                    let uu____10626 =
                                                      let uu____10643 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10646 =
                                                        let uu____10657 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10666 =
                                                          let uu____10677 =
                                                            let uu____10686 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10686
                                                             in
                                                          [uu____10677]  in
                                                        uu____10657 ::
                                                          uu____10666
                                                         in
                                                      (uu____10643,
                                                        uu____10646)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10626
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10625
                                                   in
                                                uu____10618
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10734 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10734
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10785,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10787,pats1)) ->
                                              let tupn =
                                                let uu____10832 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10832
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10845 =
                                                  let uu____10846 =
                                                    let uu____10863 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10866 =
                                                      let uu____10877 =
                                                        let uu____10888 =
                                                          let uu____10897 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10897
                                                           in
                                                        [uu____10888]  in
                                                      FStar_List.append args
                                                        uu____10877
                                                       in
                                                    (uu____10863,
                                                      uu____10866)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10846
                                                   in
                                                mk1 uu____10845  in
                                              let p2 =
                                                let uu____10945 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10945
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10992 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10375 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11084,uu____11085,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11107 =
                let uu____11108 = unparen e  in
                uu____11108.FStar_Parser_AST.tm  in
              match uu____11107 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11118 ->
                  let uu____11119 = desugar_term_aq env e  in
                  (match uu____11119 with
                   | (head1,aq) ->
                       let uu____11132 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11132, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11139 ->
            let rec aux args aqs e =
              let uu____11216 =
                let uu____11217 = unparen e  in
                uu____11217.FStar_Parser_AST.tm  in
              match uu____11216 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11235 = desugar_term_aq env t  in
                  (match uu____11235 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11283 ->
                  let uu____11284 = desugar_term_aq env e  in
                  (match uu____11284 with
                   | (head1,aq) ->
                       let uu____11305 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11305, (join_aqs (aq :: aqs))))
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
            let uu____11368 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11368
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
            let uu____11420 = desugar_term_aq env t  in
            (match uu____11420 with
             | (tm,s) ->
                 let uu____11431 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11431, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11437 =
              let uu____11450 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11450 then desugar_typ_aq else desugar_term_aq  in
            uu____11437 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11517 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11660  ->
                        match uu____11660 with
                        | (attr_opt,(p,def)) ->
                            let uu____11718 = is_app_pattern p  in
                            if uu____11718
                            then
                              let uu____11751 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11751, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11834 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11834, def1)
                               | uu____11879 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11917);
                                           FStar_Parser_AST.prange =
                                             uu____11918;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11967 =
                                            let uu____11988 =
                                              let uu____11993 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11993  in
                                            (uu____11988, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11967, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12085) ->
                                        if top_level
                                        then
                                          let uu____12121 =
                                            let uu____12142 =
                                              let uu____12147 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12147  in
                                            (uu____12142, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12121, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12238 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12271 =
                FStar_List.fold_left
                  (fun uu____12360  ->
                     fun uu____12361  ->
                       match (uu____12360, uu____12361) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12491,uu____12492),uu____12493))
                           ->
                           let uu____12627 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12667 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12667 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12702 =
                                        let uu____12705 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12705 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12702, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12721 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12721 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12627 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12271 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12974 =
                    match uu____12974 with
                    | (attrs_opt,(uu____13014,args,result_t),def) ->
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
                                let uu____13106 = is_comp_type env1 t  in
                                if uu____13106
                                then
                                  ((let uu____13110 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13120 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13120))
                                       in
                                    match uu____13110 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13127 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13130 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13130))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13127
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
                          | uu____13141 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13144 = desugar_term_aq env1 def2  in
                        (match uu____13144 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13166 =
                                     let uu____13167 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13167
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13166
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
                  let uu____13208 =
                    let uu____13225 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13225 FStar_List.unzip  in
                  (match uu____13208 with
                   | (lbs1,aqss) ->
                       let uu____13367 = desugar_term_aq env' body  in
                       (match uu____13367 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13473  ->
                                    fun used_marker  ->
                                      match uu____13473 with
                                      | (_attr_opt,(f,uu____13547,uu____13548),uu____13549)
                                          ->
                                          let uu____13606 =
                                            let uu____13608 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13608  in
                                          if uu____13606
                                          then
                                            let uu____13632 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13650 =
                                                    FStar_Ident.string_of_ident
                                                      x
                                                     in
                                                  let uu____13652 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13650, "Local",
                                                    uu____13652)
                                              | FStar_Util.Inr l ->
                                                  let uu____13657 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13659 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13657, "Global",
                                                    uu____13659)
                                               in
                                            (match uu____13632 with
                                             | (nm,gl,rng) ->
                                                 let uu____13670 =
                                                   let uu____13676 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13676)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13670)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13684 =
                                let uu____13687 =
                                  let uu____13688 =
                                    let uu____13702 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13702)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13688  in
                                FStar_All.pipe_left mk1 uu____13687  in
                              (uu____13684,
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
              let uu____13804 = desugar_term_aq env t1  in
              match uu____13804 with
              | (t11,aq0) ->
                  let uu____13825 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13825 with
                   | (env1,binder,pat1) ->
                       let uu____13855 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13897 = desugar_term_aq env1 t2  in
                             (match uu____13897 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13919 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13919
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13920 =
                                    FStar_All.pipe_left mk1
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13920, aq))
                         | LocalBinder (x,uu____13961) ->
                             let uu____13962 = desugar_term_aq env1 t2  in
                             (match uu____13962 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13984;
                                         FStar_Syntax_Syntax.p = uu____13985;_},uu____13986)::[]
                                        -> body1
                                    | uu____13999 ->
                                        let uu____14002 =
                                          let uu____14009 =
                                            let uu____14010 =
                                              let uu____14033 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14036 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14033, uu____14036)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____14010
                                             in
                                          FStar_Syntax_Syntax.mk uu____14009
                                           in
                                        uu____14002
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14073 =
                                    let uu____14076 =
                                      let uu____14077 =
                                        let uu____14091 =
                                          let uu____14094 =
                                            let uu____14095 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14095]  in
                                          FStar_Syntax_Subst.close
                                            uu____14094 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14091)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14077
                                       in
                                    FStar_All.pipe_left mk1 uu____14076  in
                                  (uu____14073, aq))
                          in
                       (match uu____13855 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14203 = FStar_List.hd lbs  in
            (match uu____14203 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14247 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14247
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____14263 =
                let uu____14264 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14264  in
              mk1 uu____14263  in
            let uu____14265 = desugar_term_aq env t1  in
            (match uu____14265 with
             | (t1',aq1) ->
                 let uu____14276 = desugar_term_aq env t2  in
                 (match uu____14276 with
                  | (t2',aq2) ->
                      let uu____14287 = desugar_term_aq env t3  in
                      (match uu____14287 with
                       | (t3',aq3) ->
                           let uu____14298 =
                             let uu____14299 =
                               let uu____14300 =
                                 let uu____14323 =
                                   let uu____14340 =
                                     let uu____14355 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14355,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14369 =
                                     let uu____14386 =
                                       let uu____14401 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14401,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14386]  in
                                   uu____14340 :: uu____14369  in
                                 (t1', uu____14323)  in
                               FStar_Syntax_Syntax.Tm_match uu____14300  in
                             mk1 uu____14299  in
                           (uu____14298, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14597 =
              match uu____14597 with
              | (pat,wopt,b) ->
                  let uu____14619 = desugar_match_pat env pat  in
                  (match uu____14619 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14650 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14650
                          in
                       let uu____14655 = desugar_term_aq env1 b  in
                       (match uu____14655 with
                        | (b1,aq) ->
                            let uu____14668 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14668, aq)))
               in
            let uu____14673 = desugar_term_aq env e  in
            (match uu____14673 with
             | (e1,aq) ->
                 let uu____14684 =
                   let uu____14715 =
                     let uu____14748 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14748 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14715
                     (fun uu____14966  ->
                        match uu____14966 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14684 with
                  | (brs,aqs) ->
                      let uu____15185 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15185, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15219 =
              let uu____15240 = is_comp_type env t  in
              if uu____15240
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15295 = desugar_term_aq env t  in
                 match uu____15295 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15219 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15387 = desugar_term_aq env e  in
                 (match uu____15387 with
                  | (e1,aq) ->
                      let uu____15398 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15398, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15437,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15480 = FStar_List.hd fields  in
              match uu____15480 with | (f,uu____15492) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15538  ->
                        match uu____15538 with
                        | (g,uu____15545) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15552,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15566 =
                         let uu____15572 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15572)
                          in
                       FStar_Errors.raise_error uu____15566
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
                  let uu____15583 =
                    let uu____15594 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15625  ->
                              match uu____15625 with
                              | (f,uu____15635) ->
                                  let uu____15636 =
                                    let uu____15637 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15637
                                     in
                                  (uu____15636, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15594)  in
                  FStar_Parser_AST.Construct uu____15583
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15655 =
                      let uu____15656 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15656  in
                    FStar_Parser_AST.mk_term uu____15655
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15658 =
                      let uu____15671 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15701  ->
                                match uu____15701 with
                                | (f,uu____15711) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15671)  in
                    FStar_Parser_AST.Record uu____15658  in
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
            let uu____15771 = desugar_term_aq env recterm1  in
            (match uu____15771 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15787;
                         FStar_Syntax_Syntax.vars = uu____15788;_},args)
                      ->
                      let uu____15814 =
                        let uu____15815 =
                          let uu____15816 =
                            let uu____15833 =
                              let uu____15836 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15837 =
                                let uu____15840 =
                                  let uu____15841 =
                                    let uu____15848 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15848)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15841
                                   in
                                FStar_Pervasives_Native.Some uu____15840  in
                              FStar_Syntax_Syntax.fvar uu____15836
                                FStar_Syntax_Syntax.delta_constant
                                uu____15837
                               in
                            (uu____15833, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15816  in
                        FStar_All.pipe_left mk1 uu____15815  in
                      (uu____15814, s)
                  | uu____15877 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            let uu____15880 =
              FStar_Syntax_DsEnv.fail_or env
                (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
               in
            (match uu____15880 with
             | (constrname,is_rec) ->
                 let uu____15899 = desugar_term_aq env e  in
                 (match uu____15899 with
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
                      let uu____15919 =
                        let uu____15920 =
                          let uu____15921 =
                            let uu____15938 =
                              let uu____15941 =
                                let uu____15942 = FStar_Ident.range_of_lid f
                                   in
                                FStar_Ident.set_lid_range projname
                                  uu____15942
                                 in
                              FStar_Syntax_Syntax.fvar uu____15941
                                (FStar_Syntax_Syntax.Delta_equational_at_level
                                   Prims.int_one) qual
                               in
                            let uu____15944 =
                              let uu____15955 = FStar_Syntax_Syntax.as_arg e1
                                 in
                              [uu____15955]  in
                            (uu____15938, uu____15944)  in
                          FStar_Syntax_Syntax.Tm_app uu____15921  in
                        FStar_All.pipe_left mk1 uu____15920  in
                      (uu____15919, s)))
        | FStar_Parser_AST.NamedTyp (n1,e) ->
            ((let uu____15995 = FStar_Ident.range_of_id n1  in
              FStar_Errors.log_issue uu____15995
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____16006 =
              let uu____16007 = FStar_Syntax_Subst.compress tm  in
              uu____16007.FStar_Syntax_Syntax.n  in
            (match uu____16006 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16015 =
                   let uu___2115_16016 =
                     let uu____16017 =
                       let uu____16019 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16019  in
                     FStar_Syntax_Util.exp_string uu____16017  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2115_16016.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2115_16016.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16015, noaqs)
             | uu____16020 ->
                 let uu____16021 =
                   let uu____16027 =
                     let uu____16029 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16029
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16027)  in
                 FStar_Errors.raise_error uu____16021
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16038 = desugar_term_aq env e  in
            (match uu____16038 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16050 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16050, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16055 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16056 =
              let uu____16057 =
                let uu____16064 = desugar_term env e  in (bv, uu____16064)
                 in
              [uu____16057]  in
            (uu____16055, uu____16056)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16089 =
              let uu____16090 =
                let uu____16091 =
                  let uu____16098 = desugar_term env e  in (uu____16098, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16091  in
              FStar_All.pipe_left mk1 uu____16090  in
            (uu____16089, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16127 -> false  in
              let uu____16129 =
                let uu____16130 = unparen rel1  in
                uu____16130.FStar_Parser_AST.tm  in
              match uu____16129 with
              | FStar_Parser_AST.Op (id1,uu____16133) ->
                  let uu____16138 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id1
                     in
                  (match uu____16138 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16146 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16146 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id1 ->
                  let uu____16157 = FStar_Syntax_DsEnv.try_lookup_id env id1
                     in
                  (match uu____16157 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16163 -> false  in
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
              let uu____16184 =
                let uu____16185 =
                  let uu____16192 =
                    let uu____16193 =
                      let uu____16194 =
                        let uu____16203 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16216 =
                          let uu____16217 =
                            let uu____16218 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16218  in
                          FStar_Parser_AST.mk_term uu____16217
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16203, uu____16216,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16194  in
                    FStar_Parser_AST.mk_term uu____16193
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16192)  in
                FStar_Parser_AST.Abs uu____16185  in
              FStar_Parser_AST.mk_term uu____16184
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
              let uu____16239 = FStar_List.last steps  in
              match uu____16239 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16242,uu____16243,last_expr)) -> last_expr
              | uu____16245 -> failwith "impossible: no last_expr on calc"
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
            let uu____16273 =
              FStar_List.fold_left
                (fun uu____16291  ->
                   fun uu____16292  ->
                     match (uu____16291, uu____16292) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16315 = is_impl rel2  in
                           if uu____16315
                           then
                             let uu____16318 =
                               let uu____16325 =
                                 let uu____16330 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16330, FStar_Parser_AST.Nothing)  in
                               [uu____16325]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16318 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16342 =
                             let uu____16349 =
                               let uu____16356 =
                                 let uu____16363 =
                                   let uu____16370 =
                                     let uu____16375 = eta_and_annot rel2  in
                                     (uu____16375, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16376 =
                                     let uu____16383 =
                                       let uu____16390 =
                                         let uu____16395 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16395,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16396 =
                                         let uu____16403 =
                                           let uu____16408 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16408,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16403]  in
                                       uu____16390 :: uu____16396  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16383
                                      in
                                   uu____16370 :: uu____16376  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16363
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16356
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16349
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16342
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16273 with
             | (e1,uu____16446) ->
                 let e2 =
                   let uu____16448 =
                     let uu____16455 =
                       let uu____16462 =
                         let uu____16469 =
                           let uu____16474 = FStar_Parser_AST.thunk e1  in
                           (uu____16474, FStar_Parser_AST.Nothing)  in
                         [uu____16469]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16462  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16455  in
                   FStar_Parser_AST.mkApp finish1 uu____16448
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16491 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16492 = desugar_formula env top  in
            (uu____16492, noaqs)
        | uu____16493 ->
            let uu____16494 =
              let uu____16500 =
                let uu____16502 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16502  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16500)  in
            FStar_Errors.raise_error uu____16494 top.FStar_Parser_AST.range

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
           (fun uu____16546  ->
              match uu____16546 with
              | (a,imp) ->
                  let uu____16559 = desugar_term env a  in
                  arg_withimp_e imp uu____16559))

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
          let is_requires uu____16596 =
            match uu____16596 with
            | (t1,uu____16603) ->
                let uu____16604 =
                  let uu____16605 = unparen t1  in
                  uu____16605.FStar_Parser_AST.tm  in
                (match uu____16604 with
                 | FStar_Parser_AST.Requires uu____16607 -> true
                 | uu____16616 -> false)
             in
          let is_ensures uu____16628 =
            match uu____16628 with
            | (t1,uu____16635) ->
                let uu____16636 =
                  let uu____16637 = unparen t1  in
                  uu____16637.FStar_Parser_AST.tm  in
                (match uu____16636 with
                 | FStar_Parser_AST.Ensures uu____16639 -> true
                 | uu____16648 -> false)
             in
          let is_app head1 uu____16666 =
            match uu____16666 with
            | (t1,uu____16674) ->
                let uu____16675 =
                  let uu____16676 = unparen t1  in
                  uu____16676.FStar_Parser_AST.tm  in
                (match uu____16675 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16679;
                        FStar_Parser_AST.level = uu____16680;_},uu____16681,uu____16682)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____16684 -> false)
             in
          let is_smt_pat uu____16696 =
            match uu____16696 with
            | (t1,uu____16703) ->
                let uu____16704 =
                  let uu____16705 = unparen t1  in
                  uu____16705.FStar_Parser_AST.tm  in
                (match uu____16704 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16709);
                               FStar_Parser_AST.range = uu____16710;
                               FStar_Parser_AST.level = uu____16711;_},uu____16712)::uu____16713::[])
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
                               FStar_Parser_AST.range = uu____16762;
                               FStar_Parser_AST.level = uu____16763;_},uu____16764)::uu____16765::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16798 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16833 = head_and_args t1  in
            match uu____16833 with
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
                     let thunk_ens uu____16926 =
                       match uu____16926 with
                       | (e,i) ->
                           let uu____16937 = FStar_Parser_AST.thunk e  in
                           (uu____16937, i)
                        in
                     let fail_lemma uu____16949 =
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
                           let uu____17055 =
                             let uu____17062 =
                               let uu____17069 = thunk_ens ens  in
                               [uu____17069; nil_pat]  in
                             req_true :: uu____17062  in
                           unit_tm :: uu____17055
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17116 =
                             let uu____17123 =
                               let uu____17130 = thunk_ens ens  in
                               [uu____17130; nil_pat]  in
                             req :: uu____17123  in
                           unit_tm :: uu____17116
                       | ens::smtpat::[] when
                           (((let uu____17179 = is_requires ens  in
                              Prims.op_Negation uu____17179) &&
                               (let uu____17182 = is_smt_pat ens  in
                                Prims.op_Negation uu____17182))
                              &&
                              (let uu____17185 = is_decreases ens  in
                               Prims.op_Negation uu____17185))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17187 =
                             let uu____17194 =
                               let uu____17201 = thunk_ens ens  in
                               [uu____17201; smtpat]  in
                             req_true :: uu____17194  in
                           unit_tm :: uu____17187
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17248 =
                             let uu____17255 =
                               let uu____17262 = thunk_ens ens  in
                               [uu____17262; nil_pat; dec]  in
                             req_true :: uu____17255  in
                           unit_tm :: uu____17248
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17322 =
                             let uu____17329 =
                               let uu____17336 = thunk_ens ens  in
                               [uu____17336; smtpat; dec]  in
                             req_true :: uu____17329  in
                           unit_tm :: uu____17322
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17396 =
                             let uu____17403 =
                               let uu____17410 = thunk_ens ens  in
                               [uu____17410; nil_pat; dec]  in
                             req :: uu____17403  in
                           unit_tm :: uu____17396
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17470 =
                             let uu____17477 =
                               let uu____17484 = thunk_ens ens  in
                               [uu____17484; smtpat]  in
                             req :: uu____17477  in
                           unit_tm :: uu____17470
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17549 =
                             let uu____17556 =
                               let uu____17563 = thunk_ens ens  in
                               [uu____17563; dec; smtpat]  in
                             req :: uu____17556  in
                           unit_tm :: uu____17549
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17625 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17625, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17653 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17653
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____17656 =
                       let uu____17663 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17663, [])  in
                     (uu____17656, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17681 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17681
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____17684 =
                       let uu____17691 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17691, [])  in
                     (uu____17684, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17713 =
                       let uu____17720 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17720, [])  in
                     (uu____17713, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17743 when allow_type_promotion ->
                     let default_effect =
                       let uu____17745 = FStar_Options.ml_ish ()  in
                       if uu____17745
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17751 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17751
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17758 =
                       let uu____17765 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17765, [])  in
                     (uu____17758, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17788 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17807 = pre_process_comp_typ t  in
          match uu____17807 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17859 =
                    let uu____17865 =
                      let uu____17867 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17867
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17865)
                     in
                  fail1 uu____17859)
               else ();
               (let is_universe uu____17883 =
                  match uu____17883 with
                  | (uu____17889,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17891 = FStar_Util.take is_universe args  in
                match uu____17891 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17950  ->
                           match uu____17950 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17957 =
                      let uu____17972 = FStar_List.hd args1  in
                      let uu____17981 = FStar_List.tl args1  in
                      (uu____17972, uu____17981)  in
                    (match uu____17957 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18036 =
                           let is_decrease uu____18075 =
                             match uu____18075 with
                             | (t1,uu____18086) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18097;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18098;_},uu____18099::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18138 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18036 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18255  ->
                                        match uu____18255 with
                                        | (t1,uu____18265) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18274,(arg,uu____18276)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18315 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18336 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18348 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18348
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18355 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18355
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18365 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18365
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18372 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18372
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18379 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18379
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18386 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18386
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18407 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18407
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
                                                    let uu____18498 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18498
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
                                              | uu____18519 -> pat  in
                                            let uu____18520 =
                                              let uu____18531 =
                                                let uu____18542 =
                                                  let uu____18551 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18551, aq)  in
                                                [uu____18542]  in
                                              ens :: uu____18531  in
                                            req :: uu____18520
                                        | uu____18592 -> rest2
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
        let uu___2440_18627 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2440_18627.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2440_18627.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2447_18681 = b  in
             {
               FStar_Parser_AST.b = (uu___2447_18681.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2447_18681.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2447_18681.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18710 body1 =
          match uu____18710 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18756::uu____18757) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18775 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2466_18802 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2466_18802.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2466_18802.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18865 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18865))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18896 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18896 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2479_18906 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2479_18906.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2479_18906.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18912 =
                     let uu____18915 =
                       let uu____18916 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18916]  in
                     no_annot_abs uu____18915 body2  in
                   FStar_All.pipe_left setpos uu____18912  in
                 let uu____18937 =
                   let uu____18938 =
                     let uu____18955 =
                       let uu____18958 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18958
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____18960 =
                       let uu____18971 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18971]  in
                     (uu____18955, uu____18960)  in
                   FStar_Syntax_Syntax.Tm_app uu____18938  in
                 FStar_All.pipe_left mk1 uu____18937)
        | uu____19010 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19075 = q (rest, pats, body)  in
              let uu____19078 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19075 uu____19078
                FStar_Parser_AST.Formula
               in
            let uu____19079 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19079 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19090 -> failwith "impossible"  in
      let uu____19094 =
        let uu____19095 = unparen f  in uu____19095.FStar_Parser_AST.tm  in
      match uu____19094 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19108,uu____19109) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19133,uu____19134) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19190 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19190
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19234 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19234
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19298 -> desugar_term env f

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
          let uu____19309 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19309)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19314 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19314)
      | FStar_Parser_AST.TVariable x ->
          let uu____19318 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____19318)
      | FStar_Parser_AST.NoName t ->
          let uu____19322 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19322)
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
      fun uu___11_19330  ->
        match uu___11_19330 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19352 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19352, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19369 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19369 with
             | (env1,a1) ->
                 let uu____19386 =
                   let uu____19393 = trans_aqual env1 imp  in
                   ((let uu___2579_19399 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2579_19399.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2579_19399.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19393)
                    in
                 (uu____19386, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19407  ->
      match uu___12_19407 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19411 =
            let uu____19412 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19412  in
          FStar_Pervasives_Native.Some uu____19411
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19440 =
        FStar_List.fold_left
          (fun uu____19473  ->
             fun b  ->
               match uu____19473 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2597_19517 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2597_19517.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2597_19517.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2597_19517.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19532 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19532 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2607_19550 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2607_19550.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2607_19550.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19551 =
                               let uu____19558 =
                                 let uu____19563 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19563)  in
                               uu____19558 :: out  in
                             (env2, uu____19551))
                    | uu____19574 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19440 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19662 =
          let uu____19663 = unparen t  in uu____19663.FStar_Parser_AST.tm  in
        match uu____19662 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____19664; FStar_Ident.ident = uu____19665;
              FStar_Ident.nsstr = uu____19666; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____19671 ->
            let uu____19672 =
              let uu____19678 =
                let uu____19680 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19680  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19678)  in
            FStar_Errors.raise_error uu____19672 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19697) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19699) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19702 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19720 = binder_ident b  in
         FStar_Common.list_of_option uu____19720) bs
  
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
               (fun uu___13_19757  ->
                  match uu___13_19757 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19762 -> false))
           in
        let quals2 q =
          let uu____19776 =
            (let uu____19780 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19780) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19776
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19797 = FStar_Ident.range_of_lid disc_name  in
                let uu____19798 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19797;
                  FStar_Syntax_Syntax.sigquals = uu____19798;
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
            let uu____19838 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19876  ->
                        match uu____19876 with
                        | (x,uu____19887) ->
                            let uu____19892 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19892 with
                             | (field_name,uu____19900) ->
                                 let only_decl =
                                   ((let uu____19905 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19905)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19907 =
                                        let uu____19909 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19909.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19907)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19927 =
                                       FStar_List.filter
                                         (fun uu___14_19931  ->
                                            match uu___14_19931 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19934 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19927
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___15_19949  ->
                                             match uu___15_19949 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19954 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19957 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19957;
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
                                      let uu____19964 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19964
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one
                                       in
                                    let lb =
                                      let uu____19975 =
                                        let uu____19980 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19980  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19975;
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
                                      let uu____19984 =
                                        let uu____19985 =
                                          let uu____19992 =
                                            let uu____19995 =
                                              let uu____19996 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19996
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19995]  in
                                          ((false, [lb]), uu____19992)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19985
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19984;
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
            FStar_All.pipe_right uu____19838 FStar_List.flatten
  
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
            (lid,uu____20045,t,uu____20047,n1,uu____20049) when
            let uu____20056 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20056 ->
            let uu____20058 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20058 with
             | (formals,uu____20076) ->
                 (match formals with
                  | [] -> []
                  | uu____20105 ->
                      let filter_records uu___16_20121 =
                        match uu___16_20121 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20124,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20136 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20138 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20138 with
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
                      let uu____20150 = FStar_Util.first_N n1 formals  in
                      (match uu____20150 with
                       | (uu____20179,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20213 -> []
  
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
                        let uu____20307 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20307
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20331 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20331
                        then
                          let uu____20337 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20337
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20341 =
                          let uu____20346 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20346  in
                        let uu____20347 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20353 =
                              let uu____20356 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20356  in
                            FStar_Syntax_Util.arrow typars uu____20353
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20361 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20341;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20347;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20361;
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
          let tycon_id uu___17_20415 =
            match uu___17_20415 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____20417,uu____20418) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____20428,uu____20429,uu____20430) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____20440,uu____20441,uu____20442) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____20464,uu____20465,uu____20466) -> id1
             in
          let binder_to_term1 b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20504) ->
                let uu____20505 =
                  let uu____20506 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20506  in
                FStar_Parser_AST.mk_term uu____20505 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20508 =
                  let uu____20509 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20509  in
                FStar_Parser_AST.mk_term uu____20508 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20511) ->
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
              | uu____20542 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20550 =
                     let uu____20551 =
                       let uu____20558 = binder_to_term1 b  in
                       (out, uu____20558, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20551  in
                   FStar_Parser_AST.mk_term uu____20550
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20570 =
            match uu___18_20570 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____20614  ->
                       match uu____20614 with
                       | (x,t) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20622 =
                    let uu____20623 =
                      let uu____20624 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____20624  in
                    FStar_Parser_AST.mk_term uu____20623
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20622 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____20631 = binder_idents parms  in id1 ::
                    uu____20631
                   in
                (FStar_List.iter
                   (fun uu____20644  ->
                      match uu____20644 with
                      | (f,uu____20650) ->
                          let uu____20651 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____20651
                          then
                            let uu____20656 =
                              let uu____20662 =
                                let uu____20664 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20664
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20662)
                               in
                            FStar_Errors.raise_error uu____20656
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____20670 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20670)))
            | uu____20724 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20764 =
            match uu___19_20764 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20788 = typars_of_binders _env binders  in
                (match uu____20788 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20824 =
                         let uu____20825 =
                           let uu____20826 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20826  in
                         FStar_Parser_AST.mk_term uu____20825
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20824 binders  in
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
                     let uu____20835 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20835 with
                      | (_env1,uu____20852) ->
                          let uu____20859 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id1 FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20859 with
                           | (_env2,uu____20876) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20883 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20926 =
              FStar_List.fold_left
                (fun uu____20960  ->
                   fun uu____20961  ->
                     match (uu____20960, uu____20961) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21030 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21030 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20926 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21121 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____21121
                | uu____21122 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____21130 = desugar_abstract_tc quals env [] tc  in
              (match uu____21130 with
               | (uu____21143,uu____21144,se,uu____21146) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21149,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21168 =
                                 let uu____21170 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21170  in
                               if uu____21168
                               then
                                 let uu____21173 =
                                   let uu____21179 =
                                     let uu____21181 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21181
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21179)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21173
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
                           | uu____21194 ->
                               let uu____21195 =
                                 let uu____21202 =
                                   let uu____21203 =
                                     let uu____21218 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21218)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21203
                                    in
                                 FStar_Syntax_Syntax.mk uu____21202  in
                               uu____21195 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2890_21231 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2890_21231.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2890_21231.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2890_21231.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2890_21231.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21232 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____21247 = typars_of_binders env binders  in
              (match uu____21247 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21281 =
                           FStar_Util.for_some
                             (fun uu___20_21284  ->
                                match uu___20_21284 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21287 -> false) quals
                            in
                         if uu____21281
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21295 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21295
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21300 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21306  ->
                               match uu___21_21306 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21309 -> false))
                        in
                     if uu____21300
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____21323 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21323
                     then
                       let uu____21329 =
                         let uu____21336 =
                           let uu____21337 = unparen t  in
                           uu____21337.FStar_Parser_AST.tm  in
                         match uu____21336 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____21358 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21388)::args_rev ->
                                   let uu____21400 =
                                     let uu____21401 = unparen last_arg  in
                                     uu____21401.FStar_Parser_AST.tm  in
                                   (match uu____21400 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21429 -> ([], args))
                               | uu____21438 -> ([], args)  in
                             (match uu____21358 with
                              | (cattributes,args1) ->
                                  let uu____21477 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21477))
                         | uu____21488 -> (t, [])  in
                       match uu____21329 with
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
                                  (fun uu___22_21511  ->
                                     match uu___22_21511 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21514 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21522)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21542 = tycon_record_as_variant trec  in
              (match uu____21542 with
               | (t,fs) ->
                   let uu____21559 =
                     let uu____21562 =
                       let uu____21563 =
                         let uu____21572 =
                           let uu____21575 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21575  in
                         (uu____21572, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21563  in
                     uu____21562 :: quals  in
                   desugar_tycon env d uu____21559 [t])
          | uu____21580::uu____21581 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21739 = et  in
                match uu____21739 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21949 ->
                         let trec = tc  in
                         let uu____21969 = tycon_record_as_variant trec  in
                         (match uu____21969 with
                          | (t,fs) ->
                              let uu____22025 =
                                let uu____22028 =
                                  let uu____22029 =
                                    let uu____22038 =
                                      let uu____22041 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22041  in
                                    (uu____22038, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22029
                                   in
                                uu____22028 :: quals1  in
                              collect_tcs uu____22025 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____22119 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22119 with
                          | (env2,uu____22176,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____22313 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22313 with
                          | (env2,uu____22370,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22486 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22532 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22532 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_22984  ->
                             match uu___24_22984 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____23038,uu____23039);
                                    FStar_Syntax_Syntax.sigrng = uu____23040;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23041;
                                    FStar_Syntax_Syntax.sigmeta = uu____23042;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23043;
                                    FStar_Syntax_Syntax.sigopts = uu____23044;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23106 =
                                     typars_of_binders env1 binders  in
                                   match uu____23106 with
                                   | (env2,tpars1) ->
                                       let uu____23133 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23133 with
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
                                 let uu____23162 =
                                   let uu____23173 =
                                     mk_typ_abbrev env1 d id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ([], uu____23173)  in
                                 [uu____23162]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____23209);
                                    FStar_Syntax_Syntax.sigrng = uu____23210;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23212;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23213;
                                    FStar_Syntax_Syntax.sigopts = uu____23214;_},constrs,tconstr,quals1)
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
                                 let uu____23305 = push_tparams env1 tpars
                                    in
                                 (match uu____23305 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23364  ->
                                             match uu____23364 with
                                             | (x,uu____23376) ->
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
                                        let uu____23387 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23387
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23410 =
                                        let uu____23429 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23506  ->
                                                  match uu____23506 with
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
                                                        let uu____23549 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23549
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
                                                                uu___23_23560
                                                                 ->
                                                                match uu___23_23560
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23572
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23580 =
                                                        let uu____23591 =
                                                          let uu____23592 =
                                                            let uu____23593 =
                                                              let uu____23609
                                                                =
                                                                let uu____23610
                                                                  =
                                                                  let uu____23613
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23613
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23610
                                                                 in
                                                              (name, univs1,
                                                                uu____23609,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23593
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23592;
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
                                                        (tps, uu____23591)
                                                         in
                                                      (name, uu____23580)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23429
                                         in
                                      (match uu____23410 with
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
                             | uu____23745 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23826  ->
                             match uu____23826 with | (uu____23837,se) -> se))
                      in
                   let uu____23851 =
                     let uu____23858 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23858 rng
                      in
                   (match uu____23851 with
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
                               (fun uu____23903  ->
                                  match uu____23903 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23951,tps,k,uu____23954,constrs)
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
                                      let uu____23975 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23990 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____24007,uu____24008,uu____24009,uu____24010,uu____24011)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24018
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23990
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24022 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24029  ->
                                                          match uu___25_24029
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24031 ->
                                                              true
                                                          | uu____24041 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24022))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23975
                                  | uu____24043 -> []))
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
      let uu____24080 =
        FStar_List.fold_left
          (fun uu____24115  ->
             fun b  ->
               match uu____24115 with
               | (env1,binders1) ->
                   let uu____24159 = desugar_binder env1 b  in
                   (match uu____24159 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24182 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24182 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24235 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24080 with
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
          let uu____24339 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24346  ->
                    match uu___26_24346 with
                    | FStar_Syntax_Syntax.Reflectable uu____24348 -> true
                    | uu____24350 -> false))
             in
          if uu____24339
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24355 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24355
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
        let warn1 uu____24406 =
          if warn
          then
            let uu____24408 =
              let uu____24414 =
                let uu____24416 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24416
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24414)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24408
          else ()  in
        let uu____24422 = FStar_Syntax_Util.head_and_args at  in
        match uu____24422 with
        | (hd1,args) ->
            let uu____24475 =
              let uu____24476 = FStar_Syntax_Subst.compress hd1  in
              uu____24476.FStar_Syntax_Syntax.n  in
            (match uu____24475 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24520)::[] ->
                      let uu____24545 =
                        let uu____24550 =
                          let uu____24559 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24559 a1  in
                        uu____24550 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24545 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24582 =
                             let uu____24588 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24588  in
                           (uu____24582, true)
                       | uu____24603 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24619 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24641 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24758 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24758 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24807 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24807 with | (res1,uu____24829) -> rebind res1 true)
  
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
        | uu____25156 -> FStar_Pervasives_Native.None  in
      FStar_List.fold_right
        (fun at  ->
           fun acc  ->
             let uu____25214 = get_fail_attr1 warn at  in
             comb uu____25214 acc) ats FStar_Pervasives_Native.None
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____25249 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____25249 with
        | FStar_Pervasives_Native.None  ->
            let uu____25252 =
              let uu____25258 =
                let uu____25260 =
                  let uu____25262 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____25262 " not found"  in
                Prims.op_Hat "Effect name " uu____25260  in
              (FStar_Errors.Fatal_EffectNotFound, uu____25258)  in
            FStar_Errors.raise_error uu____25252 r
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
                    let uu____25418 = desugar_binders monad_env eff_binders
                       in
                    match uu____25418 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25457 =
                            let uu____25466 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25466  in
                          FStar_List.length uu____25457  in
                        (if is_layered1 && (num_indices <= Prims.int_one)
                         then
                           (let uu____25500 =
                              let uu____25506 =
                                let uu____25508 =
                                  let uu____25510 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25510
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25508  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25506)
                               in
                            FStar_Errors.raise_error uu____25500
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
                                (uu____25578,uu____25579,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25581,uu____25582,uu____25583))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25598 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25601 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25613 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25613 mandatory_members)
                              eff_decls
                             in
                          match uu____25601 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25632 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25661  ->
                                        fun decl  ->
                                          match uu____25661 with
                                          | (env2,out) ->
                                              let uu____25681 =
                                                desugar_decl env2 decl  in
                                              (match uu____25681 with
                                               | (env3,ses) ->
                                                   let uu____25694 =
                                                     let uu____25697 =
                                                       FStar_List.hd ses  in
                                                     uu____25697 :: out  in
                                                   (env3, uu____25694)))
                                     (env1, []))
                                 in
                              (match uu____25632 with
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
                                                 (uu____25743,uu____25744,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25747,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25748,(def,uu____25750)::
                                                        (cps_type,uu____25752)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25753;
                                                     FStar_Parser_AST.level =
                                                       uu____25754;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25787 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25787 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25819 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25820 =
                                                        let uu____25821 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25821
                                                         in
                                                      let uu____25828 =
                                                        let uu____25829 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25829
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25819;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25820;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25828
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25836,uu____25837,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25840,defn))::[])
                                                 when for_free || is_layered1
                                                 ->
                                                 let uu____25856 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25856 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25888 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25889 =
                                                        let uu____25890 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25890
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25888;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25889;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25897 ->
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
                                       let uu____25916 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25916
                                        in
                                     let uu____25918 =
                                       let uu____25919 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25919
                                        in
                                     ([], uu____25918)  in
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
                                       let uu____25941 =
                                         let uu____25942 =
                                           let uu____25945 = lookup1 "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25945
                                            in
                                         let uu____25947 =
                                           let uu____25950 = lookup1 "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25950
                                            in
                                         let uu____25952 =
                                           let uu____25955 = lookup1 "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25955
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
                                             uu____25942;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25947;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25952
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25941
                                     else
                                       if is_layered1
                                       then
                                         (let to_comb uu____25989 =
                                            match uu____25989 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____26036 =
                                            let uu____26037 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____26039 =
                                              let uu____26044 =
                                                lookup1 "repr"  in
                                              FStar_All.pipe_right
                                                uu____26044 to_comb
                                               in
                                            let uu____26062 =
                                              let uu____26067 =
                                                lookup1 "return"  in
                                              FStar_All.pipe_right
                                                uu____26067 to_comb
                                               in
                                            let uu____26085 =
                                              let uu____26090 =
                                                lookup1 "bind"  in
                                              FStar_All.pipe_right
                                                uu____26090 to_comb
                                               in
                                            let uu____26108 =
                                              let uu____26113 =
                                                lookup1 "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____26113 to_comb
                                               in
                                            let uu____26131 =
                                              let uu____26136 =
                                                lookup1 "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____26136 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____26037;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____26039;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____26062;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____26085;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____26108;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____26131
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____26036)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_26159  ->
                                                 match uu___27_26159 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____26162 -> true
                                                 | uu____26164 -> false)
                                              qualifiers
                                             in
                                          let uu____26166 =
                                            let uu____26167 =
                                              lookup1 "return_wp"  in
                                            let uu____26169 =
                                              lookup1 "bind_wp"  in
                                            let uu____26171 =
                                              lookup1 "stronger"  in
                                            let uu____26173 =
                                              lookup1 "if_then_else"  in
                                            let uu____26175 =
                                              lookup1 "ite_wp"  in
                                            let uu____26177 =
                                              lookup1 "close_wp"  in
                                            let uu____26179 =
                                              lookup1 "trivial"  in
                                            let uu____26181 =
                                              if rr
                                              then
                                                let uu____26187 =
                                                  lookup1 "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26187
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26191 =
                                              if rr
                                              then
                                                let uu____26197 =
                                                  lookup1 "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26197
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____26201 =
                                              if rr
                                              then
                                                let uu____26207 =
                                                  lookup1 "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____26207
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____26167;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____26169;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____26171;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____26173;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____26175;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____26177;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____26179;
                                              FStar_Syntax_Syntax.repr =
                                                uu____26181;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____26191;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____26201
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____26166)
                                      in
                                   let sigel =
                                     let uu____26212 =
                                       let uu____26213 =
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
                                           uu____26213
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____26212
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
                                               let uu____26230 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____26230) env3)
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
                let uu____26253 = desugar_binders env1 eff_binders  in
                match uu____26253 with
                | (env2,binders) ->
                    let uu____26290 =
                      let uu____26301 = head_and_args defn  in
                      match uu____26301 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____26338 ->
                                let uu____26339 =
                                  let uu____26345 =
                                    let uu____26347 =
                                      let uu____26349 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____26349 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____26347  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____26345)
                                   in
                                FStar_Errors.raise_error uu____26339
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____26355 =
                            match FStar_List.rev args with
                            | (last_arg,uu____26385)::args_rev ->
                                let uu____26397 =
                                  let uu____26398 = unparen last_arg  in
                                  uu____26398.FStar_Parser_AST.tm  in
                                (match uu____26397 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____26426 -> ([], args))
                            | uu____26435 -> ([], args)  in
                          (match uu____26355 with
                           | (cattributes,args1) ->
                               let uu____26478 = desugar_args env2 args1  in
                               let uu____26479 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26478, uu____26479))
                       in
                    (match uu____26290 with
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
                          (let uu____26519 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26519 with
                           | (ed_binders,uu____26533,ed_binders_opening) ->
                               let sub' shift_n uu____26552 =
                                 match uu____26552 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26567 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26567 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26571 =
                                       let uu____26572 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26572)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26571
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26593 =
                                   sub1 ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26594 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub1 ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26595 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26611 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26612 =
                                          let uu____26613 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26613
                                           in
                                        let uu____26628 =
                                          let uu____26629 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26629
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26611;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26612;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26628
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
                                     uu____26593;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26594;
                                   FStar_Syntax_Syntax.actions = uu____26595;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26645 =
                                   let uu____26648 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26648 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26645;
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
                                           let uu____26663 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26663) env3)
                                  in
                               let env5 =
                                 let uu____26665 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26665
                                 then
                                   let reflect_lid =
                                     let uu____26672 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26672
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
             let uu____26705 = get_fail_attr1 false at  in
             FStar_Option.isNone uu____26705) ats
         in
      let env0 =
        let uu____26726 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26726 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26741 =
        let uu____26748 = get_fail_attr false attrs  in
        match uu____26748 with
        | FStar_Pervasives_Native.Some (expected_errs,lax1) ->
            let d1 =
              let uu___3445_26785 = d  in
              {
                FStar_Parser_AST.d = (uu___3445_26785.FStar_Parser_AST.d);
                FStar_Parser_AST.drange =
                  (uu___3445_26785.FStar_Parser_AST.drange);
                FStar_Parser_AST.quals =
                  (uu___3445_26785.FStar_Parser_AST.quals);
                FStar_Parser_AST.attrs = []
              }  in
            let uu____26786 =
              FStar_Errors.catch_errors
                (fun uu____26804  ->
                   FStar_Options.with_saved_options
                     (fun uu____26810  -> desugar_decl_noattrs env d1))
               in
            (match uu____26786 with
             | (errs,r) ->
                 (match (errs, r) with
                  | ([],FStar_Pervasives_Native.Some (env1,ses)) ->
                      let ses1 =
                        FStar_List.map
                          (fun se  ->
                             let uu___3460_26870 = se  in
                             let uu____26871 = no_fail_attrs attrs  in
                             {
                               FStar_Syntax_Syntax.sigel =
                                 (uu___3460_26870.FStar_Syntax_Syntax.sigel);
                               FStar_Syntax_Syntax.sigrng =
                                 (uu___3460_26870.FStar_Syntax_Syntax.sigrng);
                               FStar_Syntax_Syntax.sigquals =
                                 (uu___3460_26870.FStar_Syntax_Syntax.sigquals);
                               FStar_Syntax_Syntax.sigmeta =
                                 (uu___3460_26870.FStar_Syntax_Syntax.sigmeta);
                               FStar_Syntax_Syntax.sigattrs = uu____26871;
                               FStar_Syntax_Syntax.sigopts =
                                 (uu___3460_26870.FStar_Syntax_Syntax.sigopts)
                             }) ses
                         in
                      let se =
                        {
                          FStar_Syntax_Syntax.sigel =
                            (FStar_Syntax_Syntax.Sig_fail
                               (expected_errs, lax1, ses1));
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
                        (let uu____26924 =
                           FStar_Errors.find_multiset_discrepancy
                             expected_errs errnos
                            in
                         match uu____26924 with
                         | FStar_Pervasives_Native.None  -> (env0, [])
                         | FStar_Pervasives_Native.Some (e,n1,n2) ->
                             (FStar_List.iter FStar_Errors.print_issue errs1;
                              (let uu____26973 =
                                 let uu____26979 =
                                   let uu____26981 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int expected_errs
                                      in
                                   let uu____26984 =
                                     FStar_Common.string_of_list
                                       FStar_Util.string_of_int errnos
                                      in
                                   let uu____26987 =
                                     FStar_Util.string_of_int e  in
                                   let uu____26989 =
                                     FStar_Util.string_of_int n2  in
                                   let uu____26991 =
                                     FStar_Util.string_of_int n1  in
                                   FStar_Util.format5
                                     "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                     uu____26981 uu____26984 uu____26987
                                     uu____26989 uu____26991
                                    in
                                 (FStar_Errors.Error_DidNotFail, uu____26979)
                                  in
                               FStar_Errors.log_issue
                                 d1.FStar_Parser_AST.drange uu____26973);
                              (env0, [])))))
        | FStar_Pervasives_Native.None  -> desugar_decl_noattrs env d  in
      match uu____26741 with
      | (env1,sigelts) ->
          let rec val_attrs ses =
            match ses with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____27029;
                FStar_Syntax_Syntax.sigrng = uu____27030;
                FStar_Syntax_Syntax.sigquals = uu____27031;
                FStar_Syntax_Syntax.sigmeta = uu____27032;
                FStar_Syntax_Syntax.sigattrs = uu____27033;
                FStar_Syntax_Syntax.sigopts = uu____27034;_}::[] ->
                let uu____27047 =
                  let uu____27050 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27050  in
                FStar_All.pipe_right uu____27047
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27058 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27058))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____27071;
                FStar_Syntax_Syntax.sigrng = uu____27072;
                FStar_Syntax_Syntax.sigquals = uu____27073;
                FStar_Syntax_Syntax.sigmeta = uu____27074;
                FStar_Syntax_Syntax.sigattrs = uu____27075;
                FStar_Syntax_Syntax.sigopts = uu____27076;_}::uu____27077 ->
                let uu____27102 =
                  let uu____27105 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____27105  in
                FStar_All.pipe_right uu____27102
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____27113 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____27113))
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_fail
                  (_errs,_lax,ses1);
                FStar_Syntax_Syntax.sigrng = uu____27129;
                FStar_Syntax_Syntax.sigquals = uu____27130;
                FStar_Syntax_Syntax.sigmeta = uu____27131;
                FStar_Syntax_Syntax.sigattrs = uu____27132;
                FStar_Syntax_Syntax.sigopts = uu____27133;_}::[] ->
                FStar_List.collect (fun se  -> val_attrs [se]) ses1
            | uu____27154 -> []  in
          let attrs1 =
            let uu____27160 = val_attrs sigelts  in
            FStar_List.append attrs uu____27160  in
          let uu____27163 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3520_27167 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3520_27167.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3520_27167.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3520_27167.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3520_27167.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3520_27167.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____27163)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____27174 = desugar_decl_aux env d  in
      match uu____27174 with
      | (env1,ses) ->
          let uu____27185 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____27185)

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
          let uu____27217 = FStar_Syntax_DsEnv.iface env  in
          if uu____27217
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____27232 =
               let uu____27234 =
                 let uu____27236 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____27237 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____27236
                   uu____27237
                  in
               Prims.op_Negation uu____27234  in
             if uu____27232
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____27251 =
                  let uu____27253 =
                    let uu____27255 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____27255 lid  in
                  Prims.op_Negation uu____27253  in
                if uu____27251
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____27269 =
                     let uu____27271 =
                       let uu____27273 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____27273
                         lid
                        in
                     Prims.op_Negation uu____27271  in
                   if uu____27269
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____27291 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____27291, [])
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
              | (FStar_Parser_AST.TyconRecord uu____27320)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____27339 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____27348 =
            let uu____27353 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____27353 tcs  in
          (match uu____27348 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____27370 =
                   let uu____27371 =
                     let uu____27378 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____27378  in
                   [uu____27371]  in
                 let uu____27391 =
                   let uu____27394 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____27397 =
                     let uu____27408 =
                       let uu____27417 =
                         let uu____27418 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____27418  in
                       FStar_Syntax_Syntax.as_arg uu____27417  in
                     [uu____27408]  in
                   FStar_Syntax_Util.mk_app uu____27394 uu____27397  in
                 FStar_Syntax_Util.abs uu____27370 uu____27391
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____27458,id1))::uu____27460 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____27463::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____27467 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____27467 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____27473 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____27473]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____27494) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____27504,uu____27505,uu____27506,uu____27507,uu____27508)
                     ->
                     let uu____27517 =
                       let uu____27518 =
                         let uu____27519 =
                           let uu____27526 = mkclass lid  in
                           (meths, uu____27526)  in
                         FStar_Syntax_Syntax.Sig_splice uu____27519  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____27518;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____27517]
                 | uu____27529 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____27563;
                    FStar_Parser_AST.prange = uu____27564;_},uu____27565)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____27575;
                    FStar_Parser_AST.prange = uu____27576;_},uu____27577)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____27593;
                         FStar_Parser_AST.prange = uu____27594;_},uu____27595);
                    FStar_Parser_AST.prange = uu____27596;_},uu____27597)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____27619;
                         FStar_Parser_AST.prange = uu____27620;_},uu____27621);
                    FStar_Parser_AST.prange = uu____27622;_},uu____27623)::[]
                   -> false
               | (p,uu____27652)::[] ->
                   let uu____27661 = is_app_pattern p  in
                   Prims.op_Negation uu____27661
               | uu____27663 -> false)
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
            let uu____27738 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27738 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27751 =
                     let uu____27752 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27752.FStar_Syntax_Syntax.n  in
                   match uu____27751 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27762) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27793 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27818  ->
                                match uu____27818 with
                                | (qs,ats) ->
                                    let uu____27845 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27845 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27793 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27899::uu____27900 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27903 -> val_quals  in
                            let quals2 =
                              let uu____27907 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27940  ->
                                        match uu____27940 with
                                        | (uu____27954,(uu____27955,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27907
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____27975 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____27975
                              then
                                let uu____27981 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3697_27996 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3699_27998 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3699_27998.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3699_27998.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3697_27996.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3697_27996.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3697_27996.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3697_27996.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3697_27996.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3697_27996.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____27981)
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
                   | uu____28023 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____28031 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____28050 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____28031 with
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
                       let uu___3722_28087 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3722_28087.FStar_Parser_AST.prange)
                       }
                   | uu____28094 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3726_28101 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3726_28101.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3726_28101.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____28117 =
                     let uu____28118 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____28118  in
                   FStar_Parser_AST.mk_term uu____28117
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____28142 id_opt =
                   match uu____28142 with
                   | (env1,ses) ->
                       let uu____28164 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id1 ->
                             let lid = FStar_Ident.lid_of_ids [id1]  in
                             let branch1 =
                               let uu____28176 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____28176
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28178 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____28178
                                in
                             (bv_pat, branch1)
                         | FStar_Pervasives_Native.None  ->
                             let id1 = FStar_Ident.gen FStar_Range.dummyRange
                                in
                             let branch1 =
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Const
                                    FStar_Const.Const_unit)
                                 FStar_Range.dummyRange FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____28184 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____28184
                                in
                             let bv_pat1 =
                               let uu____28188 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____28188
                                in
                             (bv_pat1, branch1)
                          in
                       (match uu____28164 with
                        | (bv_pat,branch1) ->
                            let body1 =
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.Match
                                   (main,
                                     [(pat, FStar_Pervasives_Native.None,
                                        branch1)]))
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
                            let uu____28249 = desugar_decl env1 id_decl  in
                            (match uu____28249 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____28285 id1 =
                   match uu____28285 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id1)
                    in
                 let build_coverage_check uu____28324 =
                   match uu____28324 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____28348 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____28348 FStar_Util.set_elements
                    in
                 let uu____28355 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____28358 = is_var_pattern pat  in
                      Prims.op_Negation uu____28358)
                    in
                 if uu____28355
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
            let uu____28382 = close_fun env t  in
            desugar_term env uu____28382  in
          let quals1 =
            let uu____28386 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____28386
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____28398 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____28398;
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
                let uu____28411 =
                  let uu____28420 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____28420]  in
                let uu____28439 =
                  let uu____28442 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____28442
                   in
                FStar_Syntax_Util.arrow uu____28411 uu____28439
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
          let uu____28508 =
            let uu____28510 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____28510  in
          if uu____28508
          then
            let uu____28517 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____28535 =
                    let uu____28538 =
                      let uu____28539 = desugar_term env t  in
                      ([], uu____28539)  in
                    FStar_Pervasives_Native.Some uu____28538  in
                  (uu____28535, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____28552 =
                    let uu____28555 =
                      let uu____28556 = desugar_term env wp  in
                      ([], uu____28556)  in
                    FStar_Pervasives_Native.Some uu____28555  in
                  let uu____28563 =
                    let uu____28566 =
                      let uu____28567 = desugar_term env t  in
                      ([], uu____28567)  in
                    FStar_Pervasives_Native.Some uu____28566  in
                  (uu____28552, uu____28563)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____28579 =
                    let uu____28582 =
                      let uu____28583 = desugar_term env t  in
                      ([], uu____28583)  in
                    FStar_Pervasives_Native.Some uu____28582  in
                  (FStar_Pervasives_Native.None, uu____28579)
               in
            (match uu____28517 with
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
                   let uu____28617 =
                     let uu____28620 =
                       let uu____28621 = desugar_term env t  in
                       ([], uu____28621)  in
                     FStar_Pervasives_Native.Some uu____28620  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____28617
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
             | uu____28628 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind1) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n1 = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____28641 =
            let uu____28642 =
              let uu____28643 =
                let uu____28644 =
                  let uu____28655 =
                    let uu____28656 = desugar_term env bind1  in
                    ([], uu____28656)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n1.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____28655,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____28644  in
              {
                FStar_Syntax_Syntax.sigel = uu____28643;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____28642]  in
          (env, uu____28641)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____28675 =
              let uu____28676 =
                let uu____28683 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____28683, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____28676  in
            {
              FStar_Syntax_Syntax.sigel = uu____28675;
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
      let uu____28710 =
        FStar_List.fold_left
          (fun uu____28730  ->
             fun d  ->
               match uu____28730 with
               | (env1,sigelts) ->
                   let uu____28750 = desugar_decl env1 d  in
                   (match uu____28750 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28710 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28841) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28845;
               FStar_Syntax_Syntax.exports = uu____28846;
               FStar_Syntax_Syntax.is_interface = uu____28847;_},FStar_Parser_AST.Module
             (current_lid,uu____28849)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28858) ->
              let uu____28861 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28861
           in
        let uu____28866 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28908 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28908, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28930 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28930, mname, decls, false)
           in
        match uu____28866 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28972 = desugar_decls env2 decls  in
            (match uu____28972 with
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
          let uu____29040 =
            (FStar_Options.interactive ()) &&
              (let uu____29043 =
                 let uu____29045 =
                   let uu____29047 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____29047  in
                 FStar_Util.get_file_extension uu____29045  in
               FStar_List.mem uu____29043 ["fsti"; "fsi"])
             in
          if uu____29040 then as_interface m else m  in
        let uu____29061 = desugar_modul_common curmod env m1  in
        match uu____29061 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____29083 = FStar_Syntax_DsEnv.pop ()  in
              (uu____29083, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____29105 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____29105 with
      | (env1,modul,pop_when_done) ->
          let uu____29122 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____29122 with
           | (env2,modul1) ->
               ((let uu____29134 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____29134
                 then
                   let uu____29137 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____29137
                 else ());
                (let uu____29142 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____29142, modul1))))
  
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
        (fun uu____29192  ->
           let uu____29193 = desugar_modul env modul  in
           match uu____29193 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____29231  ->
           let uu____29232 = desugar_decls env decls  in
           match uu____29232 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____29283  ->
             let uu____29284 = desugar_partial_modul modul env a_modul  in
             match uu____29284 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____29379 ->
                  let t =
                    let uu____29389 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____29389  in
                  let uu____29402 =
                    let uu____29403 = FStar_Syntax_Subst.compress t  in
                    uu____29403.FStar_Syntax_Syntax.n  in
                  (match uu____29402 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____29415,uu____29416)
                       -> bs1
                   | uu____29441 -> failwith "Impossible")
               in
            let uu____29451 =
              let uu____29458 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____29458
                FStar_Syntax_Syntax.t_unit
               in
            match uu____29451 with
            | (binders,uu____29460,binders_opening) ->
                let erase_term t =
                  let uu____29468 =
                    let uu____29469 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____29469  in
                  FStar_Syntax_Subst.close binders uu____29468  in
                let erase_tscheme uu____29487 =
                  match uu____29487 with
                  | (us,t) ->
                      let t1 =
                        let uu____29507 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____29507 t  in
                      let uu____29510 =
                        let uu____29511 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____29511  in
                      ([], uu____29510)
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
                    | uu____29534 ->
                        let bs =
                          let uu____29544 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____29544  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____29584 =
                          let uu____29585 =
                            let uu____29588 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____29588  in
                          uu____29585.FStar_Syntax_Syntax.n  in
                        (match uu____29584 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____29590,uu____29591) -> bs1
                         | uu____29616 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____29624 =
                      let uu____29625 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____29625  in
                    FStar_Syntax_Subst.close binders uu____29624  in
                  let uu___4019_29626 = action  in
                  let uu____29627 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____29628 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___4019_29626.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___4019_29626.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____29627;
                    FStar_Syntax_Syntax.action_typ = uu____29628
                  }  in
                let uu___4021_29629 = ed  in
                let uu____29630 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____29631 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____29632 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____29633 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___4021_29629.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___4021_29629.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____29630;
                  FStar_Syntax_Syntax.signature = uu____29631;
                  FStar_Syntax_Syntax.combinators = uu____29632;
                  FStar_Syntax_Syntax.actions = uu____29633;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___4021_29629.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___4028_29649 = se  in
                  let uu____29650 =
                    let uu____29651 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____29651  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____29650;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___4028_29649.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___4028_29649.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___4028_29649.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___4028_29649.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___4028_29649.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____29653 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____29654 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____29654 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____29671 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____29671
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____29673 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____29673)
  