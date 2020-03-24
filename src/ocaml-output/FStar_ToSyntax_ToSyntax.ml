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
    (let uu____2847 = FStar_Syntax_Print.tag_of_sigelt s  in
     FStar_Util.print1 "GG generalize of %s\n" uu____2847);
    (match s.FStar_Syntax_Syntax.sigel with
     | FStar_Syntax_Syntax.Sig_inductive_typ uu____2850 ->
         failwith
           "Impossible: collect_annotated_universes: bare data/type constructor"
     | FStar_Syntax_Syntax.Sig_datacon uu____2868 ->
         failwith
           "Impossible: collect_annotated_universes: bare data/type constructor"
     | FStar_Syntax_Syntax.Sig_bundle (sigs,lids) ->
         let uvs =
           let uu____2896 =
             FStar_All.pipe_right sigs
               (FStar_List.fold_left
                  (fun uvs  ->
                     fun se  ->
                       let se_univs =
                         match se.FStar_Syntax_Syntax.sigel with
                         | FStar_Syntax_Syntax.Sig_inductive_typ
                             (uu____2917,uu____2918,bs,t,uu____2921,uu____2922)
                             ->
                             let uu____2931 = bs_univnames bs  in
                             let uu____2934 = FStar_Syntax_Free.univnames t
                                in
                             FStar_Util.set_union uu____2931 uu____2934
                         | FStar_Syntax_Syntax.Sig_datacon
                             (uu____2937,uu____2938,t,uu____2940,uu____2941,uu____2942)
                             -> FStar_Syntax_Free.univnames t
                         | uu____2949 ->
                             failwith
                               "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"
                          in
                       FStar_Util.set_union uvs se_univs) empty_set)
              in
           FStar_All.pipe_right uu____2896 FStar_Util.set_elements  in
         let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
         let uu___590_2958 = s  in
         let uu____2959 =
           let uu____2960 =
             let uu____2969 =
               FStar_All.pipe_right sigs
                 (FStar_List.map
                    (fun se  ->
                       match se.FStar_Syntax_Syntax.sigel with
                       | FStar_Syntax_Syntax.Sig_inductive_typ
                           (lid,uu____2987,bs,t,lids1,lids2) ->
                           let uu___601_3000 = se  in
                           let uu____3001 =
                             let uu____3002 =
                               let uu____3019 =
                                 FStar_Syntax_Subst.subst_binders usubst bs
                                  in
                               let uu____3020 =
                                 let uu____3021 =
                                   FStar_Syntax_Subst.shift_subst
                                     (FStar_List.length bs) usubst
                                    in
                                 FStar_Syntax_Subst.subst uu____3021 t  in
                               (lid, uvs, uu____3019, uu____3020, lids1,
                                 lids2)
                                in
                             FStar_Syntax_Syntax.Sig_inductive_typ uu____3002
                              in
                           {
                             FStar_Syntax_Syntax.sigel = uu____3001;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___601_3000.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___601_3000.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___601_3000.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___601_3000.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___601_3000.FStar_Syntax_Syntax.sigopts)
                           }
                       | FStar_Syntax_Syntax.Sig_datacon
                           (lid,uu____3035,t,tlid,n1,lids1) ->
                           let uu___611_3046 = se  in
                           let uu____3047 =
                             let uu____3048 =
                               let uu____3064 =
                                 FStar_Syntax_Subst.subst usubst t  in
                               (lid, uvs, uu____3064, tlid, n1, lids1)  in
                             FStar_Syntax_Syntax.Sig_datacon uu____3048  in
                           {
                             FStar_Syntax_Syntax.sigel = uu____3047;
                             FStar_Syntax_Syntax.sigrng =
                               (uu___611_3046.FStar_Syntax_Syntax.sigrng);
                             FStar_Syntax_Syntax.sigquals =
                               (uu___611_3046.FStar_Syntax_Syntax.sigquals);
                             FStar_Syntax_Syntax.sigmeta =
                               (uu___611_3046.FStar_Syntax_Syntax.sigmeta);
                             FStar_Syntax_Syntax.sigattrs =
                               (uu___611_3046.FStar_Syntax_Syntax.sigattrs);
                             FStar_Syntax_Syntax.sigopts =
                               (uu___611_3046.FStar_Syntax_Syntax.sigopts)
                           }
                       | uu____3068 ->
                           failwith
                             "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt"))
                in
             (uu____2969, lids)  in
           FStar_Syntax_Syntax.Sig_bundle uu____2960  in
         {
           FStar_Syntax_Syntax.sigel = uu____2959;
           FStar_Syntax_Syntax.sigrng =
             (uu___590_2958.FStar_Syntax_Syntax.sigrng);
           FStar_Syntax_Syntax.sigquals =
             (uu___590_2958.FStar_Syntax_Syntax.sigquals);
           FStar_Syntax_Syntax.sigmeta =
             (uu___590_2958.FStar_Syntax_Syntax.sigmeta);
           FStar_Syntax_Syntax.sigattrs =
             (uu___590_2958.FStar_Syntax_Syntax.sigattrs);
           FStar_Syntax_Syntax.sigopts =
             (uu___590_2958.FStar_Syntax_Syntax.sigopts)
         }
     | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____3075,t) ->
         let uvs =
           let uu____3078 = FStar_Syntax_Free.univnames t  in
           FStar_All.pipe_right uu____3078 FStar_Util.set_elements  in
         let uu___620_3083 = s  in
         let uu____3084 =
           let uu____3085 =
             let uu____3092 = FStar_Syntax_Subst.close_univ_vars uvs t  in
             (lid, uvs, uu____3092)  in
           FStar_Syntax_Syntax.Sig_declare_typ uu____3085  in
         {
           FStar_Syntax_Syntax.sigel = uu____3084;
           FStar_Syntax_Syntax.sigrng =
             (uu___620_3083.FStar_Syntax_Syntax.sigrng);
           FStar_Syntax_Syntax.sigquals =
             (uu___620_3083.FStar_Syntax_Syntax.sigquals);
           FStar_Syntax_Syntax.sigmeta =
             (uu___620_3083.FStar_Syntax_Syntax.sigmeta);
           FStar_Syntax_Syntax.sigattrs =
             (uu___620_3083.FStar_Syntax_Syntax.sigattrs);
           FStar_Syntax_Syntax.sigopts =
             (uu___620_3083.FStar_Syntax_Syntax.sigopts)
         }
     | FStar_Syntax_Syntax.Sig_let ((b,lbs),lids) ->
         let lb_univnames lb =
           let uu____3116 =
             FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp  in
           let uu____3119 =
             match (lb.FStar_Syntax_Syntax.lbdef).FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_abs (bs,e,uu____3126) ->
                 let uvs1 = bs_univnames bs  in
                 let uvs2 =
                   match e.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_ascribed
                       (uu____3159,(FStar_Util.Inl t,uu____3161),uu____3162)
                       -> FStar_Syntax_Free.univnames t
                   | FStar_Syntax_Syntax.Tm_ascribed
                       (uu____3209,(FStar_Util.Inr c,uu____3211),uu____3212)
                       -> FStar_Syntax_Free.univnames_comp c
                   | uu____3259 -> empty_set  in
                 FStar_Util.set_union uvs1 uvs2
             | FStar_Syntax_Syntax.Tm_arrow (bs,uu____3261) ->
                 bs_univnames bs
             | FStar_Syntax_Syntax.Tm_ascribed
                 (uu____3282,(FStar_Util.Inl t,uu____3284),uu____3285) ->
                 FStar_Syntax_Free.univnames t
             | FStar_Syntax_Syntax.Tm_ascribed
                 (uu____3332,(FStar_Util.Inr c,uu____3334),uu____3335) ->
                 FStar_Syntax_Free.univnames_comp c
             | uu____3382 -> empty_set  in
           FStar_Util.set_union uu____3116 uu____3119  in
         let all_lb_univs =
           let uu____3386 =
             FStar_All.pipe_right lbs
               (FStar_List.fold_left
                  (fun uvs  ->
                     fun lb  ->
                       let uu____3402 = lb_univnames lb  in
                       FStar_Util.set_union uvs uu____3402) empty_set)
              in
           FStar_All.pipe_right uu____3386 FStar_Util.set_elements  in
         let usubst = FStar_Syntax_Subst.univ_var_closing all_lb_univs  in
         let uu___679_3412 = s  in
         let uu____3413 =
           let uu____3414 =
             let uu____3421 =
               let uu____3422 =
                 FStar_All.pipe_right lbs
                   (FStar_List.map
                      (fun lb  ->
                         let uu___682_3434 = lb  in
                         let uu____3435 =
                           FStar_Syntax_Subst.subst usubst
                             lb.FStar_Syntax_Syntax.lbtyp
                            in
                         let uu____3438 =
                           FStar_Syntax_Subst.subst usubst
                             lb.FStar_Syntax_Syntax.lbdef
                            in
                         {
                           FStar_Syntax_Syntax.lbname =
                             (uu___682_3434.FStar_Syntax_Syntax.lbname);
                           FStar_Syntax_Syntax.lbunivs = all_lb_univs;
                           FStar_Syntax_Syntax.lbtyp = uu____3435;
                           FStar_Syntax_Syntax.lbeff =
                             (uu___682_3434.FStar_Syntax_Syntax.lbeff);
                           FStar_Syntax_Syntax.lbdef = uu____3438;
                           FStar_Syntax_Syntax.lbattrs =
                             (uu___682_3434.FStar_Syntax_Syntax.lbattrs);
                           FStar_Syntax_Syntax.lbpos =
                             (uu___682_3434.FStar_Syntax_Syntax.lbpos)
                         }))
                  in
               (b, uu____3422)  in
             (uu____3421, lids)  in
           FStar_Syntax_Syntax.Sig_let uu____3414  in
         {
           FStar_Syntax_Syntax.sigel = uu____3413;
           FStar_Syntax_Syntax.sigrng =
             (uu___679_3412.FStar_Syntax_Syntax.sigrng);
           FStar_Syntax_Syntax.sigquals =
             (uu___679_3412.FStar_Syntax_Syntax.sigquals);
           FStar_Syntax_Syntax.sigmeta =
             (uu___679_3412.FStar_Syntax_Syntax.sigmeta);
           FStar_Syntax_Syntax.sigattrs =
             (uu___679_3412.FStar_Syntax_Syntax.sigattrs);
           FStar_Syntax_Syntax.sigopts =
             (uu___679_3412.FStar_Syntax_Syntax.sigopts)
         }
     | FStar_Syntax_Syntax.Sig_assume (lid,uu____3447,fml) ->
         let uvs =
           let uu____3450 = FStar_Syntax_Free.univnames fml  in
           FStar_All.pipe_right uu____3450 FStar_Util.set_elements  in
         let uu___690_3455 = s  in
         let uu____3456 =
           let uu____3457 =
             let uu____3464 = FStar_Syntax_Subst.close_univ_vars uvs fml  in
             (lid, uvs, uu____3464)  in
           FStar_Syntax_Syntax.Sig_assume uu____3457  in
         {
           FStar_Syntax_Syntax.sigel = uu____3456;
           FStar_Syntax_Syntax.sigrng =
             (uu___690_3455.FStar_Syntax_Syntax.sigrng);
           FStar_Syntax_Syntax.sigquals =
             (uu___690_3455.FStar_Syntax_Syntax.sigquals);
           FStar_Syntax_Syntax.sigmeta =
             (uu___690_3455.FStar_Syntax_Syntax.sigmeta);
           FStar_Syntax_Syntax.sigattrs =
             (uu___690_3455.FStar_Syntax_Syntax.sigattrs);
           FStar_Syntax_Syntax.sigopts =
             (uu___690_3455.FStar_Syntax_Syntax.sigopts)
         }
     | FStar_Syntax_Syntax.Sig_effect_abbrev (lid,uu____3466,bs,c,flags) ->
         let uvs =
           let uu____3475 =
             let uu____3478 = bs_univnames bs  in
             let uu____3481 = FStar_Syntax_Free.univnames_comp c  in
             FStar_Util.set_union uu____3478 uu____3481  in
           FStar_All.pipe_right uu____3475 FStar_Util.set_elements  in
         let usubst = FStar_Syntax_Subst.univ_var_closing uvs  in
         let uu___701_3489 = s  in
         let uu____3490 =
           let uu____3491 =
             let uu____3504 = FStar_Syntax_Subst.subst_binders usubst bs  in
             let uu____3505 = FStar_Syntax_Subst.subst_comp usubst c  in
             (lid, uvs, uu____3504, uu____3505, flags)  in
           FStar_Syntax_Syntax.Sig_effect_abbrev uu____3491  in
         {
           FStar_Syntax_Syntax.sigel = uu____3490;
           FStar_Syntax_Syntax.sigrng =
             (uu___701_3489.FStar_Syntax_Syntax.sigrng);
           FStar_Syntax_Syntax.sigquals =
             (uu___701_3489.FStar_Syntax_Syntax.sigquals);
           FStar_Syntax_Syntax.sigmeta =
             (uu___701_3489.FStar_Syntax_Syntax.sigmeta);
           FStar_Syntax_Syntax.sigattrs =
             (uu___701_3489.FStar_Syntax_Syntax.sigattrs);
           FStar_Syntax_Syntax.sigopts =
             (uu___701_3489.FStar_Syntax_Syntax.sigopts)
         }
     | FStar_Syntax_Syntax.Sig_fail uu____3508 -> s
     | FStar_Syntax_Syntax.Sig_new_effect uu____3521 -> s
     | FStar_Syntax_Syntax.Sig_sub_effect uu____3522 -> s
     | FStar_Syntax_Syntax.Sig_main uu____3523 -> s
     | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3524 -> s
     | FStar_Syntax_Syntax.Sig_splice uu____3535 -> s
     | FStar_Syntax_Syntax.Sig_pragma uu____3542 -> s)
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3550  ->
    match uu___4_3550 with
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
    | uu____3599 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = Prims.int_zero
      then u
      else
        (let uu____3620 = sum_to_universe u (n1 - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3620)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3646 =
      let uu____3647 = unparen t  in uu____3647.FStar_Parser_AST.tm  in
    match uu____3646 with
    | FStar_Parser_AST.Wild  ->
        let uu____3653 =
          let uu____3654 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3654  in
        FStar_Util.Inr uu____3653
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3667)) ->
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
             let uu____3758 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3758
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3775 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3775
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3791 =
               let uu____3797 =
                 let uu____3799 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3799
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3797)
                in
             FStar_Errors.raise_error uu____3791 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3808 ->
        let rec aux t1 univargs =
          let uu____3845 =
            let uu____3846 = unparen t1  in uu____3846.FStar_Parser_AST.tm
             in
          match uu____3845 with
          | FStar_Parser_AST.App (t2,targ,uu____3854) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3881  ->
                     match uu___5_3881 with
                     | FStar_Util.Inr uu____3888 -> true
                     | uu____3891 -> false) univargs
              then
                let uu____3899 =
                  let uu____3900 =
                    FStar_List.map
                      (fun uu___6_3910  ->
                         match uu___6_3910 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3900  in
                FStar_Util.Inr uu____3899
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3936  ->
                        match uu___7_3936 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3946 -> failwith "impossible")
                     univargs
                    in
                 let uu____3950 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3950)
          | uu____3966 ->
              let uu____3967 =
                let uu____3973 =
                  let uu____3975 =
                    let uu____3977 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3977 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3975  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3973)  in
              FStar_Errors.raise_error uu____3967 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3992 ->
        let uu____3993 =
          let uu____3999 =
            let uu____4001 =
              let uu____4003 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____4003 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____4001  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3999)  in
        FStar_Errors.raise_error uu____3993 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____4044;_});
            FStar_Syntax_Syntax.pos = uu____4045;
            FStar_Syntax_Syntax.vars = uu____4046;_})::uu____4047
        ->
        let uu____4078 =
          let uu____4084 =
            let uu____4086 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4086
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4084)  in
        FStar_Errors.raise_error uu____4078 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4092 ->
        let uu____4111 =
          let uu____4117 =
            let uu____4119 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4119
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4117)  in
        FStar_Errors.raise_error uu____4111 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4132 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4132) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4160 = FStar_List.hd fields  in
        match uu____4160 with
        | (f,uu____4170) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4182 =
                match uu____4182 with
                | (f',uu____4188) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4190 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4190
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
              (let uu____4200 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4200);
              (match () with | () -> record)))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4248 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4255 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4256 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4258,pats1) ->
            let aux out uu____4299 =
              match uu____4299 with
              | (p1,uu____4312) ->
                  let intersection =
                    let uu____4322 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4322 out  in
                  let uu____4325 = FStar_Util.set_is_empty intersection  in
                  if uu____4325
                  then
                    let uu____4330 = pat_vars p1  in
                    FStar_Util.set_union out uu____4330
                  else
                    (let duplicate_bv =
                       let uu____4336 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4336  in
                     let uu____4339 =
                       let uu____4345 =
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4345)
                        in
                     FStar_Errors.raise_error uu____4339 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4369 = pat_vars p  in
          FStar_All.pipe_right uu____4369 (fun a1  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4397 =
              let uu____4399 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4399  in
            if uu____4397
            then ()
            else
              (let nonlinear_vars =
                 let uu____4408 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4408  in
               let first_nonlinear_var =
                 let uu____4412 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4412  in
               let uu____4415 =
                 let uu____4421 =
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4421)  in
               FStar_Errors.raise_error uu____4415 r)
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
          let uu____4736 =
            FStar_Util.find_opt
              (fun y  ->
                 (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                   x.FStar_Ident.idText) l
             in
          match uu____4736 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4753 ->
              let uu____4756 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4756 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4897 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4919 =
                  let uu____4925 =
                    FStar_Parser_AST.compile_op Prims.int_zero
                      op.FStar_Ident.idText op.FStar_Ident.idRange
                     in
                  (uu____4925, (op.FStar_Ident.idRange))  in
                FStar_Ident.mk_ident uu____4919  in
              let p2 =
                let uu___930_4930 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___930_4930.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4947 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4950 = aux loc env1 p2  in
                match uu____4950 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5006 =
                      match binder with
                      | LetBinder uu____5027 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5052 = close_fun env1 t  in
                            desugar_term env1 uu____5052  in
                          let x1 =
                            let uu___956_5054 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___956_5054.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___956_5054.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5006 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5100 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5101 -> ()
                           | uu____5102 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5103 ->
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
              let uu____5121 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5121, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5134 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5134, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5152 = resolvex loc env1 x  in
              (match uu____5152 with
               | (loc1,env2,xbv) ->
                   let uu____5184 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5184, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5202 = resolvex loc env1 x  in
              (match uu____5202 with
               | (loc1,env2,xbv) ->
                   let uu____5234 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5234, []))
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
              let uu____5248 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5248, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5276;_},args)
              ->
              let uu____5282 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5343  ->
                       match uu____5343 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5424 = aux loc1 env2 arg  in
                           (match uu____5424 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5282 with
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
                   let uu____5596 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5596, annots))
          | FStar_Parser_AST.PatApp uu____5612 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5640 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5690  ->
                       match uu____5690 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5751 = aux loc1 env2 pat  in
                           (match uu____5751 with
                            | (loc2,env3,uu____5790,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5640 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5884 =
                       let uu____5887 =
                         let uu____5894 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5894  in
                       let uu____5895 =
                         let uu____5896 =
                           let uu____5910 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5910, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5896  in
                       FStar_All.pipe_left uu____5887 uu____5895  in
                     FStar_List.fold_right
                       (fun hd1  ->
                          fun tl1  ->
                            let r =
                              FStar_Range.union_ranges
                                hd1.FStar_Syntax_Syntax.p
                                tl1.FStar_Syntax_Syntax.p
                               in
                            let uu____5944 =
                              let uu____5945 =
                                let uu____5959 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5959, [(hd1, false); (tl1, false)])
                                 in
                              FStar_Syntax_Syntax.Pat_cons uu____5945  in
                            FStar_All.pipe_left (pos_r r) uu____5944) pats1
                       uu____5884
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
              let uu____6015 =
                FStar_List.fold_left
                  (fun uu____6074  ->
                     fun p2  ->
                       match uu____6074 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6156 = aux loc1 env2 p2  in
                           (match uu____6156 with
                            | (loc2,env3,uu____6200,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6015 with
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
                     | uu____6363 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6366 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6366, annots))
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
                     (fun uu____6442  ->
                        match uu____6442 with
                        | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6472  ->
                        match uu____6472 with
                        | (f,uu____6478) ->
                            let uu____6479 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6505  ->
                                      match uu____6505 with
                                      | (g,uu____6512) ->
                                          f.FStar_Ident.idText =
                                            g.FStar_Ident.idText))
                               in
                            (match uu____6479 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6518,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6525 =
                  let uu____6526 =
                    let uu____6533 =
                      let uu____6534 =
                        let uu____6535 =
                          FStar_Ident.lid_of_ids
                            (FStar_List.append
                               (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                               [record.FStar_Syntax_DsEnv.constrname])
                           in
                        FStar_Parser_AST.PatName uu____6535  in
                      FStar_Parser_AST.mk_pattern uu____6534
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6533, args)  in
                  FStar_Parser_AST.PatApp uu____6526  in
                FStar_Parser_AST.mk_pattern uu____6525
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6538 = aux loc env1 app  in
              (match uu____6538 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6615 =
                           let uu____6616 =
                             let uu____6630 =
                               let uu___1106_6631 = fv  in
                               let uu____6632 =
                                 let uu____6635 =
                                   let uu____6636 =
                                     let uu____6643 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6643)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6636
                                    in
                                 FStar_Pervasives_Native.Some uu____6635  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1106_6631.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1106_6631.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6632
                               }  in
                             (uu____6630, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6616  in
                         FStar_All.pipe_left pos uu____6615
                     | uu____6669 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6753 = aux' true loc env1 p2  in
              (match uu____6753 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6806 =
                     FStar_List.fold_left
                       (fun uu____6854  ->
                          fun p4  ->
                            match uu____6854 with
                            | (loc2,env3,ps1) ->
                                let uu____6919 = aux' true loc2 env3 p4  in
                                (match uu____6919 with
                                 | (loc3,env4,uu____6957,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6806 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7118 ->
              let uu____7119 = aux' true loc env1 p1  in
              (match uu____7119 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7210 = aux_maybe_or env p  in
        match uu____7210 with
        | (env1,b,pats) ->
            ((let uu____7265 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7265
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
            let uu____7339 =
              let uu____7340 =
                let uu____7351 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7351, (ty, tacopt))  in
              LetBinder uu____7340  in
            (env, uu____7339, [])  in
          let op_to_ident x =
            let uu____7368 =
              let uu____7374 =
                FStar_Parser_AST.compile_op Prims.int_zero
                  x.FStar_Ident.idText x.FStar_Ident.idRange
                 in
              (uu____7374, (x.FStar_Ident.idRange))  in
            FStar_Ident.mk_ident uu____7368  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7387 = op_to_ident x  in
              mklet uu____7387 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7389) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7395;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7411 = op_to_ident x  in
              let uu____7412 = desugar_term env t  in
              mklet uu____7411 uu____7412 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7414);
                 FStar_Parser_AST.prange = uu____7415;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7435 = desugar_term env t  in
              mklet x uu____7435 tacopt1
          | uu____7436 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7449 = desugar_data_pat true env p  in
           match uu____7449 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7479;
                      FStar_Syntax_Syntax.p = uu____7480;_},uu____7481)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7494;
                      FStar_Syntax_Syntax.p = uu____7495;_},uu____7496)::[]
                     -> []
                 | uu____7509 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7517  ->
    fun env  ->
      fun pat  ->
        let uu____7521 = desugar_data_pat false env pat  in
        match uu____7521 with | (env1,uu____7538,pat1) -> (env1, pat1)

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
      let uu____7560 = desugar_term_aq env e  in
      match uu____7560 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7579 = desugar_typ_aq env e  in
      match uu____7579 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7589  ->
        fun range  ->
          match uu____7589 with
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
              ((let uu____7611 =
                  let uu____7613 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7613  in
                if uu____7611
                then
                  let uu____7616 =
                    let uu____7622 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7622)  in
                  FStar_Errors.log_issue range uu____7616
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
                  let uu____7643 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7643 range  in
                let lid1 =
                  let uu____7647 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7647 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7657 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7657 range  in
                           let private_fv =
                             let uu____7659 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7659 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1273_7660 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1273_7660.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1273_7660.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7661 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7665 =
                        let uu____7671 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7671)
                         in
                      FStar_Errors.raise_error uu____7665 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7691 =
                  let uu____7698 =
                    let uu____7699 =
                      let uu____7716 =
                        let uu____7727 =
                          let uu____7736 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7736)  in
                        [uu____7727]  in
                      (lid1, uu____7716)  in
                    FStar_Syntax_Syntax.Tm_app uu____7699  in
                  FStar_Syntax_Syntax.mk uu____7698  in
                uu____7691 FStar_Pervasives_Native.None range))

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
          let uu___1289_7855 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1289_7855.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1289_7855.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7858 =
          let uu____7859 = unparen top  in uu____7859.FStar_Parser_AST.tm  in
        match uu____7858 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7864 ->
            let uu____7873 = desugar_formula env top  in (uu____7873, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7882 = desugar_formula env t  in (uu____7882, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7891 = desugar_formula env t  in (uu____7891, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7918 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7918, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7920 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7920, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7929 =
                let uu____7930 =
                  let uu____7937 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7937, args)  in
                FStar_Parser_AST.Op uu____7930  in
              FStar_Parser_AST.mk_term uu____7929 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7942 =
              let uu____7943 =
                let uu____7944 =
                  let uu____7951 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7951, [e])  in
                FStar_Parser_AST.Op uu____7944  in
              FStar_Parser_AST.mk_term uu____7943 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7942
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7963 = FStar_Ident.text_of_id op_star  in
             uu____7963 = "*") &&
              (let uu____7968 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____7968 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7985;_},t1::t2::[])
                  when
                  let uu____7991 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____7991 FStar_Option.isNone ->
                  let uu____7998 = flatten1 t1  in
                  FStar_List.append uu____7998 [t2]
              | uu____8001 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1337_8006 = top  in
              let uu____8007 =
                let uu____8008 =
                  let uu____8019 =
                    FStar_List.map (fun _8030  -> FStar_Util.Inr _8030) terms
                     in
                  (uu____8019, rhs)  in
                FStar_Parser_AST.Sum uu____8008  in
              {
                FStar_Parser_AST.tm = uu____8007;
                FStar_Parser_AST.range =
                  (uu___1337_8006.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1337_8006.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8038 =
              let uu____8039 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8039  in
            (uu____8038, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8045 =
              let uu____8051 =
                let uu____8053 =
                  let uu____8055 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8055 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8053  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8051)  in
            FStar_Errors.raise_error uu____8045 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8070 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8070 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8077 =
                   let uu____8083 =
                     let uu____8085 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8085
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8083)
                    in
                 FStar_Errors.raise_error uu____8077
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8100 =
                     let uu____8125 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8187 = desugar_term_aq env t  in
                               match uu____8187 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8125 FStar_List.unzip  in
                   (match uu____8100 with
                    | (args1,aqs) ->
                        let uu____8320 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8320, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8337)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8354 =
              let uu___1366_8355 = top  in
              let uu____8356 =
                let uu____8357 =
                  let uu____8364 =
                    let uu___1368_8365 = top  in
                    let uu____8366 =
                      let uu____8367 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8367  in
                    {
                      FStar_Parser_AST.tm = uu____8366;
                      FStar_Parser_AST.range =
                        (uu___1368_8365.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1368_8365.FStar_Parser_AST.level)
                    }  in
                  (uu____8364, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8357  in
              {
                FStar_Parser_AST.tm = uu____8356;
                FStar_Parser_AST.range =
                  (uu___1366_8355.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1366_8355.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8354
        | FStar_Parser_AST.Construct (n1,(a,uu____8375)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8395 =
                let uu___1378_8396 = top  in
                let uu____8397 =
                  let uu____8398 =
                    let uu____8405 =
                      let uu___1380_8406 = top  in
                      let uu____8407 =
                        let uu____8408 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8408  in
                      {
                        FStar_Parser_AST.tm = uu____8407;
                        FStar_Parser_AST.range =
                          (uu___1380_8406.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1380_8406.FStar_Parser_AST.level)
                      }  in
                    (uu____8405, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8398  in
                {
                  FStar_Parser_AST.tm = uu____8397;
                  FStar_Parser_AST.range =
                    (uu___1378_8396.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1378_8396.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8395))
        | FStar_Parser_AST.Construct (n1,(a,uu____8416)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8433 =
              let uu___1389_8434 = top  in
              let uu____8435 =
                let uu____8436 =
                  let uu____8443 =
                    let uu___1391_8444 = top  in
                    let uu____8445 =
                      let uu____8446 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8446  in
                    {
                      FStar_Parser_AST.tm = uu____8445;
                      FStar_Parser_AST.range =
                        (uu___1391_8444.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1391_8444.FStar_Parser_AST.level)
                    }  in
                  (uu____8443, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8436  in
              {
                FStar_Parser_AST.tm = uu____8435;
                FStar_Parser_AST.range =
                  (uu___1389_8434.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1389_8434.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8433
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8452; FStar_Ident.ident = uu____8453;
              FStar_Ident.nsstr = uu____8454; FStar_Ident.str = "Type0";_}
            ->
            let uu____8459 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8459, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8460; FStar_Ident.ident = uu____8461;
              FStar_Ident.nsstr = uu____8462; FStar_Ident.str = "Type";_}
            ->
            let uu____8467 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8467, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8468; FStar_Ident.ident = uu____8469;
               FStar_Ident.nsstr = uu____8470; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8490 =
              let uu____8491 =
                let uu____8492 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8492  in
              mk1 uu____8491  in
            (uu____8490, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8493; FStar_Ident.ident = uu____8494;
              FStar_Ident.nsstr = uu____8495; FStar_Ident.str = "Effect";_}
            ->
            let uu____8500 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8500, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8501; FStar_Ident.ident = uu____8502;
              FStar_Ident.nsstr = uu____8503; FStar_Ident.str = "True";_}
            ->
            let uu____8508 =
              let uu____8509 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8509
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8508, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8510; FStar_Ident.ident = uu____8511;
              FStar_Ident.nsstr = uu____8512; FStar_Ident.str = "False";_}
            ->
            let uu____8517 =
              let uu____8518 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8518
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8517, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8521;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8524 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8524 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8533 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         Prims.int_one) FStar_Pervasives_Native.None
                     in
                  (uu____8533, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8535 =
                    let uu____8537 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8537 txt
                     in
                  failwith uu____8535))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8546 = desugar_name mk1 setpos env true l  in
              (uu____8546, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8555 = desugar_name mk1 setpos env true l  in
              (uu____8555, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8573 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8573 with
                | FStar_Pervasives_Native.Some uu____8583 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8591 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8591 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8609 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8630 =
                    let uu____8631 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8631  in
                  (uu____8630, noaqs)
              | uu____8637 ->
                  let uu____8645 =
                    let uu____8651 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8651)  in
                  FStar_Errors.raise_error uu____8645
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8661 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8661 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8668 =
                    let uu____8674 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8674)
                     in
                  FStar_Errors.raise_error uu____8668
                    top.FStar_Parser_AST.range
              | uu____8682 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8686 = desugar_name mk1 setpos env true lid'  in
                  (uu____8686, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8708 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8708 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8727 ->
                       let uu____8734 =
                         FStar_Util.take
                           (fun uu____8758  ->
                              match uu____8758 with
                              | (uu____8764,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8734 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8809 =
                              let uu____8834 =
                                FStar_List.map
                                  (fun uu____8877  ->
                                     match uu____8877 with
                                     | (t,imp) ->
                                         let uu____8894 =
                                           desugar_term_aq env t  in
                                         (match uu____8894 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8834
                                FStar_List.unzip
                               in
                            (match uu____8809 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9037 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9037, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9056 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9056 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9067 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9095  ->
                 match uu___8_9095 with
                 | FStar_Util.Inr uu____9101 -> true
                 | uu____9103 -> false) binders
            ->
            let terms =
              let uu____9112 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9129  ->
                        match uu___9_9129 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9135 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9112 [t]  in
            let uu____9137 =
              let uu____9162 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9219 = desugar_typ_aq env t1  in
                        match uu____9219 with
                        | (t',aq) ->
                            let uu____9230 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9230, aq)))
                 in
              FStar_All.pipe_right uu____9162 FStar_List.unzip  in
            (match uu____9137 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9340 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9340
                    in
                 let uu____9349 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9349, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9376 =
              let uu____9393 =
                let uu____9400 =
                  let uu____9407 =
                    FStar_All.pipe_left (fun _9416  -> FStar_Util.Inl _9416)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9407]  in
                FStar_List.append binders uu____9400  in
              FStar_List.fold_left
                (fun uu____9461  ->
                   fun b  ->
                     match uu____9461 with
                     | (env1,tparams,typs) ->
                         let uu____9522 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9537 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9537)
                            in
                         (match uu____9522 with
                          | (xopt,t1) ->
                              let uu____9562 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9571 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9571)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9562 with
                               | (env2,x) ->
                                   let uu____9591 =
                                     let uu____9594 =
                                       let uu____9597 =
                                         let uu____9598 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9598
                                          in
                                       [uu____9597]  in
                                     FStar_List.append typs uu____9594  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1550_9624 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1550_9624.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1550_9624.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9591)))) (env, [], []) uu____9393
               in
            (match uu____9376 with
             | (env1,uu____9652,targs) ->
                 let tup =
                   let uu____9675 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9675
                    in
                 let uu____9676 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9676, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9695 = uncurry binders t  in
            (match uu____9695 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9739 =
                   match uu___10_9739 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9756 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9756
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9780 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9780 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9813 = aux env [] bs  in (uu____9813, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9822 = desugar_binder env b  in
            (match uu____9822 with
             | (FStar_Pervasives_Native.None ,uu____9833) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9848 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9848 with
                  | ((x,uu____9864),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9877 =
                        let uu____9878 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9878  in
                      (uu____9877, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9956 = FStar_Util.set_is_empty i  in
                    if uu____9956
                    then
                      let uu____9961 = FStar_Util.set_union acc set1  in
                      aux uu____9961 sets2
                    else
                      (let uu____9966 =
                         let uu____9967 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9967  in
                       FStar_Pervasives_Native.Some uu____9966)
                 in
              let uu____9970 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9970 sets  in
            ((let uu____9974 = check_disjoint bvss  in
              match uu____9974 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9978 =
                    let uu____9984 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9984)
                     in
                  let uu____9988 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9978 uu____9988);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9996 =
                FStar_List.fold_left
                  (fun uu____10016  ->
                     fun pat  ->
                       match uu____10016 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10042,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10052 =
                                  let uu____10055 = free_type_vars env1 t  in
                                  FStar_List.append uu____10055 ftvs  in
                                (env1, uu____10052)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10060,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10071 =
                                  let uu____10074 = free_type_vars env1 t  in
                                  let uu____10077 =
                                    let uu____10080 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10080 ftvs  in
                                  FStar_List.append uu____10074 uu____10077
                                   in
                                (env1, uu____10071)
                            | uu____10085 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____9996 with
              | (uu____10094,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10106 =
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
                    FStar_List.append uu____10106 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10186 = desugar_term_aq env1 body  in
                        (match uu____10186 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10221 =
                                       let uu____10222 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10222
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10221
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
                             let uu____10291 =
                               let uu____10292 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10292  in
                             (uu____10291, aq))
                    | p::rest ->
                        let uu____10305 = desugar_binding_pat env1 p  in
                        (match uu____10305 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10337)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10352 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10361 =
                               match b with
                               | LetBinder uu____10402 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10471) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10525 =
                                           let uu____10534 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10534, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10525
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10596,uu____10597) ->
                                              let tup2 =
                                                let uu____10599 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10599
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10604 =
                                                  let uu____10611 =
                                                    let uu____10612 =
                                                      let uu____10629 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10632 =
                                                        let uu____10643 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10652 =
                                                          let uu____10663 =
                                                            let uu____10672 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10672
                                                             in
                                                          [uu____10663]  in
                                                        uu____10643 ::
                                                          uu____10652
                                                         in
                                                      (uu____10629,
                                                        uu____10632)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10612
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10611
                                                   in
                                                uu____10604
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10720 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10720
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10771,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10773,pats1)) ->
                                              let tupn =
                                                let uu____10818 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10818
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10831 =
                                                  let uu____10832 =
                                                    let uu____10849 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10852 =
                                                      let uu____10863 =
                                                        let uu____10874 =
                                                          let uu____10883 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10883
                                                           in
                                                        [uu____10874]  in
                                                      FStar_List.append args
                                                        uu____10863
                                                       in
                                                    (uu____10849,
                                                      uu____10852)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10832
                                                   in
                                                mk1 uu____10831  in
                                              let p2 =
                                                let uu____10931 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10931
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10978 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10361 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11070,uu____11071,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11093 =
                let uu____11094 = unparen e  in
                uu____11094.FStar_Parser_AST.tm  in
              match uu____11093 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11104 ->
                  let uu____11105 = desugar_term_aq env e  in
                  (match uu____11105 with
                   | (head1,aq) ->
                       let uu____11118 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11118, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11125 ->
            let rec aux args aqs e =
              let uu____11202 =
                let uu____11203 = unparen e  in
                uu____11203.FStar_Parser_AST.tm  in
              match uu____11202 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11221 = desugar_term_aq env t  in
                  (match uu____11221 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11269 ->
                  let uu____11270 = desugar_term_aq env e  in
                  (match uu____11270 with
                   | (head1,aq) ->
                       let uu____11291 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11291, (join_aqs (aq :: aqs))))
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
            let uu____11354 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11354
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
            let uu____11406 = desugar_term_aq env t  in
            (match uu____11406 with
             | (tm,s) ->
                 let uu____11417 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11417, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11423 =
              let uu____11436 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11436 then desugar_typ_aq else desugar_term_aq  in
            uu____11423 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11503 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11646  ->
                        match uu____11646 with
                        | (attr_opt,(p,def)) ->
                            let uu____11704 = is_app_pattern p  in
                            if uu____11704
                            then
                              let uu____11737 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11737, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11820 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11820, def1)
                               | uu____11865 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11903);
                                           FStar_Parser_AST.prange =
                                             uu____11904;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11953 =
                                            let uu____11974 =
                                              let uu____11979 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11979  in
                                            (uu____11974, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11953, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12071) ->
                                        if top_level
                                        then
                                          let uu____12107 =
                                            let uu____12128 =
                                              let uu____12133 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12133  in
                                            (uu____12128, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12107, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12224 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12257 =
                FStar_List.fold_left
                  (fun uu____12346  ->
                     fun uu____12347  ->
                       match (uu____12346, uu____12347) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12477,uu____12478),uu____12479))
                           ->
                           let uu____12613 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12653 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12653 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12688 =
                                        let uu____12691 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12691 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12688, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12707 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12707 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12613 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12257 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12960 =
                    match uu____12960 with
                    | (attrs_opt,(uu____13000,args,result_t),def) ->
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
                                let uu____13092 = is_comp_type env1 t  in
                                if uu____13092
                                then
                                  ((let uu____13096 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13106 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13106))
                                       in
                                    match uu____13096 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13113 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13116 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13116))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13113
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
                          | uu____13127 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13130 = desugar_term_aq env1 def2  in
                        (match uu____13130 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13152 =
                                     let uu____13153 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13153
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13152
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
                  let uu____13194 =
                    let uu____13211 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13211 FStar_List.unzip  in
                  (match uu____13194 with
                   | (lbs1,aqss) ->
                       let uu____13353 = desugar_term_aq env' body  in
                       (match uu____13353 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13459  ->
                                    fun used_marker  ->
                                      match uu____13459 with
                                      | (_attr_opt,(f,uu____13533,uu____13534),uu____13535)
                                          ->
                                          let uu____13592 =
                                            let uu____13594 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13594  in
                                          if uu____13592
                                          then
                                            let uu____13618 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13636 =
                                                    FStar_Ident.string_of_ident
                                                      x
                                                     in
                                                  let uu____13638 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13636, "Local",
                                                    uu____13638)
                                              | FStar_Util.Inr l ->
                                                  let uu____13643 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13645 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13643, "Global",
                                                    uu____13645)
                                               in
                                            (match uu____13618 with
                                             | (nm,gl,rng) ->
                                                 let uu____13656 =
                                                   let uu____13662 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13662)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13656)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13670 =
                                let uu____13673 =
                                  let uu____13674 =
                                    let uu____13688 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13688)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13674  in
                                FStar_All.pipe_left mk1 uu____13673  in
                              (uu____13670,
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
              let uu____13790 = desugar_term_aq env t1  in
              match uu____13790 with
              | (t11,aq0) ->
                  let uu____13811 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13811 with
                   | (env1,binder,pat1) ->
                       let uu____13841 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13883 = desugar_term_aq env1 t2  in
                             (match uu____13883 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13905 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13905
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13906 =
                                    FStar_All.pipe_left mk1
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13906, aq))
                         | LocalBinder (x,uu____13947) ->
                             let uu____13948 = desugar_term_aq env1 t2  in
                             (match uu____13948 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13970;
                                         FStar_Syntax_Syntax.p = uu____13971;_},uu____13972)::[]
                                        -> body1
                                    | uu____13985 ->
                                        let uu____13988 =
                                          let uu____13995 =
                                            let uu____13996 =
                                              let uu____14019 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14022 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14019, uu____14022)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____13996
                                             in
                                          FStar_Syntax_Syntax.mk uu____13995
                                           in
                                        uu____13988
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14059 =
                                    let uu____14062 =
                                      let uu____14063 =
                                        let uu____14077 =
                                          let uu____14080 =
                                            let uu____14081 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14081]  in
                                          FStar_Syntax_Subst.close
                                            uu____14080 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14077)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14063
                                       in
                                    FStar_All.pipe_left mk1 uu____14062  in
                                  (uu____14059, aq))
                          in
                       (match uu____13841 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14189 = FStar_List.hd lbs  in
            (match uu____14189 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14233 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14233
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____14249 =
                let uu____14250 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14250  in
              mk1 uu____14249  in
            let uu____14251 = desugar_term_aq env t1  in
            (match uu____14251 with
             | (t1',aq1) ->
                 let uu____14262 = desugar_term_aq env t2  in
                 (match uu____14262 with
                  | (t2',aq2) ->
                      let uu____14273 = desugar_term_aq env t3  in
                      (match uu____14273 with
                       | (t3',aq3) ->
                           let uu____14284 =
                             let uu____14285 =
                               let uu____14286 =
                                 let uu____14309 =
                                   let uu____14326 =
                                     let uu____14341 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14341,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14355 =
                                     let uu____14372 =
                                       let uu____14387 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14387,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14372]  in
                                   uu____14326 :: uu____14355  in
                                 (t1', uu____14309)  in
                               FStar_Syntax_Syntax.Tm_match uu____14286  in
                             mk1 uu____14285  in
                           (uu____14284, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14583 =
              match uu____14583 with
              | (pat,wopt,b) ->
                  let uu____14605 = desugar_match_pat env pat  in
                  (match uu____14605 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14636 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14636
                          in
                       let uu____14641 = desugar_term_aq env1 b  in
                       (match uu____14641 with
                        | (b1,aq) ->
                            let uu____14654 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14654, aq)))
               in
            let uu____14659 = desugar_term_aq env e  in
            (match uu____14659 with
             | (e1,aq) ->
                 let uu____14670 =
                   let uu____14701 =
                     let uu____14734 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14734 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14701
                     (fun uu____14952  ->
                        match uu____14952 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14670 with
                  | (brs,aqs) ->
                      let uu____15171 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15171, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15205 =
              let uu____15226 = is_comp_type env t  in
              if uu____15226
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15281 = desugar_term_aq env t  in
                 match uu____15281 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15205 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15373 = desugar_term_aq env e  in
                 (match uu____15373 with
                  | (e1,aq) ->
                      let uu____15384 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15384, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15423,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15466 = FStar_List.hd fields  in
              match uu____15466 with | (f,uu____15478) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15524  ->
                        match uu____15524 with
                        | (g,uu____15531) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15538,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15552 =
                         let uu____15558 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15558)
                          in
                       FStar_Errors.raise_error uu____15552
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
                  let uu____15569 =
                    let uu____15580 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15611  ->
                              match uu____15611 with
                              | (f,uu____15621) ->
                                  let uu____15622 =
                                    let uu____15623 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15623
                                     in
                                  (uu____15622, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15580)  in
                  FStar_Parser_AST.Construct uu____15569
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15641 =
                      let uu____15642 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15642  in
                    FStar_Parser_AST.mk_term uu____15641
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15644 =
                      let uu____15657 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15687  ->
                                match uu____15687 with
                                | (f,uu____15697) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15657)  in
                    FStar_Parser_AST.Record uu____15644  in
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
            let uu____15757 = desugar_term_aq env recterm1  in
            (match uu____15757 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15773;
                         FStar_Syntax_Syntax.vars = uu____15774;_},args)
                      ->
                      let uu____15800 =
                        let uu____15801 =
                          let uu____15802 =
                            let uu____15819 =
                              let uu____15822 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15823 =
                                let uu____15826 =
                                  let uu____15827 =
                                    let uu____15834 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15834)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15827
                                   in
                                FStar_Pervasives_Native.Some uu____15826  in
                              FStar_Syntax_Syntax.fvar uu____15822
                                FStar_Syntax_Syntax.delta_constant
                                uu____15823
                               in
                            (uu____15819, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15802  in
                        FStar_All.pipe_left mk1 uu____15801  in
                      (uu____15800, s)
                  | uu____15863 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15867 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15867 with
              | (constrname,is_rec) ->
                  let uu____15886 = desugar_term_aq env e  in
                  (match uu____15886 with
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
                       let uu____15906 =
                         let uu____15907 =
                           let uu____15908 =
                             let uu____15925 =
                               let uu____15928 =
                                 let uu____15929 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15929
                                  in
                               FStar_Syntax_Syntax.fvar uu____15928
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    Prims.int_one) qual
                                in
                             let uu____15931 =
                               let uu____15942 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15942]  in
                             (uu____15925, uu____15931)  in
                           FStar_Syntax_Syntax.Tm_app uu____15908  in
                         FStar_All.pipe_left mk1 uu____15907  in
                       (uu____15906, s))))
        | FStar_Parser_AST.NamedTyp (n1,e) ->
            ((let uu____15982 = FStar_Ident.range_of_id n1  in
              FStar_Errors.log_issue uu____15982
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15993 =
              let uu____15994 = FStar_Syntax_Subst.compress tm  in
              uu____15994.FStar_Syntax_Syntax.n  in
            (match uu____15993 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____16002 =
                   let uu___2119_16003 =
                     let uu____16004 =
                       let uu____16006 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16006  in
                     FStar_Syntax_Util.exp_string uu____16004  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2119_16003.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2119_16003.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____16002, noaqs)
             | uu____16007 ->
                 let uu____16008 =
                   let uu____16014 =
                     let uu____16016 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16016
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16014)  in
                 FStar_Errors.raise_error uu____16008
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16025 = desugar_term_aq env e  in
            (match uu____16025 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16037 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16037, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16042 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16043 =
              let uu____16044 =
                let uu____16051 = desugar_term env e  in (bv, uu____16051)
                 in
              [uu____16044]  in
            (uu____16042, uu____16043)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16076 =
              let uu____16077 =
                let uu____16078 =
                  let uu____16085 = desugar_term env e  in (uu____16085, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16078  in
              FStar_All.pipe_left mk1 uu____16077  in
            (uu____16076, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16114 -> false  in
              let uu____16116 =
                let uu____16117 = unparen rel1  in
                uu____16117.FStar_Parser_AST.tm  in
              match uu____16116 with
              | FStar_Parser_AST.Op (id1,uu____16120) ->
                  let uu____16125 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id1
                     in
                  (match uu____16125 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16133 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16133 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id1 ->
                  let uu____16144 = FStar_Syntax_DsEnv.try_lookup_id env id1
                     in
                  (match uu____16144 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16150 -> false  in
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
              let uu____16171 =
                let uu____16172 =
                  let uu____16179 =
                    let uu____16180 =
                      let uu____16181 =
                        let uu____16190 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16203 =
                          let uu____16204 =
                            let uu____16205 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16205  in
                          FStar_Parser_AST.mk_term uu____16204
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16190, uu____16203,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16181  in
                    FStar_Parser_AST.mk_term uu____16180
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16179)  in
                FStar_Parser_AST.Abs uu____16172  in
              FStar_Parser_AST.mk_term uu____16171
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
              let uu____16226 = FStar_List.last steps  in
              match uu____16226 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16229,uu____16230,last_expr)) -> last_expr
              | uu____16232 -> failwith "impossible: no last_expr on calc"
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
            let uu____16260 =
              FStar_List.fold_left
                (fun uu____16278  ->
                   fun uu____16279  ->
                     match (uu____16278, uu____16279) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16302 = is_impl rel2  in
                           if uu____16302
                           then
                             let uu____16305 =
                               let uu____16312 =
                                 let uu____16317 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16317, FStar_Parser_AST.Nothing)  in
                               [uu____16312]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16305 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16329 =
                             let uu____16336 =
                               let uu____16343 =
                                 let uu____16350 =
                                   let uu____16357 =
                                     let uu____16362 = eta_and_annot rel2  in
                                     (uu____16362, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16363 =
                                     let uu____16370 =
                                       let uu____16377 =
                                         let uu____16382 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16382,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16383 =
                                         let uu____16390 =
                                           let uu____16395 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16395,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16390]  in
                                       uu____16377 :: uu____16383  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16370
                                      in
                                   uu____16357 :: uu____16363  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16350
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16343
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16336
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16329
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16260 with
             | (e1,uu____16433) ->
                 let e2 =
                   let uu____16435 =
                     let uu____16442 =
                       let uu____16449 =
                         let uu____16456 =
                           let uu____16461 = FStar_Parser_AST.thunk e1  in
                           (uu____16461, FStar_Parser_AST.Nothing)  in
                         [uu____16456]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16449  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16442  in
                   FStar_Parser_AST.mkApp finish1 uu____16435
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16478 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16479 = desugar_formula env top  in
            (uu____16479, noaqs)
        | uu____16480 ->
            let uu____16481 =
              let uu____16487 =
                let uu____16489 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16489  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16487)  in
            FStar_Errors.raise_error uu____16481 top.FStar_Parser_AST.range

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
           (fun uu____16533  ->
              match uu____16533 with
              | (a,imp) ->
                  let uu____16546 = desugar_term env a  in
                  arg_withimp_e imp uu____16546))

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
          let is_requires uu____16583 =
            match uu____16583 with
            | (t1,uu____16590) ->
                let uu____16591 =
                  let uu____16592 = unparen t1  in
                  uu____16592.FStar_Parser_AST.tm  in
                (match uu____16591 with
                 | FStar_Parser_AST.Requires uu____16594 -> true
                 | uu____16603 -> false)
             in
          let is_ensures uu____16615 =
            match uu____16615 with
            | (t1,uu____16622) ->
                let uu____16623 =
                  let uu____16624 = unparen t1  in
                  uu____16624.FStar_Parser_AST.tm  in
                (match uu____16623 with
                 | FStar_Parser_AST.Ensures uu____16626 -> true
                 | uu____16635 -> false)
             in
          let is_app head1 uu____16653 =
            match uu____16653 with
            | (t1,uu____16661) ->
                let uu____16662 =
                  let uu____16663 = unparen t1  in
                  uu____16663.FStar_Parser_AST.tm  in
                (match uu____16662 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16666;
                        FStar_Parser_AST.level = uu____16667;_},uu____16668,uu____16669)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____16671 -> false)
             in
          let is_smt_pat uu____16683 =
            match uu____16683 with
            | (t1,uu____16690) ->
                let uu____16691 =
                  let uu____16692 = unparen t1  in
                  uu____16692.FStar_Parser_AST.tm  in
                (match uu____16691 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16696);
                               FStar_Parser_AST.range = uu____16697;
                               FStar_Parser_AST.level = uu____16698;_},uu____16699)::uu____16700::[])
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
                               FStar_Parser_AST.range = uu____16749;
                               FStar_Parser_AST.level = uu____16750;_},uu____16751)::uu____16752::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16785 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16820 = head_and_args t1  in
            match uu____16820 with
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
                     let thunk_ens uu____16913 =
                       match uu____16913 with
                       | (e,i) ->
                           let uu____16924 = FStar_Parser_AST.thunk e  in
                           (uu____16924, i)
                        in
                     let fail_lemma uu____16936 =
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
                           let uu____17042 =
                             let uu____17049 =
                               let uu____17056 = thunk_ens ens  in
                               [uu____17056; nil_pat]  in
                             req_true :: uu____17049  in
                           unit_tm :: uu____17042
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17103 =
                             let uu____17110 =
                               let uu____17117 = thunk_ens ens  in
                               [uu____17117; nil_pat]  in
                             req :: uu____17110  in
                           unit_tm :: uu____17103
                       | ens::smtpat::[] when
                           (((let uu____17166 = is_requires ens  in
                              Prims.op_Negation uu____17166) &&
                               (let uu____17169 = is_smt_pat ens  in
                                Prims.op_Negation uu____17169))
                              &&
                              (let uu____17172 = is_decreases ens  in
                               Prims.op_Negation uu____17172))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17174 =
                             let uu____17181 =
                               let uu____17188 = thunk_ens ens  in
                               [uu____17188; smtpat]  in
                             req_true :: uu____17181  in
                           unit_tm :: uu____17174
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17235 =
                             let uu____17242 =
                               let uu____17249 = thunk_ens ens  in
                               [uu____17249; nil_pat; dec]  in
                             req_true :: uu____17242  in
                           unit_tm :: uu____17235
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17309 =
                             let uu____17316 =
                               let uu____17323 = thunk_ens ens  in
                               [uu____17323; smtpat; dec]  in
                             req_true :: uu____17316  in
                           unit_tm :: uu____17309
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17383 =
                             let uu____17390 =
                               let uu____17397 = thunk_ens ens  in
                               [uu____17397; nil_pat; dec]  in
                             req :: uu____17390  in
                           unit_tm :: uu____17383
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17457 =
                             let uu____17464 =
                               let uu____17471 = thunk_ens ens  in
                               [uu____17471; smtpat]  in
                             req :: uu____17464  in
                           unit_tm :: uu____17457
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17536 =
                             let uu____17543 =
                               let uu____17550 = thunk_ens ens  in
                               [uu____17550; dec; smtpat]  in
                             req :: uu____17543  in
                           unit_tm :: uu____17536
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17612 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17612, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17640 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17640
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____17643 =
                       let uu____17650 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17650, [])  in
                     (uu____17643, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17668 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17668
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____17671 =
                       let uu____17678 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17678, [])  in
                     (uu____17671, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17700 =
                       let uu____17707 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17707, [])  in
                     (uu____17700, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17730 when allow_type_promotion ->
                     let default_effect =
                       let uu____17732 = FStar_Options.ml_ish ()  in
                       if uu____17732
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17738 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17738
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17745 =
                       let uu____17752 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17752, [])  in
                     (uu____17745, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17775 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17794 = pre_process_comp_typ t  in
          match uu____17794 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17846 =
                    let uu____17852 =
                      let uu____17854 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17854
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17852)
                     in
                  fail1 uu____17846)
               else ();
               (let is_universe uu____17870 =
                  match uu____17870 with
                  | (uu____17876,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17878 = FStar_Util.take is_universe args  in
                match uu____17878 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17937  ->
                           match uu____17937 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17944 =
                      let uu____17959 = FStar_List.hd args1  in
                      let uu____17968 = FStar_List.tl args1  in
                      (uu____17959, uu____17968)  in
                    (match uu____17944 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18023 =
                           let is_decrease uu____18062 =
                             match uu____18062 with
                             | (t1,uu____18073) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18084;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18085;_},uu____18086::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18125 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18023 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18242  ->
                                        match uu____18242 with
                                        | (t1,uu____18252) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18261,(arg,uu____18263)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18302 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18323 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18335 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18335
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18342 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18342
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18352 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18352
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18359 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18359
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18366 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18366
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18373 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18373
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18394 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18394
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
                                                    let uu____18485 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18485
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
                                              | uu____18506 -> pat  in
                                            let uu____18507 =
                                              let uu____18518 =
                                                let uu____18529 =
                                                  let uu____18538 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18538, aq)  in
                                                [uu____18529]  in
                                              ens :: uu____18518  in
                                            req :: uu____18507
                                        | uu____18579 -> rest2
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
        let uu___2444_18614 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2444_18614.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2444_18614.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2451_18668 = b  in
             {
               FStar_Parser_AST.b = (uu___2451_18668.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2451_18668.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2451_18668.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18697 body1 =
          match uu____18697 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18743::uu____18744) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18762 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2470_18789 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2470_18789.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2470_18789.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18852 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18852))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18883 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18883 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2483_18893 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2483_18893.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2483_18893.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18899 =
                     let uu____18902 =
                       let uu____18903 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18903]  in
                     no_annot_abs uu____18902 body2  in
                   FStar_All.pipe_left setpos uu____18899  in
                 let uu____18924 =
                   let uu____18925 =
                     let uu____18942 =
                       let uu____18945 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18945
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____18947 =
                       let uu____18958 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18958]  in
                     (uu____18942, uu____18947)  in
                   FStar_Syntax_Syntax.Tm_app uu____18925  in
                 FStar_All.pipe_left mk1 uu____18924)
        | uu____18997 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19062 = q (rest, pats, body)  in
              let uu____19065 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19062 uu____19065
                FStar_Parser_AST.Formula
               in
            let uu____19066 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19066 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19077 -> failwith "impossible"  in
      let uu____19081 =
        let uu____19082 = unparen f  in uu____19082.FStar_Parser_AST.tm  in
      match uu____19081 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19095,uu____19096) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19120,uu____19121) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19177 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19177
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19221 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19221
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19285 -> desugar_term env f

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
          let uu____19296 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19296)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19301 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19301)
      | FStar_Parser_AST.TVariable x ->
          let uu____19305 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____19305)
      | FStar_Parser_AST.NoName t ->
          let uu____19309 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19309)
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
      fun uu___11_19317  ->
        match uu___11_19317 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19339 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19339, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19356 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19356 with
             | (env1,a1) ->
                 let uu____19373 =
                   let uu____19380 = trans_aqual env1 imp  in
                   ((let uu___2583_19386 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2583_19386.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2583_19386.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19380)
                    in
                 (uu____19373, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19394  ->
      match uu___12_19394 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19398 =
            let uu____19399 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19399  in
          FStar_Pervasives_Native.Some uu____19398
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19427 =
        FStar_List.fold_left
          (fun uu____19460  ->
             fun b  ->
               match uu____19460 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2601_19504 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2601_19504.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2601_19504.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2601_19504.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19519 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19519 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2611_19537 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2611_19537.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2611_19537.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19538 =
                               let uu____19545 =
                                 let uu____19550 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19550)  in
                               uu____19545 :: out  in
                             (env2, uu____19538))
                    | uu____19561 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19427 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19649 =
          let uu____19650 = unparen t  in uu____19650.FStar_Parser_AST.tm  in
        match uu____19649 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____19651; FStar_Ident.ident = uu____19652;
              FStar_Ident.nsstr = uu____19653; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____19658 ->
            let uu____19659 =
              let uu____19665 =
                let uu____19667 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19667  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19665)  in
            FStar_Errors.raise_error uu____19659 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19684) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19686) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19689 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19707 = binder_ident b  in
         FStar_Common.list_of_option uu____19707) bs
  
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
               (fun uu___13_19744  ->
                  match uu___13_19744 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19749 -> false))
           in
        let quals2 q =
          let uu____19763 =
            (let uu____19767 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19767) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19763
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19784 = FStar_Ident.range_of_lid disc_name  in
                let uu____19785 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19784;
                  FStar_Syntax_Syntax.sigquals = uu____19785;
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
            let uu____19825 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19863  ->
                        match uu____19863 with
                        | (x,uu____19874) ->
                            let uu____19879 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19879 with
                             | (field_name,uu____19887) ->
                                 let only_decl =
                                   ((let uu____19892 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19892)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19894 =
                                        let uu____19896 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19896.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19894)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19914 =
                                       FStar_List.filter
                                         (fun uu___14_19918  ->
                                            match uu___14_19918 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19921 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19914
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___15_19936  ->
                                             match uu___15_19936 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19941 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19944 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19944;
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
                                      let uu____19951 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19951
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one
                                       in
                                    let lb =
                                      let uu____19962 =
                                        let uu____19967 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19967  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19962;
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
                                      let uu____19971 =
                                        let uu____19972 =
                                          let uu____19979 =
                                            let uu____19982 =
                                              let uu____19983 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19983
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19982]  in
                                          ((false, [lb]), uu____19979)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19972
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19971;
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
            FStar_All.pipe_right uu____19825 FStar_List.flatten
  
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
            (lid,uu____20032,t,uu____20034,n1,uu____20036) when
            let uu____20043 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20043 ->
            let uu____20045 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20045 with
             | (formals,uu____20063) ->
                 (match formals with
                  | [] -> []
                  | uu____20092 ->
                      let filter_records uu___16_20108 =
                        match uu___16_20108 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20111,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20123 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20125 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20125 with
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
                      let uu____20137 = FStar_Util.first_N n1 formals  in
                      (match uu____20137 with
                       | (uu____20166,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20200 -> []
  
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
                        let uu____20294 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20294
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20318 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20318
                        then
                          let uu____20324 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20324
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20328 =
                          let uu____20333 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20333  in
                        let uu____20334 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20340 =
                              let uu____20343 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20343  in
                            FStar_Syntax_Util.arrow typars uu____20340
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20348 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20328;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20334;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20348;
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
          let tycon_id uu___17_20402 =
            match uu___17_20402 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____20404,uu____20405) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____20415,uu____20416,uu____20417) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____20427,uu____20428,uu____20429) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____20451,uu____20452,uu____20453) -> id1
             in
          let binder_to_term1 b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20491) ->
                let uu____20492 =
                  let uu____20493 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20493  in
                FStar_Parser_AST.mk_term uu____20492 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20495 =
                  let uu____20496 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20496  in
                FStar_Parser_AST.mk_term uu____20495 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20498) ->
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
              | uu____20529 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20537 =
                     let uu____20538 =
                       let uu____20545 = binder_to_term1 b  in
                       (out, uu____20545, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20538  in
                   FStar_Parser_AST.mk_term uu____20537
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20557 =
            match uu___18_20557 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____20601  ->
                       match uu____20601 with
                       | (x,t) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20609 =
                    let uu____20610 =
                      let uu____20611 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____20611  in
                    FStar_Parser_AST.mk_term uu____20610
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20609 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____20618 = binder_idents parms  in id1 ::
                    uu____20618
                   in
                (FStar_List.iter
                   (fun uu____20631  ->
                      match uu____20631 with
                      | (f,uu____20637) ->
                          let uu____20638 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____20638
                          then
                            let uu____20643 =
                              let uu____20649 =
                                let uu____20651 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20651
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20649)
                               in
                            FStar_Errors.raise_error uu____20643
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____20657 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20657)))
            | uu____20711 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20751 =
            match uu___19_20751 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20775 = typars_of_binders _env binders  in
                (match uu____20775 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20811 =
                         let uu____20812 =
                           let uu____20813 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20813  in
                         FStar_Parser_AST.mk_term uu____20812
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20811 binders  in
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
                     let uu____20822 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20822 with
                      | (_env1,uu____20839) ->
                          let uu____20846 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id1 FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20846 with
                           | (_env2,uu____20863) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20870 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20913 =
              FStar_List.fold_left
                (fun uu____20947  ->
                   fun uu____20948  ->
                     match (uu____20947, uu____20948) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21017 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21017 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20913 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21108 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____21108
                | uu____21109 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____21117 = desugar_abstract_tc quals env [] tc  in
              (match uu____21117 with
               | (uu____21130,uu____21131,se,uu____21133) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21136,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21155 =
                                 let uu____21157 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21157  in
                               if uu____21155
                               then
                                 let uu____21160 =
                                   let uu____21166 =
                                     let uu____21168 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21168
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21166)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21160
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
                           | uu____21181 ->
                               let uu____21182 =
                                 let uu____21189 =
                                   let uu____21190 =
                                     let uu____21205 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21205)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21190
                                    in
                                 FStar_Syntax_Syntax.mk uu____21189  in
                               uu____21182 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2894_21218 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2894_21218.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2894_21218.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2894_21218.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2894_21218.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21219 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____21234 = typars_of_binders env binders  in
              (match uu____21234 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21268 =
                           FStar_Util.for_some
                             (fun uu___20_21271  ->
                                match uu___20_21271 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21274 -> false) quals
                            in
                         if uu____21268
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21282 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21282
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21287 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21293  ->
                               match uu___21_21293 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21296 -> false))
                        in
                     if uu____21287
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____21310 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21310
                     then
                       let uu____21316 =
                         let uu____21323 =
                           let uu____21324 = unparen t  in
                           uu____21324.FStar_Parser_AST.tm  in
                         match uu____21323 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____21345 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21375)::args_rev ->
                                   let uu____21387 =
                                     let uu____21388 = unparen last_arg  in
                                     uu____21388.FStar_Parser_AST.tm  in
                                   (match uu____21387 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21416 -> ([], args))
                               | uu____21425 -> ([], args)  in
                             (match uu____21345 with
                              | (cattributes,args1) ->
                                  let uu____21464 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21464))
                         | uu____21475 -> (t, [])  in
                       match uu____21316 with
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
                                  (fun uu___22_21498  ->
                                     match uu___22_21498 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21501 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21509)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21529 = tycon_record_as_variant trec  in
              (match uu____21529 with
               | (t,fs) ->
                   let uu____21546 =
                     let uu____21549 =
                       let uu____21550 =
                         let uu____21559 =
                           let uu____21562 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21562  in
                         (uu____21559, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21550  in
                     uu____21549 :: quals  in
                   desugar_tycon env d uu____21546 [t])
          | uu____21567::uu____21568 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21726 = et  in
                match uu____21726 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21936 ->
                         let trec = tc  in
                         let uu____21956 = tycon_record_as_variant trec  in
                         (match uu____21956 with
                          | (t,fs) ->
                              let uu____22012 =
                                let uu____22015 =
                                  let uu____22016 =
                                    let uu____22025 =
                                      let uu____22028 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22028  in
                                    (uu____22025, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22016
                                   in
                                uu____22015 :: quals1  in
                              collect_tcs uu____22012 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____22106 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22106 with
                          | (env2,uu____22163,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____22300 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22300 with
                          | (env2,uu____22357,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22473 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22519 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22519 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_22971  ->
                             match uu___24_22971 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____23025,uu____23026);
                                    FStar_Syntax_Syntax.sigrng = uu____23027;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23028;
                                    FStar_Syntax_Syntax.sigmeta = uu____23029;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23030;
                                    FStar_Syntax_Syntax.sigopts = uu____23031;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23093 =
                                     typars_of_binders env1 binders  in
                                   match uu____23093 with
                                   | (env2,tpars1) ->
                                       let uu____23120 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23120 with
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
                                 let uu____23149 =
                                   let uu____23160 =
                                     mk_typ_abbrev env1 d id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ([], uu____23160)  in
                                 [uu____23149]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____23196);
                                    FStar_Syntax_Syntax.sigrng = uu____23197;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23199;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23200;
                                    FStar_Syntax_Syntax.sigopts = uu____23201;_},constrs,tconstr,quals1)
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
                                 let uu____23292 = push_tparams env1 tpars
                                    in
                                 (match uu____23292 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23351  ->
                                             match uu____23351 with
                                             | (x,uu____23363) ->
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
                                        let uu____23374 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23374
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23397 =
                                        let uu____23416 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23493  ->
                                                  match uu____23493 with
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
                                                        let uu____23536 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23536
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
                                                                uu___23_23547
                                                                 ->
                                                                match uu___23_23547
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23559
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23567 =
                                                        let uu____23578 =
                                                          let uu____23579 =
                                                            let uu____23580 =
                                                              let uu____23596
                                                                =
                                                                let uu____23597
                                                                  =
                                                                  let uu____23600
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23600
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23597
                                                                 in
                                                              (name, univs1,
                                                                uu____23596,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23580
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23579;
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
                                                        (tps, uu____23578)
                                                         in
                                                      (name, uu____23567)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23416
                                         in
                                      (match uu____23397 with
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
                             | uu____23732 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23813  ->
                             match uu____23813 with | (uu____23824,se) -> se))
                      in
                   let uu____23838 =
                     let uu____23845 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23845 rng
                      in
                   (match uu____23838 with
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
                               (fun uu____23890  ->
                                  match uu____23890 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23938,tps,k,uu____23941,constrs)
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
                                      let uu____23962 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23977 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23994,uu____23995,uu____23996,uu____23997,uu____23998)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24005
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23977
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24009 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24016  ->
                                                          match uu___25_24016
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24018 ->
                                                              true
                                                          | uu____24028 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24009))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23962
                                  | uu____24030 -> []))
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
      let uu____24067 =
        FStar_List.fold_left
          (fun uu____24102  ->
             fun b  ->
               match uu____24102 with
               | (env1,binders1) ->
                   let uu____24146 = desugar_binder env1 b  in
                   (match uu____24146 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24169 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24169 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24222 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24067 with
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
          let uu____24326 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24333  ->
                    match uu___26_24333 with
                    | FStar_Syntax_Syntax.Reflectable uu____24335 -> true
                    | uu____24337 -> false))
             in
          if uu____24326
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24342 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24342
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
        let warn1 uu____24393 =
          if warn
          then
            let uu____24395 =
              let uu____24401 =
                let uu____24403 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24403
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24401)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24395
          else ()  in
        let uu____24409 = FStar_Syntax_Util.head_and_args at  in
        match uu____24409 with
        | (hd1,args) ->
            let uu____24462 =
              let uu____24463 = FStar_Syntax_Subst.compress hd1  in
              uu____24463.FStar_Syntax_Syntax.n  in
            (match uu____24462 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24507)::[] ->
                      let uu____24532 =
                        let uu____24537 =
                          let uu____24546 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24546 a1  in
                        uu____24537 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24532 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24569 =
                             let uu____24575 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24575  in
                           (uu____24569, true)
                       | uu____24590 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24606 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24628 -> (FStar_Pervasives_Native.None, false))
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____24655 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____24655 with
        | FStar_Pervasives_Native.None  ->
            let uu____24658 =
              let uu____24664 =
                let uu____24666 =
                  let uu____24668 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____24668 " not found"  in
                Prims.op_Hat "Effect name " uu____24666  in
              (FStar_Errors.Fatal_EffectNotFound, uu____24664)  in
            FStar_Errors.raise_error uu____24658 r
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
                    let uu____24824 = desugar_binders monad_env eff_binders
                       in
                    match uu____24824 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____24863 =
                            let uu____24872 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24872  in
                          FStar_List.length uu____24863  in
                        (if is_layered1 && (num_indices <= Prims.int_one)
                         then
                           (let uu____24906 =
                              let uu____24912 =
                                let uu____24914 =
                                  let uu____24916 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____24916
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____24914  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____24912)
                               in
                            FStar_Errors.raise_error uu____24906
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
                                (uu____24984,uu____24985,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____24987,uu____24988,uu____24989))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25004 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25007 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25019 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25019 mandatory_members)
                              eff_decls
                             in
                          match uu____25007 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25038 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25067  ->
                                        fun decl  ->
                                          match uu____25067 with
                                          | (env2,out) ->
                                              let uu____25087 =
                                                desugar_decl env2 decl  in
                                              (match uu____25087 with
                                               | (env3,ses) ->
                                                   let uu____25100 =
                                                     let uu____25103 =
                                                       FStar_List.hd ses  in
                                                     uu____25103 :: out  in
                                                   (env3, uu____25100)))
                                     (env1, []))
                                 in
                              (match uu____25038 with
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
                                                 (uu____25149,uu____25150,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25153,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25154,(def,uu____25156)::
                                                        (cps_type,uu____25158)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25159;
                                                     FStar_Parser_AST.level =
                                                       uu____25160;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25193 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25193 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25225 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25226 =
                                                        let uu____25227 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25227
                                                         in
                                                      let uu____25234 =
                                                        let uu____25235 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25235
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25225;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25226;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25234
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25242,uu____25243,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25246,defn))::[])
                                                 when for_free || is_layered1
                                                 ->
                                                 let uu____25262 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25262 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25294 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25295 =
                                                        let uu____25296 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25296
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25294;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25295;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25303 ->
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
                                       let uu____25322 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25322
                                        in
                                     let uu____25324 =
                                       let uu____25325 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25325
                                        in
                                     ([], uu____25324)  in
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
                                       let uu____25347 =
                                         let uu____25348 =
                                           let uu____25351 = lookup1 "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25351
                                            in
                                         let uu____25353 =
                                           let uu____25356 = lookup1 "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25356
                                            in
                                         let uu____25358 =
                                           let uu____25361 = lookup1 "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25361
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
                                             uu____25348;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25353;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25358
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25347
                                     else
                                       if is_layered1
                                       then
                                         (let to_comb uu____25395 =
                                            match uu____25395 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____25442 =
                                            let uu____25443 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____25445 =
                                              let uu____25450 =
                                                lookup1 "repr"  in
                                              FStar_All.pipe_right
                                                uu____25450 to_comb
                                               in
                                            let uu____25468 =
                                              let uu____25473 =
                                                lookup1 "return"  in
                                              FStar_All.pipe_right
                                                uu____25473 to_comb
                                               in
                                            let uu____25491 =
                                              let uu____25496 =
                                                lookup1 "bind"  in
                                              FStar_All.pipe_right
                                                uu____25496 to_comb
                                               in
                                            let uu____25514 =
                                              let uu____25519 =
                                                lookup1 "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____25519 to_comb
                                               in
                                            let uu____25537 =
                                              let uu____25542 =
                                                lookup1 "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____25542 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____25443;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____25445;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____25468;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____25491;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____25514;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____25537
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____25442)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_25565  ->
                                                 match uu___27_25565 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____25568 -> true
                                                 | uu____25570 -> false)
                                              qualifiers
                                             in
                                          let uu____25572 =
                                            let uu____25573 =
                                              lookup1 "return_wp"  in
                                            let uu____25575 =
                                              lookup1 "bind_wp"  in
                                            let uu____25577 =
                                              lookup1 "stronger"  in
                                            let uu____25579 =
                                              lookup1 "if_then_else"  in
                                            let uu____25581 =
                                              lookup1 "ite_wp"  in
                                            let uu____25583 =
                                              lookup1 "close_wp"  in
                                            let uu____25585 =
                                              lookup1 "trivial"  in
                                            let uu____25587 =
                                              if rr
                                              then
                                                let uu____25593 =
                                                  lookup1 "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25593
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25597 =
                                              if rr
                                              then
                                                let uu____25603 =
                                                  lookup1 "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25603
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25607 =
                                              if rr
                                              then
                                                let uu____25613 =
                                                  lookup1 "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25613
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____25573;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____25575;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____25577;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____25579;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____25581;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____25583;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____25585;
                                              FStar_Syntax_Syntax.repr =
                                                uu____25587;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____25597;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____25607
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____25572)
                                      in
                                   let sigel =
                                     let uu____25618 =
                                       let uu____25619 =
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
                                           uu____25619
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____25618
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
                                               let uu____25636 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____25636) env3)
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
                let uu____25659 = desugar_binders env1 eff_binders  in
                match uu____25659 with
                | (env2,binders) ->
                    let uu____25696 =
                      let uu____25707 = head_and_args defn  in
                      match uu____25707 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25744 ->
                                let uu____25745 =
                                  let uu____25751 =
                                    let uu____25753 =
                                      let uu____25755 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25755 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25753  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25751)
                                   in
                                FStar_Errors.raise_error uu____25745
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25761 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25791)::args_rev ->
                                let uu____25803 =
                                  let uu____25804 = unparen last_arg  in
                                  uu____25804.FStar_Parser_AST.tm  in
                                (match uu____25803 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25832 -> ([], args))
                            | uu____25841 -> ([], args)  in
                          (match uu____25761 with
                           | (cattributes,args1) ->
                               let uu____25884 = desugar_args env2 args1  in
                               let uu____25885 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25884, uu____25885))
                       in
                    (match uu____25696 with
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
                          (let uu____25925 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25925 with
                           | (ed_binders,uu____25939,ed_binders_opening) ->
                               let sub' shift_n uu____25958 =
                                 match uu____25958 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25973 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25973 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25977 =
                                       let uu____25978 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25978)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25977
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25999 =
                                   sub1 ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26000 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub1 ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26001 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26017 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26018 =
                                          let uu____26019 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26019
                                           in
                                        let uu____26034 =
                                          let uu____26035 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26035
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26017;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26018;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26034
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
                                     uu____25999;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26000;
                                   FStar_Syntax_Syntax.actions = uu____26001;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26051 =
                                   let uu____26054 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26054 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26051;
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
                                           let uu____26069 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26069) env3)
                                  in
                               let env5 =
                                 let uu____26071 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26071
                                 then
                                   let reflect_lid =
                                     let uu____26078 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26078
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
        let uu____26095 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26095 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26110 = desugar_decl_noattrs env d  in
      match uu____26110 with
      | (env1,sigelts) ->
          let val_attrs =
            match sigelts with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____26126;
                FStar_Syntax_Syntax.sigrng = uu____26127;
                FStar_Syntax_Syntax.sigquals = uu____26128;
                FStar_Syntax_Syntax.sigmeta = uu____26129;
                FStar_Syntax_Syntax.sigattrs = uu____26130;
                FStar_Syntax_Syntax.sigopts = uu____26131;_}::[] ->
                let uu____26144 =
                  let uu____26147 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____26147  in
                FStar_All.pipe_right uu____26144
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____26155 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____26155))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____26168;
                FStar_Syntax_Syntax.sigrng = uu____26169;
                FStar_Syntax_Syntax.sigquals = uu____26170;
                FStar_Syntax_Syntax.sigmeta = uu____26171;
                FStar_Syntax_Syntax.sigattrs = uu____26172;
                FStar_Syntax_Syntax.sigopts = uu____26173;_}::uu____26174 ->
                let uu____26199 =
                  let uu____26202 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____26202  in
                FStar_All.pipe_right uu____26199
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____26210 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____26210))
            | uu____26223 -> []  in
          let attrs1 = FStar_List.append attrs val_attrs  in
          let uu____26227 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3427_26231 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3427_26231.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3427_26231.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3427_26231.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3427_26231.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3427_26231.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____26227)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26238 = desugar_decl_aux env d  in
      match uu____26238 with
      | (env1,ses) ->
          let uu____26249 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26249)

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
          let uu____26281 = FStar_Syntax_DsEnv.iface env  in
          if uu____26281
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26296 =
               let uu____26298 =
                 let uu____26300 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26301 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26300
                   uu____26301
                  in
               Prims.op_Negation uu____26298  in
             if uu____26296
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26315 =
                  let uu____26317 =
                    let uu____26319 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26319 lid  in
                  Prims.op_Negation uu____26317  in
                if uu____26315
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26333 =
                     let uu____26335 =
                       let uu____26337 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26337
                         lid
                        in
                     Prims.op_Negation uu____26335  in
                   if uu____26333
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26355 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26355, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26384)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26403 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____26412 =
            let uu____26417 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26417 tcs  in
          (match uu____26412 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26434 =
                   let uu____26435 =
                     let uu____26442 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26442  in
                   [uu____26435]  in
                 let uu____26455 =
                   let uu____26458 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26461 =
                     let uu____26472 =
                       let uu____26481 =
                         let uu____26482 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26482  in
                       FStar_Syntax_Syntax.as_arg uu____26481  in
                     [uu____26472]  in
                   FStar_Syntax_Util.mk_app uu____26458 uu____26461  in
                 FStar_Syntax_Util.abs uu____26434 uu____26455
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26522,id1))::uu____26524 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26527::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26531 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26531 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26537 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26537]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26558) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26568,uu____26569,uu____26570,uu____26571,uu____26572)
                     ->
                     let uu____26581 =
                       let uu____26582 =
                         let uu____26583 =
                           let uu____26590 = mkclass lid  in
                           (meths, uu____26590)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26583  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26582;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____26581]
                 | uu____26593 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26627;
                    FStar_Parser_AST.prange = uu____26628;_},uu____26629)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26639;
                    FStar_Parser_AST.prange = uu____26640;_},uu____26641)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26657;
                         FStar_Parser_AST.prange = uu____26658;_},uu____26659);
                    FStar_Parser_AST.prange = uu____26660;_},uu____26661)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26683;
                         FStar_Parser_AST.prange = uu____26684;_},uu____26685);
                    FStar_Parser_AST.prange = uu____26686;_},uu____26687)::[]
                   -> false
               | (p,uu____26716)::[] ->
                   let uu____26725 = is_app_pattern p  in
                   Prims.op_Negation uu____26725
               | uu____26727 -> false)
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
            let uu____26802 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26802 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26815 =
                     let uu____26816 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26816.FStar_Syntax_Syntax.n  in
                   match uu____26815 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26826) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____26857 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____26882  ->
                                match uu____26882 with
                                | (qs,ats) ->
                                    let uu____26909 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____26909 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____26857 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____26963::uu____26964 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____26967 -> val_quals  in
                            let quals2 =
                              let uu____26971 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27004  ->
                                        match uu____27004 with
                                        | (uu____27018,(uu____27019,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____26971
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____27039 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____27039
                              then
                                let uu____27045 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3604_27060 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3606_27062 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3606_27062.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3606_27062.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3604_27060.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3604_27060.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3604_27060.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3604_27060.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3604_27060.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3604_27060.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____27045)
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
                   | uu____27087 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27095 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27114 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27095 with
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
                       let uu___3629_27151 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3629_27151.FStar_Parser_AST.prange)
                       }
                   | uu____27158 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3633_27165 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3633_27165.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3633_27165.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____27181 =
                     let uu____27182 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____27182  in
                   FStar_Parser_AST.mk_term uu____27181
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____27206 id_opt =
                   match uu____27206 with
                   | (env1,ses) ->
                       let uu____27228 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id1 ->
                             let lid = FStar_Ident.lid_of_ids [id1]  in
                             let branch1 =
                               let uu____27240 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____27240
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____27242 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____27242
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
                               let uu____27248 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____27248
                                in
                             let bv_pat1 =
                               let uu____27252 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____27252
                                in
                             (bv_pat1, branch1)
                          in
                       (match uu____27228 with
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
                            let uu____27313 = desugar_decl env1 id_decl  in
                            (match uu____27313 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____27349 id1 =
                   match uu____27349 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id1)
                    in
                 let build_coverage_check uu____27388 =
                   match uu____27388 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____27412 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____27412 FStar_Util.set_elements
                    in
                 let uu____27419 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____27422 = is_var_pattern pat  in
                      Prims.op_Negation uu____27422)
                    in
                 if uu____27419
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
            let uu____27446 = close_fun env t  in
            desugar_term env uu____27446  in
          let quals1 =
            let uu____27450 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27450
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27462 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27462;
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
                let uu____27475 =
                  let uu____27484 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27484]  in
                let uu____27503 =
                  let uu____27506 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27506
                   in
                FStar_Syntax_Util.arrow uu____27475 uu____27503
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
          let uu____27572 =
            let uu____27574 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____27574  in
          if uu____27572
          then
            let uu____27581 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____27599 =
                    let uu____27602 =
                      let uu____27603 = desugar_term env t  in
                      ([], uu____27603)  in
                    FStar_Pervasives_Native.Some uu____27602  in
                  (uu____27599, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____27616 =
                    let uu____27619 =
                      let uu____27620 = desugar_term env wp  in
                      ([], uu____27620)  in
                    FStar_Pervasives_Native.Some uu____27619  in
                  let uu____27627 =
                    let uu____27630 =
                      let uu____27631 = desugar_term env t  in
                      ([], uu____27631)  in
                    FStar_Pervasives_Native.Some uu____27630  in
                  (uu____27616, uu____27627)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____27643 =
                    let uu____27646 =
                      let uu____27647 = desugar_term env t  in
                      ([], uu____27647)  in
                    FStar_Pervasives_Native.Some uu____27646  in
                  (FStar_Pervasives_Native.None, uu____27643)
               in
            (match uu____27581 with
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
                   let uu____27681 =
                     let uu____27684 =
                       let uu____27685 = desugar_term env t  in
                       ([], uu____27685)  in
                     FStar_Pervasives_Native.Some uu____27684  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____27681
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
             | uu____27692 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind1) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n1 = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____27705 =
            let uu____27706 =
              let uu____27707 =
                let uu____27708 =
                  let uu____27719 =
                    let uu____27720 = desugar_term env bind1  in
                    ([], uu____27720)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n1.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____27719,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____27708  in
              {
                FStar_Syntax_Syntax.sigel = uu____27707;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____27706]  in
          (env, uu____27705)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____27739 =
              let uu____27740 =
                let uu____27747 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27747, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27740  in
            {
              FStar_Syntax_Syntax.sigel = uu____27739;
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = [];
              FStar_Syntax_Syntax.sigmeta =
                FStar_Syntax_Syntax.default_sigmeta;
              FStar_Syntax_Syntax.sigattrs = [];
              FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
            }  in
          let env1 = FStar_Syntax_DsEnv.push_sigelt env se  in (env1, [se])
      | FStar_Parser_AST.Fail (expected_errs,lax1,d1) ->
          let env0 =
            let uu____27765 = FStar_Syntax_DsEnv.snapshot env  in
            FStar_All.pipe_right uu____27765 FStar_Pervasives_Native.snd  in
          let uu____27777 =
            FStar_Errors.catch_errors
              (fun uu____27795  ->
                 FStar_Options.with_saved_options
                   (fun uu____27801  -> desugar_decl env d1))
             in
          (match uu____27777 with
           | (errs,r) ->
               (match (errs, r) with
                | ([],FStar_Pervasives_Native.Some (uu____27836,ses)) ->
                    let se =
                      {
                        FStar_Syntax_Syntax.sigel =
                          (FStar_Syntax_Syntax.Sig_fail
                             (expected_errs, lax1, ses));
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
                | (errs1,uu____27858) ->
                    if expected_errs = []
                    then (env0, [])
                    else
                      (let actual_errs =
                         FStar_List.concatMap
                           (fun i  ->
                              FStar_Common.list_of_option
                                i.FStar_Errors.issue_number) errs1
                          in
                       let uu____27894 =
                         FStar_Errors.find_multiset_discrepancy expected_errs
                           actual_errs
                          in
                       match uu____27894 with
                       | FStar_Pervasives_Native.None  -> (env0, [])
                       | FStar_Pervasives_Native.Some (e,n1,n2) ->
                           (FStar_List.iter FStar_Errors.print_issue errs1;
                            (let uu____27939 =
                               let uu____27945 =
                                 let uu____27947 =
                                   FStar_Common.string_of_list
                                     FStar_Util.string_of_int expected_errs
                                    in
                                 let uu____27950 =
                                   FStar_Common.string_of_list
                                     FStar_Util.string_of_int actual_errs
                                    in
                                 let uu____27953 = FStar_Util.string_of_int e
                                    in
                                 let uu____27955 =
                                   FStar_Util.string_of_int n2  in
                                 let uu____27957 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format5
                                   "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                   uu____27947 uu____27950 uu____27953
                                   uu____27955 uu____27957
                                  in
                               (FStar_Errors.Error_DidNotFail, uu____27945)
                                in
                             FStar_Errors.log_issue
                               d1.FStar_Parser_AST.drange uu____27939);
                            (env0, [])))))

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____27982 =
        FStar_List.fold_left
          (fun uu____28002  ->
             fun d  ->
               match uu____28002 with
               | (env1,sigelts) ->
                   let uu____28022 = desugar_decl env1 d  in
                   (match uu____28022 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27982 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28113) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28117;
               FStar_Syntax_Syntax.exports = uu____28118;
               FStar_Syntax_Syntax.is_interface = uu____28119;_},FStar_Parser_AST.Module
             (current_lid,uu____28121)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28130) ->
              let uu____28133 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28133
           in
        let uu____28138 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28180 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28180, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28202 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28202, mname, decls, false)
           in
        match uu____28138 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28244 = desugar_decls env2 decls  in
            (match uu____28244 with
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
          let uu____28312 =
            (FStar_Options.interactive ()) &&
              (let uu____28315 =
                 let uu____28317 =
                   let uu____28319 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28319  in
                 FStar_Util.get_file_extension uu____28317  in
               FStar_List.mem uu____28315 ["fsti"; "fsi"])
             in
          if uu____28312 then as_interface m else m  in
        let uu____28333 = desugar_modul_common curmod env m1  in
        match uu____28333 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28355 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28355, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28377 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28377 with
      | (env1,modul,pop_when_done) ->
          let uu____28394 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28394 with
           | (env2,modul1) ->
               ((let uu____28406 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28406
                 then
                   let uu____28409 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28409
                 else ());
                (let uu____28414 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28414, modul1))))
  
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
        (fun uu____28464  ->
           let uu____28465 = desugar_modul env modul  in
           match uu____28465 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28503  ->
           let uu____28504 = desugar_decls env decls  in
           match uu____28504 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28555  ->
             let uu____28556 = desugar_partial_modul modul env a_modul  in
             match uu____28556 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28651 ->
                  let t =
                    let uu____28661 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28661  in
                  let uu____28674 =
                    let uu____28675 = FStar_Syntax_Subst.compress t  in
                    uu____28675.FStar_Syntax_Syntax.n  in
                  (match uu____28674 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28687,uu____28688)
                       -> bs1
                   | uu____28713 -> failwith "Impossible")
               in
            let uu____28723 =
              let uu____28730 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28730
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28723 with
            | (binders,uu____28732,binders_opening) ->
                let erase_term t =
                  let uu____28740 =
                    let uu____28741 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28741  in
                  FStar_Syntax_Subst.close binders uu____28740  in
                let erase_tscheme uu____28759 =
                  match uu____28759 with
                  | (us,t) ->
                      let t1 =
                        let uu____28779 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28779 t  in
                      let uu____28782 =
                        let uu____28783 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28783  in
                      ([], uu____28782)
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
                    | uu____28806 ->
                        let bs =
                          let uu____28816 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28816  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28856 =
                          let uu____28857 =
                            let uu____28860 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28860  in
                          uu____28857.FStar_Syntax_Syntax.n  in
                        (match uu____28856 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28862,uu____28863) -> bs1
                         | uu____28888 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28896 =
                      let uu____28897 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28897  in
                    FStar_Syntax_Subst.close binders uu____28896  in
                  let uu___3958_28898 = action  in
                  let uu____28899 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28900 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3958_28898.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3958_28898.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28899;
                    FStar_Syntax_Syntax.action_typ = uu____28900
                  }  in
                let uu___3960_28901 = ed  in
                let uu____28902 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28903 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____28904 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____28905 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3960_28901.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3960_28901.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28902;
                  FStar_Syntax_Syntax.signature = uu____28903;
                  FStar_Syntax_Syntax.combinators = uu____28904;
                  FStar_Syntax_Syntax.actions = uu____28905;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3960_28901.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3967_28921 = se  in
                  let uu____28922 =
                    let uu____28923 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28923  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28922;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3967_28921.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3967_28921.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3967_28921.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3967_28921.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3967_28921.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28925 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28926 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28926 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28943 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28943
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28945 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28945)
  