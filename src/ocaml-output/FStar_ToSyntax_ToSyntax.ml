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
  
let (generalize_annotated_univs :
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
    | uu____3504 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3512  ->
    match uu___4_3512 with
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
    | uu____3561 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = Prims.int_zero
      then u
      else
        (let uu____3582 = sum_to_universe u (n1 - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3582)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3608 =
      let uu____3609 = unparen t  in uu____3609.FStar_Parser_AST.tm  in
    match uu____3608 with
    | FStar_Parser_AST.Wild  ->
        let uu____3615 =
          let uu____3616 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3616  in
        FStar_Util.Inr uu____3615
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3629)) ->
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
             let uu____3720 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3720
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3737 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3737
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3753 =
               let uu____3759 =
                 let uu____3761 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3761
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3759)
                in
             FStar_Errors.raise_error uu____3753 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3770 ->
        let rec aux t1 univargs =
          let uu____3807 =
            let uu____3808 = unparen t1  in uu____3808.FStar_Parser_AST.tm
             in
          match uu____3807 with
          | FStar_Parser_AST.App (t2,targ,uu____3816) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3843  ->
                     match uu___5_3843 with
                     | FStar_Util.Inr uu____3850 -> true
                     | uu____3853 -> false) univargs
              then
                let uu____3861 =
                  let uu____3862 =
                    FStar_List.map
                      (fun uu___6_3872  ->
                         match uu___6_3872 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3862  in
                FStar_Util.Inr uu____3861
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
                 FStar_Util.Inl uu____3912)
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
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4210 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4217 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4218 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4220,pats1) ->
            let aux out uu____4261 =
              match uu____4261 with
              | (p1,uu____4274) ->
                  let intersection =
                    let uu____4284 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4284 out  in
                  let uu____4287 = FStar_Util.set_is_empty intersection  in
                  if uu____4287
                  then
                    let uu____4292 = pat_vars p1  in
                    FStar_Util.set_union out uu____4292
                  else
                    (let duplicate_bv =
                       let uu____4298 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4298  in
                     let uu____4301 =
                       let uu____4307 =
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4307)
                        in
                     FStar_Errors.raise_error uu____4301 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4331 = pat_vars p  in
          FStar_All.pipe_right uu____4331 (fun a1  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4359 =
              let uu____4361 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4361  in
            if uu____4359
            then ()
            else
              (let nonlinear_vars =
                 let uu____4370 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4370  in
               let first_nonlinear_var =
                 let uu____4374 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4374  in
               let uu____4377 =
                 let uu____4383 =
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4383)  in
               FStar_Errors.raise_error uu____4377 r)
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
          let uu____4698 =
            FStar_Util.find_opt
              (fun y  ->
                 (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                   x.FStar_Ident.idText) l
             in
          match uu____4698 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4715 ->
              let uu____4718 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4718 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4859 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4881 =
                  let uu____4887 =
                    FStar_Parser_AST.compile_op Prims.int_zero
                      op.FStar_Ident.idText op.FStar_Ident.idRange
                     in
                  (uu____4887, (op.FStar_Ident.idRange))  in
                FStar_Ident.mk_ident uu____4881  in
              let p2 =
                let uu___916_4892 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___916_4892.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4909 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4912 = aux loc env1 p2  in
                match uu____4912 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____4968 =
                      match binder with
                      | LetBinder uu____4989 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5014 = close_fun env1 t  in
                            desugar_term env1 uu____5014  in
                          let x1 =
                            let uu___942_5016 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___942_5016.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___942_5016.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____4968 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5062 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5063 -> ()
                           | uu____5064 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5065 ->
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
              let uu____5083 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5083, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5096 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5096, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5114 = resolvex loc env1 x  in
              (match uu____5114 with
               | (loc1,env2,xbv) ->
                   let uu____5146 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5146, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5164 = resolvex loc env1 x  in
              (match uu____5164 with
               | (loc1,env2,xbv) ->
                   let uu____5196 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5196, []))
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
              let uu____5210 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5210, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5238;_},args)
              ->
              let uu____5244 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5305  ->
                       match uu____5305 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5386 = aux loc1 env2 arg  in
                           (match uu____5386 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5244 with
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
                   let uu____5558 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5558, annots))
          | FStar_Parser_AST.PatApp uu____5574 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5602 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5652  ->
                       match uu____5652 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5713 = aux loc1 env2 pat  in
                           (match uu____5713 with
                            | (loc2,env3,uu____5752,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5602 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5846 =
                       let uu____5849 =
                         let uu____5856 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5856  in
                       let uu____5857 =
                         let uu____5858 =
                           let uu____5872 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5872, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5858  in
                       FStar_All.pipe_left uu____5849 uu____5857  in
                     FStar_List.fold_right
                       (fun hd1  ->
                          fun tl1  ->
                            let r =
                              FStar_Range.union_ranges
                                hd1.FStar_Syntax_Syntax.p
                                tl1.FStar_Syntax_Syntax.p
                               in
                            let uu____5906 =
                              let uu____5907 =
                                let uu____5921 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5921, [(hd1, false); (tl1, false)])
                                 in
                              FStar_Syntax_Syntax.Pat_cons uu____5907  in
                            FStar_All.pipe_left (pos_r r) uu____5906) pats1
                       uu____5846
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
              let uu____5977 =
                FStar_List.fold_left
                  (fun uu____6036  ->
                     fun p2  ->
                       match uu____6036 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6118 = aux loc1 env2 p2  in
                           (match uu____6118 with
                            | (loc2,env3,uu____6162,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____5977 with
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
                     | uu____6325 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6328 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6328, annots))
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
                     (fun uu____6404  ->
                        match uu____6404 with
                        | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6434  ->
                        match uu____6434 with
                        | (f,uu____6440) ->
                            let uu____6441 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6467  ->
                                      match uu____6467 with
                                      | (g,uu____6474) ->
                                          f.FStar_Ident.idText =
                                            g.FStar_Ident.idText))
                               in
                            (match uu____6441 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6480,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6487 =
                  let uu____6488 =
                    let uu____6495 =
                      let uu____6496 =
                        let uu____6497 =
                          FStar_Ident.lid_of_ids
                            (FStar_List.append
                               (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                               [record.FStar_Syntax_DsEnv.constrname])
                           in
                        FStar_Parser_AST.PatName uu____6497  in
                      FStar_Parser_AST.mk_pattern uu____6496
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6495, args)  in
                  FStar_Parser_AST.PatApp uu____6488  in
                FStar_Parser_AST.mk_pattern uu____6487
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6500 = aux loc env1 app  in
              (match uu____6500 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6577 =
                           let uu____6578 =
                             let uu____6592 =
                               let uu___1092_6593 = fv  in
                               let uu____6594 =
                                 let uu____6597 =
                                   let uu____6598 =
                                     let uu____6605 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6605)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6598
                                    in
                                 FStar_Pervasives_Native.Some uu____6597  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1092_6593.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1092_6593.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6594
                               }  in
                             (uu____6592, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6578  in
                         FStar_All.pipe_left pos uu____6577
                     | uu____6631 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6715 = aux' true loc env1 p2  in
              (match uu____6715 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6768 =
                     FStar_List.fold_left
                       (fun uu____6816  ->
                          fun p4  ->
                            match uu____6816 with
                            | (loc2,env3,ps1) ->
                                let uu____6881 = aux' true loc2 env3 p4  in
                                (match uu____6881 with
                                 | (loc3,env4,uu____6919,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6768 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7080 ->
              let uu____7081 = aux' true loc env1 p1  in
              (match uu____7081 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7172 = aux_maybe_or env p  in
        match uu____7172 with
        | (env1,b,pats) ->
            ((let uu____7227 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7227
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
            let uu____7301 =
              let uu____7302 =
                let uu____7313 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7313, (ty, tacopt))  in
              LetBinder uu____7302  in
            (env, uu____7301, [])  in
          let op_to_ident x =
            let uu____7330 =
              let uu____7336 =
                FStar_Parser_AST.compile_op Prims.int_zero
                  x.FStar_Ident.idText x.FStar_Ident.idRange
                 in
              (uu____7336, (x.FStar_Ident.idRange))  in
            FStar_Ident.mk_ident uu____7330  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7349 = op_to_ident x  in
              mklet uu____7349 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7351) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7357;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7373 = op_to_ident x  in
              let uu____7374 = desugar_term env t  in
              mklet uu____7373 uu____7374 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7376);
                 FStar_Parser_AST.prange = uu____7377;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7397 = desugar_term env t  in
              mklet x uu____7397 tacopt1
          | uu____7398 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7411 = desugar_data_pat true env p  in
           match uu____7411 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7441;
                      FStar_Syntax_Syntax.p = uu____7442;_},uu____7443)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7456;
                      FStar_Syntax_Syntax.p = uu____7457;_},uu____7458)::[]
                     -> []
                 | uu____7471 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7479  ->
    fun env  ->
      fun pat  ->
        let uu____7483 = desugar_data_pat false env pat  in
        match uu____7483 with | (env1,uu____7500,pat1) -> (env1, pat1)

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
      let uu____7522 = desugar_term_aq env e  in
      match uu____7522 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7541 = desugar_typ_aq env e  in
      match uu____7541 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7551  ->
        fun range  ->
          match uu____7551 with
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
              ((let uu____7573 =
                  let uu____7575 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7575  in
                if uu____7573
                then
                  let uu____7578 =
                    let uu____7584 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7584)  in
                  FStar_Errors.log_issue range uu____7578
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
                  let uu____7605 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7605 range  in
                let lid1 =
                  let uu____7609 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7609 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7619 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7619 range  in
                           let private_fv =
                             let uu____7621 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7621 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1259_7622 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1259_7622.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1259_7622.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7623 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7627 =
                        let uu____7633 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7633)
                         in
                      FStar_Errors.raise_error uu____7627 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7653 =
                  let uu____7660 =
                    let uu____7661 =
                      let uu____7678 =
                        let uu____7689 =
                          let uu____7698 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7698)  in
                        [uu____7689]  in
                      (lid1, uu____7678)  in
                    FStar_Syntax_Syntax.Tm_app uu____7661  in
                  FStar_Syntax_Syntax.mk uu____7660  in
                uu____7653 FStar_Pervasives_Native.None range))

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
          let uu___1275_7817 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1275_7817.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1275_7817.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7820 =
          let uu____7821 = unparen top  in uu____7821.FStar_Parser_AST.tm  in
        match uu____7820 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7826 ->
            let uu____7835 = desugar_formula env top  in (uu____7835, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7844 = desugar_formula env t  in (uu____7844, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7853 = desugar_formula env t  in (uu____7853, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7880 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7880, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7882 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7882, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7891 =
                let uu____7892 =
                  let uu____7899 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7899, args)  in
                FStar_Parser_AST.Op uu____7892  in
              FStar_Parser_AST.mk_term uu____7891 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7904 =
              let uu____7905 =
                let uu____7906 =
                  let uu____7913 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7913, [e])  in
                FStar_Parser_AST.Op uu____7906  in
              FStar_Parser_AST.mk_term uu____7905 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7904
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7925 = FStar_Ident.text_of_id op_star  in
             uu____7925 = "*") &&
              (let uu____7930 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____7930 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7947;_},t1::t2::[])
                  when
                  let uu____7953 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____7953 FStar_Option.isNone ->
                  let uu____7960 = flatten1 t1  in
                  FStar_List.append uu____7960 [t2]
              | uu____7963 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1323_7968 = top  in
              let uu____7969 =
                let uu____7970 =
                  let uu____7981 =
                    FStar_List.map (fun _7992  -> FStar_Util.Inr _7992) terms
                     in
                  (uu____7981, rhs)  in
                FStar_Parser_AST.Sum uu____7970  in
              {
                FStar_Parser_AST.tm = uu____7969;
                FStar_Parser_AST.range =
                  (uu___1323_7968.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1323_7968.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8000 =
              let uu____8001 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8001  in
            (uu____8000, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8007 =
              let uu____8013 =
                let uu____8015 =
                  let uu____8017 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8017 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8015  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8013)  in
            FStar_Errors.raise_error uu____8007 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8032 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8032 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8039 =
                   let uu____8045 =
                     let uu____8047 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8047
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8045)
                    in
                 FStar_Errors.raise_error uu____8039
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8062 =
                     let uu____8087 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8149 = desugar_term_aq env t  in
                               match uu____8149 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8087 FStar_List.unzip  in
                   (match uu____8062 with
                    | (args1,aqs) ->
                        let uu____8282 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8282, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8299)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8316 =
              let uu___1352_8317 = top  in
              let uu____8318 =
                let uu____8319 =
                  let uu____8326 =
                    let uu___1354_8327 = top  in
                    let uu____8328 =
                      let uu____8329 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8329  in
                    {
                      FStar_Parser_AST.tm = uu____8328;
                      FStar_Parser_AST.range =
                        (uu___1354_8327.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1354_8327.FStar_Parser_AST.level)
                    }  in
                  (uu____8326, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8319  in
              {
                FStar_Parser_AST.tm = uu____8318;
                FStar_Parser_AST.range =
                  (uu___1352_8317.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1352_8317.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8316
        | FStar_Parser_AST.Construct (n1,(a,uu____8337)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8357 =
                let uu___1364_8358 = top  in
                let uu____8359 =
                  let uu____8360 =
                    let uu____8367 =
                      let uu___1366_8368 = top  in
                      let uu____8369 =
                        let uu____8370 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8370  in
                      {
                        FStar_Parser_AST.tm = uu____8369;
                        FStar_Parser_AST.range =
                          (uu___1366_8368.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1366_8368.FStar_Parser_AST.level)
                      }  in
                    (uu____8367, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8360  in
                {
                  FStar_Parser_AST.tm = uu____8359;
                  FStar_Parser_AST.range =
                    (uu___1364_8358.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1364_8358.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8357))
        | FStar_Parser_AST.Construct (n1,(a,uu____8378)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8395 =
              let uu___1375_8396 = top  in
              let uu____8397 =
                let uu____8398 =
                  let uu____8405 =
                    let uu___1377_8406 = top  in
                    let uu____8407 =
                      let uu____8408 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8408  in
                    {
                      FStar_Parser_AST.tm = uu____8407;
                      FStar_Parser_AST.range =
                        (uu___1377_8406.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1377_8406.FStar_Parser_AST.level)
                    }  in
                  (uu____8405, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8398  in
              {
                FStar_Parser_AST.tm = uu____8397;
                FStar_Parser_AST.range =
                  (uu___1375_8396.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1375_8396.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8395
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8414; FStar_Ident.ident = uu____8415;
              FStar_Ident.nsstr = uu____8416; FStar_Ident.str = "Type0";_}
            ->
            let uu____8421 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8421, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8422; FStar_Ident.ident = uu____8423;
              FStar_Ident.nsstr = uu____8424; FStar_Ident.str = "Type";_}
            ->
            let uu____8429 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8429, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8430; FStar_Ident.ident = uu____8431;
               FStar_Ident.nsstr = uu____8432; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8452 =
              let uu____8453 =
                let uu____8454 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8454  in
              mk1 uu____8453  in
            (uu____8452, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8455; FStar_Ident.ident = uu____8456;
              FStar_Ident.nsstr = uu____8457; FStar_Ident.str = "Effect";_}
            ->
            let uu____8462 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8462, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8463; FStar_Ident.ident = uu____8464;
              FStar_Ident.nsstr = uu____8465; FStar_Ident.str = "True";_}
            ->
            let uu____8470 =
              let uu____8471 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8471
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8470, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8472; FStar_Ident.ident = uu____8473;
              FStar_Ident.nsstr = uu____8474; FStar_Ident.str = "False";_}
            ->
            let uu____8479 =
              let uu____8480 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8480
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8479, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8483;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8486 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8486 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8495 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         Prims.int_one) FStar_Pervasives_Native.None
                     in
                  (uu____8495, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8497 =
                    let uu____8499 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8499 txt
                     in
                  failwith uu____8497))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8508 = desugar_name mk1 setpos env true l  in
              (uu____8508, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8517 = desugar_name mk1 setpos env true l  in
              (uu____8517, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8535 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8535 with
                | FStar_Pervasives_Native.Some uu____8545 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8553 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8553 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8571 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8592 =
                    let uu____8593 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8593  in
                  (uu____8592, noaqs)
              | uu____8599 ->
                  let uu____8607 =
                    let uu____8613 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8613)  in
                  FStar_Errors.raise_error uu____8607
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8623 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8623 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8630 =
                    let uu____8636 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8636)
                     in
                  FStar_Errors.raise_error uu____8630
                    top.FStar_Parser_AST.range
              | uu____8644 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8648 = desugar_name mk1 setpos env true lid'  in
                  (uu____8648, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8670 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8670 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8689 ->
                       let uu____8696 =
                         FStar_Util.take
                           (fun uu____8720  ->
                              match uu____8720 with
                              | (uu____8726,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8696 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8771 =
                              let uu____8796 =
                                FStar_List.map
                                  (fun uu____8839  ->
                                     match uu____8839 with
                                     | (t,imp) ->
                                         let uu____8856 =
                                           desugar_term_aq env t  in
                                         (match uu____8856 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8796
                                FStar_List.unzip
                               in
                            (match uu____8771 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____8999 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____8999, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9018 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9018 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9029 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
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
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9311, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9338 =
              let uu____9355 =
                let uu____9362 =
                  let uu____9369 =
                    FStar_All.pipe_left (fun _9378  -> FStar_Util.Inl _9378)
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
                                        [(((let uu___1536_9586 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1536_9586.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1536_9586.FStar_Syntax_Syntax.index);
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
                   FStar_All.pipe_left mk1
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
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9742 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9742 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
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
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9918 = FStar_Util.set_is_empty i  in
                    if uu____9918
                    then
                      let uu____9923 = FStar_Util.set_union acc set1  in
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
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9940 =
                    let uu____9946 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9946)
                     in
                  let uu____9950 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9940 uu____9950);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9958 =
                FStar_List.fold_left
                  (fun uu____9978  ->
                     fun pat  ->
                       match uu____9978 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10004,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10014 =
                                  let uu____10017 = free_type_vars env1 t  in
                                  FStar_List.append uu____10017 ftvs  in
                                (env1, uu____10014)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10022,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10033 =
                                  let uu____10036 = free_type_vars env1 t  in
                                  let uu____10039 =
                                    let uu____10042 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10042 ftvs  in
                                  FStar_List.append uu____10036 uu____10039
                                   in
                                (env1, uu____10033)
                            | uu____10047 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____9958 with
              | (uu____10056,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10068 =
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
                    FStar_List.append uu____10068 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10148 = desugar_term_aq env1 body  in
                        (match uu____10148 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10183 =
                                       let uu____10184 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10184
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10183
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
                             let uu____10253 =
                               let uu____10254 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10254  in
                             (uu____10253, aq))
                    | p::rest ->
                        let uu____10267 = desugar_binding_pat env1 p  in
                        (match uu____10267 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10299)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10314 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10323 =
                               match b with
                               | LetBinder uu____10364 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10433) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10487 =
                                           let uu____10496 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10496, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10487
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10558,uu____10559) ->
                                              let tup2 =
                                                let uu____10561 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10561
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10566 =
                                                  let uu____10573 =
                                                    let uu____10574 =
                                                      let uu____10591 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10594 =
                                                        let uu____10605 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10614 =
                                                          let uu____10625 =
                                                            let uu____10634 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10634
                                                             in
                                                          [uu____10625]  in
                                                        uu____10605 ::
                                                          uu____10614
                                                         in
                                                      (uu____10591,
                                                        uu____10594)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10574
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10573
                                                   in
                                                uu____10566
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10682 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10682
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10733,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10735,pats1)) ->
                                              let tupn =
                                                let uu____10780 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10780
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10793 =
                                                  let uu____10794 =
                                                    let uu____10811 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10814 =
                                                      let uu____10825 =
                                                        let uu____10836 =
                                                          let uu____10845 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10845
                                                           in
                                                        [uu____10836]  in
                                                      FStar_List.append args
                                                        uu____10825
                                                       in
                                                    (uu____10811,
                                                      uu____10814)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10794
                                                   in
                                                mk1 uu____10793  in
                                              let p2 =
                                                let uu____10893 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10893
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10940 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10323 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11032,uu____11033,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11055 =
                let uu____11056 = unparen e  in
                uu____11056.FStar_Parser_AST.tm  in
              match uu____11055 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11066 ->
                  let uu____11067 = desugar_term_aq env e  in
                  (match uu____11067 with
                   | (head1,aq) ->
                       let uu____11080 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11080, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11087 ->
            let rec aux args aqs e =
              let uu____11164 =
                let uu____11165 = unparen e  in
                uu____11165.FStar_Parser_AST.tm  in
              match uu____11164 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11183 = desugar_term_aq env t  in
                  (match uu____11183 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11231 ->
                  let uu____11232 = desugar_term_aq env e  in
                  (match uu____11232 with
                   | (head1,aq) ->
                       let uu____11253 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11253, (join_aqs (aq :: aqs))))
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
            let uu____11316 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11316
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
            let uu____11368 = desugar_term_aq env t  in
            (match uu____11368 with
             | (tm,s) ->
                 let uu____11379 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11379, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11385 =
              let uu____11398 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11398 then desugar_typ_aq else desugar_term_aq  in
            uu____11385 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11465 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11608  ->
                        match uu____11608 with
                        | (attr_opt,(p,def)) ->
                            let uu____11666 = is_app_pattern p  in
                            if uu____11666
                            then
                              let uu____11699 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11699, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11782 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11782, def1)
                               | uu____11827 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11865);
                                           FStar_Parser_AST.prange =
                                             uu____11866;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11915 =
                                            let uu____11936 =
                                              let uu____11941 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11941  in
                                            (uu____11936, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11915, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12033) ->
                                        if top_level
                                        then
                                          let uu____12069 =
                                            let uu____12090 =
                                              let uu____12095 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12095  in
                                            (uu____12090, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12069, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12186 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12219 =
                FStar_List.fold_left
                  (fun uu____12308  ->
                     fun uu____12309  ->
                       match (uu____12308, uu____12309) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12439,uu____12440),uu____12441))
                           ->
                           let uu____12575 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12615 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12615 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12650 =
                                        let uu____12653 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12653 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12650, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12669 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12669 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12575 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12219 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12922 =
                    match uu____12922 with
                    | (attrs_opt,(uu____12962,args,result_t),def) ->
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
                                let uu____13054 = is_comp_type env1 t  in
                                if uu____13054
                                then
                                  ((let uu____13058 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13068 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13068))
                                       in
                                    match uu____13058 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13075 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13078 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13078))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13075
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
                          | uu____13089 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13092 = desugar_term_aq env1 def2  in
                        (match uu____13092 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13114 =
                                     let uu____13115 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13115
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13114
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
                  let uu____13156 =
                    let uu____13173 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13173 FStar_List.unzip  in
                  (match uu____13156 with
                   | (lbs1,aqss) ->
                       let uu____13315 = desugar_term_aq env' body  in
                       (match uu____13315 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13421  ->
                                    fun used_marker  ->
                                      match uu____13421 with
                                      | (_attr_opt,(f,uu____13495,uu____13496),uu____13497)
                                          ->
                                          let uu____13554 =
                                            let uu____13556 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13556  in
                                          if uu____13554
                                          then
                                            let uu____13580 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13598 =
                                                    FStar_Ident.string_of_ident
                                                      x
                                                     in
                                                  let uu____13600 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13598, "Local",
                                                    uu____13600)
                                              | FStar_Util.Inr l ->
                                                  let uu____13605 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13607 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13605, "Global",
                                                    uu____13607)
                                               in
                                            (match uu____13580 with
                                             | (nm,gl,rng) ->
                                                 let uu____13618 =
                                                   let uu____13624 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13624)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13618)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13632 =
                                let uu____13635 =
                                  let uu____13636 =
                                    let uu____13650 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13650)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13636  in
                                FStar_All.pipe_left mk1 uu____13635  in
                              (uu____13632,
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
              let uu____13752 = desugar_term_aq env t1  in
              match uu____13752 with
              | (t11,aq0) ->
                  let uu____13773 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13773 with
                   | (env1,binder,pat1) ->
                       let uu____13803 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13845 = desugar_term_aq env1 t2  in
                             (match uu____13845 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13867 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13867
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13868 =
                                    FStar_All.pipe_left mk1
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13868, aq))
                         | LocalBinder (x,uu____13909) ->
                             let uu____13910 = desugar_term_aq env1 t2  in
                             (match uu____13910 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13932;
                                         FStar_Syntax_Syntax.p = uu____13933;_},uu____13934)::[]
                                        -> body1
                                    | uu____13947 ->
                                        let uu____13950 =
                                          let uu____13957 =
                                            let uu____13958 =
                                              let uu____13981 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____13984 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____13981, uu____13984)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____13958
                                             in
                                          FStar_Syntax_Syntax.mk uu____13957
                                           in
                                        uu____13950
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14021 =
                                    let uu____14024 =
                                      let uu____14025 =
                                        let uu____14039 =
                                          let uu____14042 =
                                            let uu____14043 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14043]  in
                                          FStar_Syntax_Subst.close
                                            uu____14042 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14039)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14025
                                       in
                                    FStar_All.pipe_left mk1 uu____14024  in
                                  (uu____14021, aq))
                          in
                       (match uu____13803 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14151 = FStar_List.hd lbs  in
            (match uu____14151 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14195 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14195
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____14211 =
                let uu____14212 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14212  in
              mk1 uu____14211  in
            let uu____14213 = desugar_term_aq env t1  in
            (match uu____14213 with
             | (t1',aq1) ->
                 let uu____14224 = desugar_term_aq env t2  in
                 (match uu____14224 with
                  | (t2',aq2) ->
                      let uu____14235 = desugar_term_aq env t3  in
                      (match uu____14235 with
                       | (t3',aq3) ->
                           let uu____14246 =
                             let uu____14247 =
                               let uu____14248 =
                                 let uu____14271 =
                                   let uu____14288 =
                                     let uu____14303 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14303,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14317 =
                                     let uu____14334 =
                                       let uu____14349 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14349,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14334]  in
                                   uu____14288 :: uu____14317  in
                                 (t1', uu____14271)  in
                               FStar_Syntax_Syntax.Tm_match uu____14248  in
                             mk1 uu____14247  in
                           (uu____14246, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14545 =
              match uu____14545 with
              | (pat,wopt,b) ->
                  let uu____14567 = desugar_match_pat env pat  in
                  (match uu____14567 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14598 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14598
                          in
                       let uu____14603 = desugar_term_aq env1 b  in
                       (match uu____14603 with
                        | (b1,aq) ->
                            let uu____14616 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14616, aq)))
               in
            let uu____14621 = desugar_term_aq env e  in
            (match uu____14621 with
             | (e1,aq) ->
                 let uu____14632 =
                   let uu____14663 =
                     let uu____14696 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14696 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14663
                     (fun uu____14914  ->
                        match uu____14914 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14632 with
                  | (brs,aqs) ->
                      let uu____15133 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15133, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15167 =
              let uu____15188 = is_comp_type env t  in
              if uu____15188
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15243 = desugar_term_aq env t  in
                 match uu____15243 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15167 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15335 = desugar_term_aq env e  in
                 (match uu____15335 with
                  | (e1,aq) ->
                      let uu____15346 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15346, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15385,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15428 = FStar_List.hd fields  in
              match uu____15428 with | (f,uu____15440) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15486  ->
                        match uu____15486 with
                        | (g,uu____15493) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15500,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15514 =
                         let uu____15520 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15520)
                          in
                       FStar_Errors.raise_error uu____15514
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
                  let uu____15531 =
                    let uu____15542 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15573  ->
                              match uu____15573 with
                              | (f,uu____15583) ->
                                  let uu____15584 =
                                    let uu____15585 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15585
                                     in
                                  (uu____15584, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15542)  in
                  FStar_Parser_AST.Construct uu____15531
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15603 =
                      let uu____15604 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15604  in
                    FStar_Parser_AST.mk_term uu____15603
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15606 =
                      let uu____15619 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15649  ->
                                match uu____15649 with
                                | (f,uu____15659) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15619)  in
                    FStar_Parser_AST.Record uu____15606  in
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
            let uu____15719 = desugar_term_aq env recterm1  in
            (match uu____15719 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15735;
                         FStar_Syntax_Syntax.vars = uu____15736;_},args)
                      ->
                      let uu____15762 =
                        let uu____15763 =
                          let uu____15764 =
                            let uu____15781 =
                              let uu____15784 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15785 =
                                let uu____15788 =
                                  let uu____15789 =
                                    let uu____15796 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15796)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15789
                                   in
                                FStar_Pervasives_Native.Some uu____15788  in
                              FStar_Syntax_Syntax.fvar uu____15784
                                FStar_Syntax_Syntax.delta_constant
                                uu____15785
                               in
                            (uu____15781, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15764  in
                        FStar_All.pipe_left mk1 uu____15763  in
                      (uu____15762, s)
                  | uu____15825 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15829 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15829 with
              | (constrname,is_rec) ->
                  let uu____15848 = desugar_term_aq env e  in
                  (match uu____15848 with
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
                       let uu____15868 =
                         let uu____15869 =
                           let uu____15870 =
                             let uu____15887 =
                               let uu____15890 =
                                 let uu____15891 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15891
                                  in
                               FStar_Syntax_Syntax.fvar uu____15890
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    Prims.int_one) qual
                                in
                             let uu____15893 =
                               let uu____15904 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15904]  in
                             (uu____15887, uu____15893)  in
                           FStar_Syntax_Syntax.Tm_app uu____15870  in
                         FStar_All.pipe_left mk1 uu____15869  in
                       (uu____15868, s))))
        | FStar_Parser_AST.NamedTyp (uu____15941,e) -> desugar_term_aq env e
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15951 =
              let uu____15952 = FStar_Syntax_Subst.compress tm  in
              uu____15952.FStar_Syntax_Syntax.n  in
            (match uu____15951 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15960 =
                   let uu___2104_15961 =
                     let uu____15962 =
                       let uu____15964 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____15964  in
                     FStar_Syntax_Util.exp_string uu____15962  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2104_15961.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2104_15961.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15960, noaqs)
             | uu____15965 ->
                 let uu____15966 =
                   let uu____15972 =
                     let uu____15974 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____15974
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____15972)  in
                 FStar_Errors.raise_error uu____15966
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____15983 = desugar_term_aq env e  in
            (match uu____15983 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____15995 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____15995, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16000 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16001 =
              let uu____16002 =
                let uu____16009 = desugar_term env e  in (bv, uu____16009)
                 in
              [uu____16002]  in
            (uu____16000, uu____16001)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16034 =
              let uu____16035 =
                let uu____16036 =
                  let uu____16043 = desugar_term env e  in (uu____16043, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16036  in
              FStar_All.pipe_left mk1 uu____16035  in
            (uu____16034, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16072 -> false  in
              let uu____16074 =
                let uu____16075 = unparen rel1  in
                uu____16075.FStar_Parser_AST.tm  in
              match uu____16074 with
              | FStar_Parser_AST.Op (id1,uu____16078) ->
                  let uu____16083 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id1
                     in
                  (match uu____16083 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16091 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16091 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id1 ->
                  let uu____16102 = FStar_Syntax_DsEnv.try_lookup_id env id1
                     in
                  (match uu____16102 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16108 -> false  in
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
              let uu____16129 =
                let uu____16130 =
                  let uu____16137 =
                    let uu____16138 =
                      let uu____16139 =
                        let uu____16148 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16161 =
                          let uu____16162 =
                            let uu____16163 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16163  in
                          FStar_Parser_AST.mk_term uu____16162
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16148, uu____16161,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16139  in
                    FStar_Parser_AST.mk_term uu____16138
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16137)  in
                FStar_Parser_AST.Abs uu____16130  in
              FStar_Parser_AST.mk_term uu____16129
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
              let uu____16184 = FStar_List.last steps  in
              match uu____16184 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16187,uu____16188,last_expr)) -> last_expr
              | uu____16190 -> failwith "impossible: no last_expr on calc"
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
            let uu____16218 =
              FStar_List.fold_left
                (fun uu____16236  ->
                   fun uu____16237  ->
                     match (uu____16236, uu____16237) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16260 = is_impl rel2  in
                           if uu____16260
                           then
                             let uu____16263 =
                               let uu____16270 =
                                 let uu____16275 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16275, FStar_Parser_AST.Nothing)  in
                               [uu____16270]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16263 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16287 =
                             let uu____16294 =
                               let uu____16301 =
                                 let uu____16308 =
                                   let uu____16315 =
                                     let uu____16320 = eta_and_annot rel2  in
                                     (uu____16320, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16321 =
                                     let uu____16328 =
                                       let uu____16335 =
                                         let uu____16340 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16340,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16341 =
                                         let uu____16348 =
                                           let uu____16353 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16353,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16348]  in
                                       uu____16335 :: uu____16341  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16328
                                      in
                                   uu____16315 :: uu____16321  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16308
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16301
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16294
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16287
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16218 with
             | (e1,uu____16391) ->
                 let e2 =
                   let uu____16393 =
                     let uu____16400 =
                       let uu____16407 =
                         let uu____16414 =
                           let uu____16419 = FStar_Parser_AST.thunk e1  in
                           (uu____16419, FStar_Parser_AST.Nothing)  in
                         [uu____16414]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16407  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16400  in
                   FStar_Parser_AST.mkApp finish1 uu____16393
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16436 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16437 = desugar_formula env top  in
            (uu____16437, noaqs)
        | uu____16438 ->
            let uu____16439 =
              let uu____16445 =
                let uu____16447 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16447  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16445)  in
            FStar_Errors.raise_error uu____16439 top.FStar_Parser_AST.range

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
           (fun uu____16491  ->
              match uu____16491 with
              | (a,imp) ->
                  let uu____16504 = desugar_term env a  in
                  arg_withimp_e imp uu____16504))

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
          let is_requires uu____16541 =
            match uu____16541 with
            | (t1,uu____16548) ->
                let uu____16549 =
                  let uu____16550 = unparen t1  in
                  uu____16550.FStar_Parser_AST.tm  in
                (match uu____16549 with
                 | FStar_Parser_AST.Requires uu____16552 -> true
                 | uu____16561 -> false)
             in
          let is_ensures uu____16573 =
            match uu____16573 with
            | (t1,uu____16580) ->
                let uu____16581 =
                  let uu____16582 = unparen t1  in
                  uu____16582.FStar_Parser_AST.tm  in
                (match uu____16581 with
                 | FStar_Parser_AST.Ensures uu____16584 -> true
                 | uu____16593 -> false)
             in
          let is_app head1 uu____16611 =
            match uu____16611 with
            | (t1,uu____16619) ->
                let uu____16620 =
                  let uu____16621 = unparen t1  in
                  uu____16621.FStar_Parser_AST.tm  in
                (match uu____16620 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16624;
                        FStar_Parser_AST.level = uu____16625;_},uu____16626,uu____16627)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____16629 -> false)
             in
          let is_smt_pat uu____16641 =
            match uu____16641 with
            | (t1,uu____16648) ->
                let uu____16649 =
                  let uu____16650 = unparen t1  in
                  uu____16650.FStar_Parser_AST.tm  in
                (match uu____16649 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16654);
                               FStar_Parser_AST.range = uu____16655;
                               FStar_Parser_AST.level = uu____16656;_},uu____16657)::uu____16658::[])
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
                               FStar_Parser_AST.range = uu____16707;
                               FStar_Parser_AST.level = uu____16708;_},uu____16709)::uu____16710::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16743 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16778 = head_and_args t1  in
            match uu____16778 with
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
                     let thunk_ens uu____16871 =
                       match uu____16871 with
                       | (e,i) ->
                           let uu____16882 = FStar_Parser_AST.thunk e  in
                           (uu____16882, i)
                        in
                     let fail_lemma uu____16894 =
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
                           let uu____17000 =
                             let uu____17007 =
                               let uu____17014 = thunk_ens ens  in
                               [uu____17014; nil_pat]  in
                             req_true :: uu____17007  in
                           unit_tm :: uu____17000
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17061 =
                             let uu____17068 =
                               let uu____17075 = thunk_ens ens  in
                               [uu____17075; nil_pat]  in
                             req :: uu____17068  in
                           unit_tm :: uu____17061
                       | ens::smtpat::[] when
                           (((let uu____17124 = is_requires ens  in
                              Prims.op_Negation uu____17124) &&
                               (let uu____17127 = is_smt_pat ens  in
                                Prims.op_Negation uu____17127))
                              &&
                              (let uu____17130 = is_decreases ens  in
                               Prims.op_Negation uu____17130))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17132 =
                             let uu____17139 =
                               let uu____17146 = thunk_ens ens  in
                               [uu____17146; smtpat]  in
                             req_true :: uu____17139  in
                           unit_tm :: uu____17132
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17193 =
                             let uu____17200 =
                               let uu____17207 = thunk_ens ens  in
                               [uu____17207; nil_pat; dec]  in
                             req_true :: uu____17200  in
                           unit_tm :: uu____17193
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17267 =
                             let uu____17274 =
                               let uu____17281 = thunk_ens ens  in
                               [uu____17281; smtpat; dec]  in
                             req_true :: uu____17274  in
                           unit_tm :: uu____17267
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17341 =
                             let uu____17348 =
                               let uu____17355 = thunk_ens ens  in
                               [uu____17355; nil_pat; dec]  in
                             req :: uu____17348  in
                           unit_tm :: uu____17341
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17415 =
                             let uu____17422 =
                               let uu____17429 = thunk_ens ens  in
                               [uu____17429; smtpat]  in
                             req :: uu____17422  in
                           unit_tm :: uu____17415
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17494 =
                             let uu____17501 =
                               let uu____17508 = thunk_ens ens  in
                               [uu____17508; dec; smtpat]  in
                             req :: uu____17501  in
                           unit_tm :: uu____17494
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17570 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17570, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17598 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17598
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____17601 =
                       let uu____17608 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17608, [])  in
                     (uu____17601, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17626 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17626
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____17629 =
                       let uu____17636 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17636, [])  in
                     (uu____17629, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17658 =
                       let uu____17665 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17665, [])  in
                     (uu____17658, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17688 when allow_type_promotion ->
                     let default_effect =
                       let uu____17690 = FStar_Options.ml_ish ()  in
                       if uu____17690
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17696 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17696
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17703 =
                       let uu____17710 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17710, [])  in
                     (uu____17703, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17733 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17752 = pre_process_comp_typ t  in
          match uu____17752 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17804 =
                    let uu____17810 =
                      let uu____17812 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17812
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17810)
                     in
                  fail1 uu____17804)
               else ();
               (let is_universe uu____17828 =
                  match uu____17828 with
                  | (uu____17834,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17836 = FStar_Util.take is_universe args  in
                match uu____17836 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17895  ->
                           match uu____17895 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17902 =
                      let uu____17917 = FStar_List.hd args1  in
                      let uu____17926 = FStar_List.tl args1  in
                      (uu____17917, uu____17926)  in
                    (match uu____17902 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____17981 =
                           let is_decrease uu____18020 =
                             match uu____18020 with
                             | (t1,uu____18031) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18042;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18043;_},uu____18044::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18083 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____17981 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18200  ->
                                        match uu____18200 with
                                        | (t1,uu____18210) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18219,(arg,uu____18221)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18260 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18281 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18293 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18293
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18300 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18300
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18310 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18310
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18317 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18317
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18324 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18324
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18331 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18331
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18352 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18352
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
                                                    let uu____18443 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18443
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
                                              | uu____18464 -> pat  in
                                            let uu____18465 =
                                              let uu____18476 =
                                                let uu____18487 =
                                                  let uu____18496 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18496, aq)  in
                                                [uu____18487]  in
                                              ens :: uu____18476  in
                                            req :: uu____18465
                                        | uu____18537 -> rest2
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
        let uu___2429_18572 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2429_18572.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2429_18572.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2436_18626 = b  in
             {
               FStar_Parser_AST.b = (uu___2436_18626.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2436_18626.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2436_18626.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18655 body1 =
          match uu____18655 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18701::uu____18702) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18720 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2455_18747 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2455_18747.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2455_18747.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18810 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18810))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18841 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18841 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2468_18851 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2468_18851.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2468_18851.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18857 =
                     let uu____18860 =
                       let uu____18861 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18861]  in
                     no_annot_abs uu____18860 body2  in
                   FStar_All.pipe_left setpos uu____18857  in
                 let uu____18882 =
                   let uu____18883 =
                     let uu____18900 =
                       let uu____18903 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18903
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____18905 =
                       let uu____18916 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18916]  in
                     (uu____18900, uu____18905)  in
                   FStar_Syntax_Syntax.Tm_app uu____18883  in
                 FStar_All.pipe_left mk1 uu____18882)
        | uu____18955 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19020 = q (rest, pats, body)  in
              let uu____19023 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19020 uu____19023
                FStar_Parser_AST.Formula
               in
            let uu____19024 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19024 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19035 -> failwith "impossible"  in
      let uu____19039 =
        let uu____19040 = unparen f  in uu____19040.FStar_Parser_AST.tm  in
      match uu____19039 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19053,uu____19054) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19078,uu____19079) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19135 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19135
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19179 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19179
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19243 -> desugar_term env f

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
          let uu____19254 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19254)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19259 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19259)
      | FStar_Parser_AST.TVariable x ->
          let uu____19263 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____19263)
      | FStar_Parser_AST.NoName t ->
          let uu____19267 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19267)
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
      fun uu___11_19275  ->
        match uu___11_19275 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19297 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19297, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19314 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19314 with
             | (env1,a1) ->
                 let uu____19331 =
                   let uu____19338 = trans_aqual env1 imp  in
                   ((let uu___2568_19344 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2568_19344.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2568_19344.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19338)
                    in
                 (uu____19331, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19352  ->
      match uu___12_19352 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19356 =
            let uu____19357 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19357  in
          FStar_Pervasives_Native.Some uu____19356
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19385 =
        FStar_List.fold_left
          (fun uu____19418  ->
             fun b  ->
               match uu____19418 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2586_19462 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2586_19462.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2586_19462.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2586_19462.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19477 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19477 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2596_19495 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2596_19495.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2596_19495.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19496 =
                               let uu____19503 =
                                 let uu____19508 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19508)  in
                               uu____19503 :: out  in
                             (env2, uu____19496))
                    | uu____19519 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19385 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19607 =
          let uu____19608 = unparen t  in uu____19608.FStar_Parser_AST.tm  in
        match uu____19607 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____19609; FStar_Ident.ident = uu____19610;
              FStar_Ident.nsstr = uu____19611; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____19616 ->
            let uu____19617 =
              let uu____19623 =
                let uu____19625 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19625  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19623)  in
            FStar_Errors.raise_error uu____19617 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19642) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19644) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19647 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19665 = binder_ident b  in
         FStar_Common.list_of_option uu____19665) bs
  
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
               (fun uu___13_19702  ->
                  match uu___13_19702 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19707 -> false))
           in
        let quals2 q =
          let uu____19721 =
            (let uu____19725 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19725) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19721
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19742 = FStar_Ident.range_of_lid disc_name  in
                let uu____19743 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19742;
                  FStar_Syntax_Syntax.sigquals = uu____19743;
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
            let uu____19783 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19821  ->
                        match uu____19821 with
                        | (x,uu____19832) ->
                            let uu____19837 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19837 with
                             | (field_name,uu____19845) ->
                                 let only_decl =
                                   ((let uu____19850 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19850)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19852 =
                                        let uu____19854 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19854.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19852)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19872 =
                                       FStar_List.filter
                                         (fun uu___14_19876  ->
                                            match uu___14_19876 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19879 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19872
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___15_19894  ->
                                             match uu___15_19894 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19899 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19902 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19902;
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
                                      let uu____19909 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19909
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one
                                       in
                                    let lb =
                                      let uu____19920 =
                                        let uu____19925 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19925  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19920;
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
                                      let uu____19929 =
                                        let uu____19930 =
                                          let uu____19937 =
                                            let uu____19940 =
                                              let uu____19941 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19941
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19940]  in
                                          ((false, [lb]), uu____19937)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19930
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19929;
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
            FStar_All.pipe_right uu____19783 FStar_List.flatten
  
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
            (lid,uu____19990,t,uu____19992,n1,uu____19994) when
            let uu____20001 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20001 ->
            let uu____20003 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20003 with
             | (formals,uu____20021) ->
                 (match formals with
                  | [] -> []
                  | uu____20050 ->
                      let filter_records uu___16_20066 =
                        match uu___16_20066 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20069,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20081 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20083 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20083 with
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
                      let uu____20095 = FStar_Util.first_N n1 formals  in
                      (match uu____20095 with
                       | (uu____20124,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20158 -> []
  
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
                        let uu____20252 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20252
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20276 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20276
                        then
                          let uu____20282 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20282
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20286 =
                          let uu____20291 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20291  in
                        let uu____20292 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20298 =
                              let uu____20301 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20301  in
                            FStar_Syntax_Util.arrow typars uu____20298
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20306 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20286;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20292;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20306;
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
          let tycon_id uu___17_20360 =
            match uu___17_20360 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____20362,uu____20363) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____20373,uu____20374,uu____20375) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____20385,uu____20386,uu____20387) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____20409,uu____20410,uu____20411) -> id1
             in
          let binder_to_term1 b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20449) ->
                let uu____20450 =
                  let uu____20451 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20451  in
                FStar_Parser_AST.mk_term uu____20450 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20453 =
                  let uu____20454 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20454  in
                FStar_Parser_AST.mk_term uu____20453 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20456) ->
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
              | uu____20487 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20495 =
                     let uu____20496 =
                       let uu____20503 = binder_to_term1 b  in
                       (out, uu____20503, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20496  in
                   FStar_Parser_AST.mk_term uu____20495
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20515 =
            match uu___18_20515 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____20559  ->
                       match uu____20559 with
                       | (x,t) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20567 =
                    let uu____20568 =
                      let uu____20569 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____20569  in
                    FStar_Parser_AST.mk_term uu____20568
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20567 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____20576 = binder_idents parms  in id1 ::
                    uu____20576
                   in
                (FStar_List.iter
                   (fun uu____20589  ->
                      match uu____20589 with
                      | (f,uu____20595) ->
                          let uu____20596 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____20596
                          then
                            let uu____20601 =
                              let uu____20607 =
                                let uu____20609 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20609
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20607)
                               in
                            FStar_Errors.raise_error uu____20601
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____20615 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20615)))
            | uu____20669 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20709 =
            match uu___19_20709 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20733 = typars_of_binders _env binders  in
                (match uu____20733 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20769 =
                         let uu____20770 =
                           let uu____20771 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20771  in
                         FStar_Parser_AST.mk_term uu____20770
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20769 binders  in
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
                     let uu____20780 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20780 with
                      | (_env1,uu____20797) ->
                          let uu____20804 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id1 FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20804 with
                           | (_env2,uu____20821) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20828 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20871 =
              FStar_List.fold_left
                (fun uu____20905  ->
                   fun uu____20906  ->
                     match (uu____20905, uu____20906) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____20975 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____20975 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20871 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21066 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____21066
                | uu____21067 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____21075 = desugar_abstract_tc quals env [] tc  in
              (match uu____21075 with
               | (uu____21088,uu____21089,se,uu____21091) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21094,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21113 =
                                 let uu____21115 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21115  in
                               if uu____21113
                               then
                                 let uu____21118 =
                                   let uu____21124 =
                                     let uu____21126 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21126
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21124)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21118
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
                           | uu____21139 ->
                               let uu____21140 =
                                 let uu____21147 =
                                   let uu____21148 =
                                     let uu____21163 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21163)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21148
                                    in
                                 FStar_Syntax_Syntax.mk uu____21147  in
                               uu____21140 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2879_21176 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2879_21176.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2879_21176.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2879_21176.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2879_21176.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21177 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____21192 = typars_of_binders env binders  in
              (match uu____21192 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21226 =
                           FStar_Util.for_some
                             (fun uu___20_21229  ->
                                match uu___20_21229 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21232 -> false) quals
                            in
                         if uu____21226
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21240 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21240
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21245 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21251  ->
                               match uu___21_21251 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21254 -> false))
                        in
                     if uu____21245
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____21268 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21268
                     then
                       let uu____21274 =
                         let uu____21281 =
                           let uu____21282 = unparen t  in
                           uu____21282.FStar_Parser_AST.tm  in
                         match uu____21281 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____21303 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21333)::args_rev ->
                                   let uu____21345 =
                                     let uu____21346 = unparen last_arg  in
                                     uu____21346.FStar_Parser_AST.tm  in
                                   (match uu____21345 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21374 -> ([], args))
                               | uu____21383 -> ([], args)  in
                             (match uu____21303 with
                              | (cattributes,args1) ->
                                  let uu____21422 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21422))
                         | uu____21433 -> (t, [])  in
                       match uu____21274 with
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
                                  (fun uu___22_21456  ->
                                     match uu___22_21456 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21459 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21467)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21487 = tycon_record_as_variant trec  in
              (match uu____21487 with
               | (t,fs) ->
                   let uu____21504 =
                     let uu____21507 =
                       let uu____21508 =
                         let uu____21517 =
                           let uu____21520 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21520  in
                         (uu____21517, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21508  in
                     uu____21507 :: quals  in
                   desugar_tycon env d uu____21504 [t])
          | uu____21525::uu____21526 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21684 = et  in
                match uu____21684 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21894 ->
                         let trec = tc  in
                         let uu____21914 = tycon_record_as_variant trec  in
                         (match uu____21914 with
                          | (t,fs) ->
                              let uu____21970 =
                                let uu____21973 =
                                  let uu____21974 =
                                    let uu____21983 =
                                      let uu____21986 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____21986  in
                                    (uu____21983, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____21974
                                   in
                                uu____21973 :: quals1  in
                              collect_tcs uu____21970 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____22064 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22064 with
                          | (env2,uu____22121,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____22258 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22258 with
                          | (env2,uu____22315,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22431 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22477 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22477 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_22929  ->
                             match uu___24_22929 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____22983,uu____22984);
                                    FStar_Syntax_Syntax.sigrng = uu____22985;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____22986;
                                    FStar_Syntax_Syntax.sigmeta = uu____22987;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____22988;
                                    FStar_Syntax_Syntax.sigopts = uu____22989;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23051 =
                                     typars_of_binders env1 binders  in
                                   match uu____23051 with
                                   | (env2,tpars1) ->
                                       let uu____23078 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23078 with
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
                                 let uu____23107 =
                                   let uu____23118 =
                                     mk_typ_abbrev env1 d id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ([], uu____23118)  in
                                 [uu____23107]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____23154);
                                    FStar_Syntax_Syntax.sigrng = uu____23155;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23157;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23158;
                                    FStar_Syntax_Syntax.sigopts = uu____23159;_},constrs,tconstr,quals1)
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
                                 let uu____23250 = push_tparams env1 tpars
                                    in
                                 (match uu____23250 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23309  ->
                                             match uu____23309 with
                                             | (x,uu____23321) ->
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
                                        let uu____23332 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23332
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23355 =
                                        let uu____23374 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23451  ->
                                                  match uu____23451 with
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
                                                        let uu____23494 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23494
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
                                                                uu___23_23505
                                                                 ->
                                                                match uu___23_23505
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23517
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23525 =
                                                        let uu____23536 =
                                                          let uu____23537 =
                                                            let uu____23538 =
                                                              let uu____23554
                                                                =
                                                                let uu____23555
                                                                  =
                                                                  let uu____23558
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23558
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23555
                                                                 in
                                                              (name, univs1,
                                                                uu____23554,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23538
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23537;
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
                                                        (tps, uu____23536)
                                                         in
                                                      (name, uu____23525)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23374
                                         in
                                      (match uu____23355 with
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
                             | uu____23690 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23771  ->
                             match uu____23771 with | (uu____23782,se) -> se))
                      in
                   let uu____23796 =
                     let uu____23803 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23803 rng
                      in
                   (match uu____23796 with
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
                               (fun uu____23848  ->
                                  match uu____23848 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23896,tps,k,uu____23899,constrs)
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
                                      let uu____23920 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23935 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23952,uu____23953,uu____23954,uu____23955,uu____23956)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____23963
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23935
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____23967 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_23974  ->
                                                          match uu___25_23974
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____23976 ->
                                                              true
                                                          | uu____23986 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____23967))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23920
                                  | uu____23988 -> []))
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
      let uu____24025 =
        FStar_List.fold_left
          (fun uu____24060  ->
             fun b  ->
               match uu____24060 with
               | (env1,binders1) ->
                   let uu____24104 = desugar_binder env1 b  in
                   (match uu____24104 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24127 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24127 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24180 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24025 with
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
          let uu____24284 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24291  ->
                    match uu___26_24291 with
                    | FStar_Syntax_Syntax.Reflectable uu____24293 -> true
                    | uu____24295 -> false))
             in
          if uu____24284
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24300 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24300
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
        let warn1 uu____24351 =
          if warn
          then
            let uu____24353 =
              let uu____24359 =
                let uu____24361 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24361
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24359)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24353
          else ()  in
        let uu____24367 = FStar_Syntax_Util.head_and_args at  in
        match uu____24367 with
        | (hd1,args) ->
            let uu____24420 =
              let uu____24421 = FStar_Syntax_Subst.compress hd1  in
              uu____24421.FStar_Syntax_Syntax.n  in
            (match uu____24420 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24465)::[] ->
                      let uu____24490 =
                        let uu____24495 =
                          let uu____24504 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24504 a1  in
                        uu____24495 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24490 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24527 =
                             let uu____24533 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24533  in
                           (uu____24527, true)
                       | uu____24548 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24564 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24586 -> (FStar_Pervasives_Native.None, false))
  
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
      let uu____24703 =
        parse_attr_with_list warn at FStar_Parser_Const.fail_attr  in
      match uu____24703 with
      | (res,matched) ->
          if matched
          then rebind res false
          else
            (let uu____24752 =
               parse_attr_with_list warn at FStar_Parser_Const.fail_lax_attr
                in
             match uu____24752 with | (res1,uu____24774) -> rebind res1 true)
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____24804 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____24804 with
        | FStar_Pervasives_Native.None  ->
            let uu____24807 =
              let uu____24813 =
                let uu____24815 =
                  let uu____24817 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____24817 " not found"  in
                Prims.op_Hat "Effect name " uu____24815  in
              (FStar_Errors.Fatal_EffectNotFound, uu____24813)  in
            FStar_Errors.raise_error uu____24807 r
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
                    let uu____24973 = desugar_binders monad_env eff_binders
                       in
                    match uu____24973 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____25012 =
                            let uu____25021 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____25021  in
                          FStar_List.length uu____25012  in
                        (if is_layered1 && (num_indices <= Prims.int_one)
                         then
                           (let uu____25055 =
                              let uu____25061 =
                                let uu____25063 =
                                  let uu____25065 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____25065
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____25063  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____25061)
                               in
                            FStar_Errors.raise_error uu____25055
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
                                (uu____25133,uu____25134,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____25136,uu____25137,uu____25138))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25153 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25156 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25168 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25168 mandatory_members)
                              eff_decls
                             in
                          match uu____25156 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25187 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25216  ->
                                        fun decl  ->
                                          match uu____25216 with
                                          | (env2,out) ->
                                              let uu____25236 =
                                                desugar_decl env2 decl  in
                                              (match uu____25236 with
                                               | (env3,ses) ->
                                                   let uu____25249 =
                                                     let uu____25252 =
                                                       FStar_List.hd ses  in
                                                     uu____25252 :: out  in
                                                   (env3, uu____25249)))
                                     (env1, []))
                                 in
                              (match uu____25187 with
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
                                                 (uu____25298,uu____25299,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25302,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25303,(def,uu____25305)::
                                                        (cps_type,uu____25307)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25308;
                                                     FStar_Parser_AST.level =
                                                       uu____25309;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25342 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25342 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25374 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25375 =
                                                        let uu____25376 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25376
                                                         in
                                                      let uu____25383 =
                                                        let uu____25384 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25384
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25374;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25375;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25383
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25391,uu____25392,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25395,defn))::[])
                                                 when for_free || is_layered1
                                                 ->
                                                 let uu____25411 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25411 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25443 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25444 =
                                                        let uu____25445 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25445
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25443;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25444;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25452 ->
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
                                       let uu____25471 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25471
                                        in
                                     let uu____25473 =
                                       let uu____25474 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25474
                                        in
                                     ([], uu____25473)  in
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
                                       let uu____25496 =
                                         let uu____25497 =
                                           let uu____25500 = lookup1 "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25500
                                            in
                                         let uu____25502 =
                                           let uu____25505 = lookup1 "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25505
                                            in
                                         let uu____25507 =
                                           let uu____25510 = lookup1 "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25510
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
                                             uu____25497;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25502;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25507
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25496
                                     else
                                       if is_layered1
                                       then
                                         (let to_comb uu____25544 =
                                            match uu____25544 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____25591 =
                                            let uu____25592 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____25594 =
                                              let uu____25599 =
                                                lookup1 "repr"  in
                                              FStar_All.pipe_right
                                                uu____25599 to_comb
                                               in
                                            let uu____25617 =
                                              let uu____25622 =
                                                lookup1 "return"  in
                                              FStar_All.pipe_right
                                                uu____25622 to_comb
                                               in
                                            let uu____25640 =
                                              let uu____25645 =
                                                lookup1 "bind"  in
                                              FStar_All.pipe_right
                                                uu____25645 to_comb
                                               in
                                            let uu____25663 =
                                              let uu____25668 =
                                                lookup1 "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____25668 to_comb
                                               in
                                            let uu____25686 =
                                              let uu____25691 =
                                                lookup1 "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____25691 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____25592;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____25594;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____25617;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____25640;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____25663;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____25686
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____25591)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_25714  ->
                                                 match uu___27_25714 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____25717 -> true
                                                 | uu____25719 -> false)
                                              qualifiers
                                             in
                                          let uu____25721 =
                                            let uu____25722 =
                                              lookup1 "return_wp"  in
                                            let uu____25724 =
                                              lookup1 "bind_wp"  in
                                            let uu____25726 =
                                              lookup1 "stronger"  in
                                            let uu____25728 =
                                              lookup1 "if_then_else"  in
                                            let uu____25730 =
                                              lookup1 "ite_wp"  in
                                            let uu____25732 =
                                              lookup1 "close_wp"  in
                                            let uu____25734 =
                                              lookup1 "trivial"  in
                                            let uu____25736 =
                                              if rr
                                              then
                                                let uu____25742 =
                                                  lookup1 "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25742
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25746 =
                                              if rr
                                              then
                                                let uu____25752 =
                                                  lookup1 "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25752
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25756 =
                                              if rr
                                              then
                                                let uu____25762 =
                                                  lookup1 "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25762
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____25722;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____25724;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____25726;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____25728;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____25730;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____25732;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____25734;
                                              FStar_Syntax_Syntax.repr =
                                                uu____25736;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____25746;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____25756
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____25721)
                                      in
                                   let sigel =
                                     let uu____25767 =
                                       let uu____25768 =
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
                                           uu____25768
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____25767
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
                                               let uu____25785 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____25785) env3)
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
                let uu____25808 = desugar_binders env1 eff_binders  in
                match uu____25808 with
                | (env2,binders) ->
                    let uu____25845 =
                      let uu____25856 = head_and_args defn  in
                      match uu____25856 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25893 ->
                                let uu____25894 =
                                  let uu____25900 =
                                    let uu____25902 =
                                      let uu____25904 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25904 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25902  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25900)
                                   in
                                FStar_Errors.raise_error uu____25894
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25910 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25940)::args_rev ->
                                let uu____25952 =
                                  let uu____25953 = unparen last_arg  in
                                  uu____25953.FStar_Parser_AST.tm  in
                                (match uu____25952 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25981 -> ([], args))
                            | uu____25990 -> ([], args)  in
                          (match uu____25910 with
                           | (cattributes,args1) ->
                               let uu____26033 = desugar_args env2 args1  in
                               let uu____26034 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____26033, uu____26034))
                       in
                    (match uu____25845 with
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
                          (let uu____26074 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____26074 with
                           | (ed_binders,uu____26088,ed_binders_opening) ->
                               let sub' shift_n uu____26107 =
                                 match uu____26107 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____26122 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____26122 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____26126 =
                                       let uu____26127 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____26127)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____26126
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____26148 =
                                   sub1 ed.FStar_Syntax_Syntax.signature  in
                                 let uu____26149 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub1 ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____26150 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26166 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26167 =
                                          let uu____26168 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26168
                                           in
                                        let uu____26183 =
                                          let uu____26184 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26184
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26166;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26167;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26183
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
                                     uu____26148;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____26149;
                                   FStar_Syntax_Syntax.actions = uu____26150;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26200 =
                                   let uu____26203 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26203 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26200;
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
                                           let uu____26218 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26218) env3)
                                  in
                               let env5 =
                                 let uu____26220 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26220
                                 then
                                   let reflect_lid =
                                     let uu____26227 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26227
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
        let uu____26244 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26244 FStar_Pervasives_Native.snd  in
      let uu____26256 = desugar_decl_noattrs env d  in
      match uu____26256 with
      | (env1,sigelts) ->
          let attrs =
            FStar_List.map (desugar_term env1) d.FStar_Parser_AST.attrs  in
          let val_attrs =
            match sigelts with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____26275;
                FStar_Syntax_Syntax.sigrng = uu____26276;
                FStar_Syntax_Syntax.sigquals = uu____26277;
                FStar_Syntax_Syntax.sigmeta = uu____26278;
                FStar_Syntax_Syntax.sigattrs = uu____26279;
                FStar_Syntax_Syntax.sigopts = uu____26280;_}::[] ->
                let uu____26293 =
                  let uu____26296 =
                    let uu____26299 = FStar_List.hd sigelts  in
                    FStar_Syntax_Util.lids_of_sigelt uu____26299  in
                  FStar_All.pipe_right uu____26296
                    (FStar_List.collect
                       (fun nm  ->
                          let uu____26307 =
                            FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                              env0 nm
                             in
                          FStar_Pervasives_Native.snd uu____26307))
                   in
                FStar_All.pipe_right uu____26293
                  (FStar_List.filter
                     (fun t  ->
                        let uu____26327 = get_fail_attr false t  in
                        FStar_Option.isNone uu____26327))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____26347;
                FStar_Syntax_Syntax.sigrng = uu____26348;
                FStar_Syntax_Syntax.sigquals = uu____26349;
                FStar_Syntax_Syntax.sigmeta = uu____26350;
                FStar_Syntax_Syntax.sigattrs = uu____26351;
                FStar_Syntax_Syntax.sigopts = uu____26352;_}::uu____26353 ->
                let uu____26378 =
                  let uu____26381 =
                    let uu____26384 = FStar_List.hd sigelts  in
                    FStar_Syntax_Util.lids_of_sigelt uu____26384  in
                  FStar_All.pipe_right uu____26381
                    (FStar_List.collect
                       (fun nm  ->
                          let uu____26392 =
                            FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                              env0 nm
                             in
                          FStar_Pervasives_Native.snd uu____26392))
                   in
                FStar_All.pipe_right uu____26378
                  (FStar_List.filter
                     (fun t  ->
                        let uu____26412 = get_fail_attr false t  in
                        FStar_Option.isNone uu____26412))
            | uu____26432 -> []  in
          let attrs1 = FStar_List.append attrs val_attrs  in
          let uu____26436 =
            FStar_List.mapi
              (fun i  ->
                 fun sigelt  ->
                   if i = Prims.int_zero
                   then
                     let uu___3430_26446 = sigelt  in
                     {
                       FStar_Syntax_Syntax.sigel =
                         (uu___3430_26446.FStar_Syntax_Syntax.sigel);
                       FStar_Syntax_Syntax.sigrng =
                         (uu___3430_26446.FStar_Syntax_Syntax.sigrng);
                       FStar_Syntax_Syntax.sigquals =
                         (uu___3430_26446.FStar_Syntax_Syntax.sigquals);
                       FStar_Syntax_Syntax.sigmeta =
                         (uu___3430_26446.FStar_Syntax_Syntax.sigmeta);
                       FStar_Syntax_Syntax.sigattrs = attrs1;
                       FStar_Syntax_Syntax.sigopts =
                         (uu___3430_26446.FStar_Syntax_Syntax.sigopts)
                     }
                   else
                     (let uu___3432_26449 = sigelt  in
                      let uu____26450 =
                        FStar_List.filter
                          (fun at  ->
                             let uu____26456 = get_fail_attr false at  in
                             FStar_Option.isNone uu____26456) attrs1
                         in
                      {
                        FStar_Syntax_Syntax.sigel =
                          (uu___3432_26449.FStar_Syntax_Syntax.sigel);
                        FStar_Syntax_Syntax.sigrng =
                          (uu___3432_26449.FStar_Syntax_Syntax.sigrng);
                        FStar_Syntax_Syntax.sigquals =
                          (uu___3432_26449.FStar_Syntax_Syntax.sigquals);
                        FStar_Syntax_Syntax.sigmeta =
                          (uu___3432_26449.FStar_Syntax_Syntax.sigmeta);
                        FStar_Syntax_Syntax.sigattrs = uu____26450;
                        FStar_Syntax_Syntax.sigopts =
                          (uu___3432_26449.FStar_Syntax_Syntax.sigopts)
                      })) sigelts
             in
          (env1, uu____26436)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26482 = desugar_decl_aux env d  in
      match uu____26482 with
      | (env1,ses) ->
          let uu____26493 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26493)

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
          let uu____26525 = FStar_Syntax_DsEnv.iface env  in
          if uu____26525
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26540 =
               let uu____26542 =
                 let uu____26544 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26545 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26544
                   uu____26545
                  in
               Prims.op_Negation uu____26542  in
             if uu____26540
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26559 =
                  let uu____26561 =
                    let uu____26563 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26563 lid  in
                  Prims.op_Negation uu____26561  in
                if uu____26559
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26577 =
                     let uu____26579 =
                       let uu____26581 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26581
                         lid
                        in
                     Prims.op_Negation uu____26579  in
                   if uu____26577
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26599 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26599, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26628)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26647 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____26656 =
            let uu____26661 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26661 tcs  in
          (match uu____26656 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26678 =
                   let uu____26679 =
                     let uu____26686 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26686  in
                   [uu____26679]  in
                 let uu____26699 =
                   let uu____26702 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26705 =
                     let uu____26716 =
                       let uu____26725 =
                         let uu____26726 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26726  in
                       FStar_Syntax_Syntax.as_arg uu____26725  in
                     [uu____26716]  in
                   FStar_Syntax_Util.mk_app uu____26702 uu____26705  in
                 FStar_Syntax_Util.abs uu____26678 uu____26699
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26766,id1))::uu____26768 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26771::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26775 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26775 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26781 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26781]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26802) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26812,uu____26813,uu____26814,uu____26815,uu____26816)
                     ->
                     let uu____26825 =
                       let uu____26826 =
                         let uu____26827 =
                           let uu____26834 = mkclass lid  in
                           (meths, uu____26834)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26827  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26826;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____26825]
                 | uu____26837 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26871;
                    FStar_Parser_AST.prange = uu____26872;_},uu____26873)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26883;
                    FStar_Parser_AST.prange = uu____26884;_},uu____26885)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26901;
                         FStar_Parser_AST.prange = uu____26902;_},uu____26903);
                    FStar_Parser_AST.prange = uu____26904;_},uu____26905)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26927;
                         FStar_Parser_AST.prange = uu____26928;_},uu____26929);
                    FStar_Parser_AST.prange = uu____26930;_},uu____26931)::[]
                   -> false
               | (p,uu____26960)::[] ->
                   let uu____26969 = is_app_pattern p  in
                   Prims.op_Negation uu____26969
               | uu____26971 -> false)
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
            let uu____27046 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____27046 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____27059 =
                     let uu____27060 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____27060.FStar_Syntax_Syntax.n  in
                   match uu____27059 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____27070) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____27101 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____27126  ->
                                match uu____27126 with
                                | (qs,ats) ->
                                    let uu____27153 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____27153 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____27101 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____27207::uu____27208 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____27211 -> val_quals  in
                            let quals2 =
                              let uu____27215 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27248  ->
                                        match uu____27248 with
                                        | (uu____27262,(uu____27263,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____27215
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____27283 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____27283
                              then
                                let uu____27289 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3610_27304 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3612_27306 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3612_27306.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3612_27306.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3610_27304.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3610_27304.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3610_27304.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3610_27304.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3610_27304.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3610_27304.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____27289)
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
                   | uu____27331 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27339 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27358 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27339 with
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
                       let uu___3635_27395 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3635_27395.FStar_Parser_AST.prange)
                       }
                   | uu____27402 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3639_27409 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3639_27409.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3639_27409.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____27425 =
                     let uu____27426 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____27426  in
                   FStar_Parser_AST.mk_term uu____27425
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____27450 id_opt =
                   match uu____27450 with
                   | (env1,ses) ->
                       let uu____27472 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id1 ->
                             let lid = FStar_Ident.lid_of_ids [id1]  in
                             let branch1 =
                               let uu____27484 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____27484
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____27486 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____27486
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
                               let uu____27492 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____27492
                                in
                             let bv_pat1 =
                               let uu____27496 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____27496
                                in
                             (bv_pat1, branch1)
                          in
                       (match uu____27472 with
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
                            let uu____27557 = desugar_decl env1 id_decl  in
                            (match uu____27557 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____27593 id1 =
                   match uu____27593 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id1)
                    in
                 let build_coverage_check uu____27632 =
                   match uu____27632 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____27656 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____27656 FStar_Util.set_elements
                    in
                 let uu____27663 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____27666 = is_var_pattern pat  in
                      Prims.op_Negation uu____27666)
                    in
                 if uu____27663
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
            let uu____27690 = close_fun env t  in
            desugar_term env uu____27690  in
          let quals1 =
            let uu____27694 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27694
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27706 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27706;
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
                let uu____27719 =
                  let uu____27728 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27728]  in
                let uu____27747 =
                  let uu____27750 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27750
                   in
                FStar_Syntax_Util.arrow uu____27719 uu____27747
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
          let uu____27816 =
            let uu____27818 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____27818  in
          if uu____27816
          then
            let uu____27825 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____27843 =
                    let uu____27846 =
                      let uu____27847 = desugar_term env t  in
                      ([], uu____27847)  in
                    FStar_Pervasives_Native.Some uu____27846  in
                  (uu____27843, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____27860 =
                    let uu____27863 =
                      let uu____27864 = desugar_term env wp  in
                      ([], uu____27864)  in
                    FStar_Pervasives_Native.Some uu____27863  in
                  let uu____27871 =
                    let uu____27874 =
                      let uu____27875 = desugar_term env t  in
                      ([], uu____27875)  in
                    FStar_Pervasives_Native.Some uu____27874  in
                  (uu____27860, uu____27871)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____27887 =
                    let uu____27890 =
                      let uu____27891 = desugar_term env t  in
                      ([], uu____27891)  in
                    FStar_Pervasives_Native.Some uu____27890  in
                  (FStar_Pervasives_Native.None, uu____27887)
               in
            (match uu____27825 with
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
                   let uu____27925 =
                     let uu____27928 =
                       let uu____27929 = desugar_term env t  in
                       ([], uu____27929)  in
                     FStar_Pervasives_Native.Some uu____27928  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____27925
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
             | uu____27936 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind1) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n1 = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____27949 =
            let uu____27950 =
              let uu____27951 =
                let uu____27952 =
                  let uu____27963 =
                    let uu____27964 = desugar_term env bind1  in
                    ([], uu____27964)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n1.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____27963,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____27952  in
              {
                FStar_Syntax_Syntax.sigel = uu____27951;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____27950]  in
          (env, uu____27949)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____27983 =
              let uu____27984 =
                let uu____27991 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27991, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27984  in
            {
              FStar_Syntax_Syntax.sigel = uu____27983;
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
      let uu____28018 =
        FStar_List.fold_left
          (fun uu____28038  ->
             fun d  ->
               match uu____28038 with
               | (env1,sigelts) ->
                   let uu____28058 = desugar_decl env1 d  in
                   (match uu____28058 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____28018 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28149) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28153;
               FStar_Syntax_Syntax.exports = uu____28154;
               FStar_Syntax_Syntax.is_interface = uu____28155;_},FStar_Parser_AST.Module
             (current_lid,uu____28157)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28166) ->
              let uu____28169 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28169
           in
        let uu____28174 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28216 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28216, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28238 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28238, mname, decls, false)
           in
        match uu____28174 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28280 = desugar_decls env2 decls  in
            (match uu____28280 with
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
          let uu____28348 =
            (FStar_Options.interactive ()) &&
              (let uu____28351 =
                 let uu____28353 =
                   let uu____28355 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28355  in
                 FStar_Util.get_file_extension uu____28353  in
               FStar_List.mem uu____28351 ["fsti"; "fsi"])
             in
          if uu____28348 then as_interface m else m  in
        let uu____28369 = desugar_modul_common curmod env m1  in
        match uu____28369 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28391 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28391, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28413 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28413 with
      | (env1,modul,pop_when_done) ->
          let uu____28430 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28430 with
           | (env2,modul1) ->
               ((let uu____28442 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28442
                 then
                   let uu____28445 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28445
                 else ());
                (let uu____28450 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28450, modul1))))
  
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
        (fun uu____28500  ->
           let uu____28501 = desugar_modul env modul  in
           match uu____28501 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28539  ->
           let uu____28540 = desugar_decls env decls  in
           match uu____28540 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28591  ->
             let uu____28592 = desugar_partial_modul modul env a_modul  in
             match uu____28592 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28687 ->
                  let t =
                    let uu____28697 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28697  in
                  let uu____28710 =
                    let uu____28711 = FStar_Syntax_Subst.compress t  in
                    uu____28711.FStar_Syntax_Syntax.n  in
                  (match uu____28710 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28723,uu____28724)
                       -> bs1
                   | uu____28749 -> failwith "Impossible")
               in
            let uu____28759 =
              let uu____28766 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28766
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28759 with
            | (binders,uu____28768,binders_opening) ->
                let erase_term t =
                  let uu____28776 =
                    let uu____28777 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28777  in
                  FStar_Syntax_Subst.close binders uu____28776  in
                let erase_tscheme uu____28795 =
                  match uu____28795 with
                  | (us,t) ->
                      let t1 =
                        let uu____28815 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28815 t  in
                      let uu____28818 =
                        let uu____28819 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28819  in
                      ([], uu____28818)
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
                    | uu____28842 ->
                        let bs =
                          let uu____28852 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28852  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28892 =
                          let uu____28893 =
                            let uu____28896 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28896  in
                          uu____28893.FStar_Syntax_Syntax.n  in
                        (match uu____28892 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28898,uu____28899) -> bs1
                         | uu____28924 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28932 =
                      let uu____28933 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28933  in
                    FStar_Syntax_Subst.close binders uu____28932  in
                  let uu___3932_28934 = action  in
                  let uu____28935 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28936 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3932_28934.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3932_28934.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28935;
                    FStar_Syntax_Syntax.action_typ = uu____28936
                  }  in
                let uu___3934_28937 = ed  in
                let uu____28938 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28939 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____28940 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____28941 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3934_28937.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3934_28937.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28938;
                  FStar_Syntax_Syntax.signature = uu____28939;
                  FStar_Syntax_Syntax.combinators = uu____28940;
                  FStar_Syntax_Syntax.actions = uu____28941;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3934_28937.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3941_28957 = se  in
                  let uu____28958 =
                    let uu____28959 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28959  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28958;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3941_28957.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3941_28957.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3941_28957.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3941_28957.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3941_28957.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28961 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28962 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28962 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28979 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28979
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28981 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28981)
  