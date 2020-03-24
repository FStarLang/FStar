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
    | FStar_Syntax_Syntax.Sig_fail uu____3504 -> s
    | FStar_Syntax_Syntax.Sig_new_effect uu____3517 -> s
    | FStar_Syntax_Syntax.Sig_sub_effect uu____3518 -> s
    | FStar_Syntax_Syntax.Sig_main uu____3519 -> s
    | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3520 -> s
    | FStar_Syntax_Syntax.Sig_splice uu____3531 -> s
    | FStar_Syntax_Syntax.Sig_pragma uu____3538 -> s
  
let (is_special_effect_combinator : Prims.string -> Prims.bool) =
  fun uu___4_3546  ->
    match uu___4_3546 with
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
    | uu____3595 -> false
  
let rec (sum_to_universe :
  FStar_Syntax_Syntax.universe -> Prims.int -> FStar_Syntax_Syntax.universe)
  =
  fun u  ->
    fun n1  ->
      if n1 = Prims.int_zero
      then u
      else
        (let uu____3616 = sum_to_universe u (n1 - Prims.int_one)  in
         FStar_Syntax_Syntax.U_succ uu____3616)
  
let (int_to_universe : Prims.int -> FStar_Syntax_Syntax.universe) =
  fun n1  -> sum_to_universe FStar_Syntax_Syntax.U_zero n1 
let rec (desugar_maybe_non_constant_universe :
  FStar_Parser_AST.term ->
    (Prims.int,FStar_Syntax_Syntax.universe) FStar_Util.either)
  =
  fun t  ->
    let uu____3642 =
      let uu____3643 = unparen t  in uu____3643.FStar_Parser_AST.tm  in
    match uu____3642 with
    | FStar_Parser_AST.Wild  ->
        let uu____3649 =
          let uu____3650 = FStar_Syntax_Unionfind.univ_fresh ()  in
          FStar_Syntax_Syntax.U_unif uu____3650  in
        FStar_Util.Inr uu____3649
    | FStar_Parser_AST.Uvar u ->
        FStar_Util.Inr (FStar_Syntax_Syntax.U_name u)
    | FStar_Parser_AST.Const (FStar_Const.Const_int (repr,uu____3663)) ->
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
             let uu____3754 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3754
         | (FStar_Util.Inr u,FStar_Util.Inl n1) ->
             let uu____3771 = sum_to_universe u n1  in
             FStar_Util.Inr uu____3771
         | (FStar_Util.Inr u11,FStar_Util.Inr u21) ->
             let uu____3787 =
               let uu____3793 =
                 let uu____3795 = FStar_Parser_AST.term_to_string t  in
                 Prims.op_Hat
                   "This universe might contain a sum of two universe variables "
                   uu____3795
                  in
               (FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars,
                 uu____3793)
                in
             FStar_Errors.raise_error uu____3787 t.FStar_Parser_AST.range)
    | FStar_Parser_AST.App uu____3804 ->
        let rec aux t1 univargs =
          let uu____3841 =
            let uu____3842 = unparen t1  in uu____3842.FStar_Parser_AST.tm
             in
          match uu____3841 with
          | FStar_Parser_AST.App (t2,targ,uu____3850) ->
              let uarg = desugar_maybe_non_constant_universe targ  in
              aux t2 (uarg :: univargs)
          | FStar_Parser_AST.Var max_lid1 ->
              if
                FStar_List.existsb
                  (fun uu___5_3877  ->
                     match uu___5_3877 with
                     | FStar_Util.Inr uu____3884 -> true
                     | uu____3887 -> false) univargs
              then
                let uu____3895 =
                  let uu____3896 =
                    FStar_List.map
                      (fun uu___6_3906  ->
                         match uu___6_3906 with
                         | FStar_Util.Inl n1 -> int_to_universe n1
                         | FStar_Util.Inr u -> u) univargs
                     in
                  FStar_Syntax_Syntax.U_max uu____3896  in
                FStar_Util.Inr uu____3895
              else
                (let nargs =
                   FStar_List.map
                     (fun uu___7_3932  ->
                        match uu___7_3932 with
                        | FStar_Util.Inl n1 -> n1
                        | FStar_Util.Inr uu____3942 -> failwith "impossible")
                     univargs
                    in
                 let uu____3946 =
                   FStar_List.fold_left
                     (fun m  -> fun n1  -> if m > n1 then m else n1)
                     Prims.int_zero nargs
                    in
                 FStar_Util.Inl uu____3946)
          | uu____3962 ->
              let uu____3963 =
                let uu____3969 =
                  let uu____3971 =
                    let uu____3973 = FStar_Parser_AST.term_to_string t1  in
                    Prims.op_Hat uu____3973 " in universe context"  in
                  Prims.op_Hat "Unexpected term " uu____3971  in
                (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3969)  in
              FStar_Errors.raise_error uu____3963 t1.FStar_Parser_AST.range
           in
        aux t []
    | uu____3988 ->
        let uu____3989 =
          let uu____3995 =
            let uu____3997 =
              let uu____3999 = FStar_Parser_AST.term_to_string t  in
              Prims.op_Hat uu____3999 " in universe context"  in
            Prims.op_Hat "Unexpected term " uu____3997  in
          (FStar_Errors.Fatal_UnexpectedTermInUniverse, uu____3995)  in
        FStar_Errors.raise_error uu____3989 t.FStar_Parser_AST.range
  
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
                   FStar_Syntax_Syntax.antiquotes = uu____4040;_});
            FStar_Syntax_Syntax.pos = uu____4041;
            FStar_Syntax_Syntax.vars = uu____4042;_})::uu____4043
        ->
        let uu____4074 =
          let uu____4080 =
            let uu____4082 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4082
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4080)  in
        FStar_Errors.raise_error uu____4074 e.FStar_Syntax_Syntax.pos
    | (bv,e)::uu____4088 ->
        let uu____4107 =
          let uu____4113 =
            let uu____4115 = FStar_Syntax_Print.term_to_string e  in
            FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4115
             in
          (FStar_Errors.Fatal_UnexpectedAntiquotation, uu____4113)  in
        FStar_Errors.raise_error uu____4107 e.FStar_Syntax_Syntax.pos
  
let check_fields :
  'Auu____4128 .
    FStar_Syntax_DsEnv.env ->
      (FStar_Ident.lident * 'Auu____4128) Prims.list ->
        FStar_Range.range -> FStar_Syntax_DsEnv.record_or_dc
  =
  fun env  ->
    fun fields  ->
      fun rg  ->
        let uu____4156 = FStar_List.hd fields  in
        match uu____4156 with
        | (f,uu____4166) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let record =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f
                 in
              let check_field uu____4178 =
                match uu____4178 with
                | (f',uu____4184) ->
                    (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f';
                     (let uu____4186 =
                        FStar_Syntax_DsEnv.belongs_to_record env f' record
                         in
                      if uu____4186
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
              (let uu____4196 = FStar_List.tl fields  in
               FStar_List.iter check_field uu____4196);
              (match () with | () -> record)))
  
let (check_linear_pattern_variables :
  FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list ->
    FStar_Range.range -> unit)
  =
  fun pats  ->
    fun r  ->
      let rec pat_vars p =
        match p.FStar_Syntax_Syntax.v with
        | FStar_Syntax_Syntax.Pat_dot_term uu____4244 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_wild uu____4251 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_constant uu____4252 ->
            FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_var x ->
            FStar_Util.set_add x FStar_Syntax_Syntax.no_names
        | FStar_Syntax_Syntax.Pat_cons (uu____4254,pats1) ->
            let aux out uu____4295 =
              match uu____4295 with
              | (p1,uu____4308) ->
                  let intersection =
                    let uu____4318 = pat_vars p1  in
                    FStar_Util.set_intersect uu____4318 out  in
                  let uu____4321 = FStar_Util.set_is_empty intersection  in
                  if uu____4321
                  then
                    let uu____4326 = pat_vars p1  in
                    FStar_Util.set_union out uu____4326
                  else
                    (let duplicate_bv =
                       let uu____4332 = FStar_Util.set_elements intersection
                          in
                       FStar_List.hd uu____4332  in
                     let uu____4335 =
                       let uu____4341 =
                         FStar_Util.format1
                           "Non-linear patterns are not permitted: `%s` appears more than once in this pattern."
                           (duplicate_bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                          in
                       (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                         uu____4341)
                        in
                     FStar_Errors.raise_error uu____4335 r)
               in
            FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1
         in
      match pats with
      | [] -> ()
      | p::[] ->
          let uu____4365 = pat_vars p  in
          FStar_All.pipe_right uu____4365 (fun a1  -> ())
      | p::ps ->
          let pvars = pat_vars p  in
          let aux p1 =
            let uu____4393 =
              let uu____4395 = pat_vars p1  in
              FStar_Util.set_eq pvars uu____4395  in
            if uu____4393
            then ()
            else
              (let nonlinear_vars =
                 let uu____4404 = pat_vars p1  in
                 FStar_Util.set_symmetric_difference pvars uu____4404  in
               let first_nonlinear_var =
                 let uu____4408 = FStar_Util.set_elements nonlinear_vars  in
                 FStar_List.hd uu____4408  in
               let uu____4411 =
                 let uu____4417 =
                   FStar_Util.format1
                     "Patterns in this match are incoherent, variable %s is bound in some but not all patterns."
                     (first_nonlinear_var.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
                    in
                 (FStar_Errors.Fatal_IncoherentPatterns, uu____4417)  in
               FStar_Errors.raise_error uu____4411 r)
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
          let uu____4732 =
            FStar_Util.find_opt
              (fun y  ->
                 (y.FStar_Syntax_Syntax.ppname).FStar_Ident.idText =
                   x.FStar_Ident.idText) l
             in
          match uu____4732 with
          | FStar_Pervasives_Native.Some y -> (l, e, y)
          | uu____4749 ->
              let uu____4752 = FStar_Syntax_DsEnv.push_bv e x  in
              (match uu____4752 with | (e1,x1) -> ((x1 :: l), e1, x1))
           in
        let rec aux' top loc env1 p1 =
          let pos q =
            FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange  in
          let pos_r r q = FStar_Syntax_Syntax.withinfo q r  in
          let orig = p1  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr uu____4893 ->
              failwith "impossible: PatOr handled below"
          | FStar_Parser_AST.PatOp op ->
              let id_op =
                let uu____4915 =
                  let uu____4921 =
                    FStar_Parser_AST.compile_op Prims.int_zero
                      op.FStar_Ident.idText op.FStar_Ident.idRange
                     in
                  (uu____4921, (op.FStar_Ident.idRange))  in
                FStar_Ident.mk_ident uu____4915  in
              let p2 =
                let uu___929_4926 = p1  in
                {
                  FStar_Parser_AST.pat =
                    (FStar_Parser_AST.PatVar
                       (id_op, FStar_Pervasives_Native.None));
                  FStar_Parser_AST.prange =
                    (uu___929_4926.FStar_Parser_AST.prange)
                }  in
              aux loc env1 p2
          | FStar_Parser_AST.PatAscribed (p2,(t,tacopt)) ->
              ((match tacopt with
                | FStar_Pervasives_Native.None  -> ()
                | FStar_Pervasives_Native.Some uu____4943 ->
                    FStar_Errors.raise_error
                      (FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly,
                        "Type ascriptions within patterns cannot be associated with a tactic")
                      orig.FStar_Parser_AST.prange);
               (let uu____4946 = aux loc env1 p2  in
                match uu____4946 with
                | (loc1,env',binder,p3,annots) ->
                    let uu____5002 =
                      match binder with
                      | LetBinder uu____5023 -> failwith "impossible"
                      | LocalBinder (x,aq) ->
                          let t1 =
                            let uu____5048 = close_fun env1 t  in
                            desugar_term env1 uu____5048  in
                          let x1 =
                            let uu___955_5050 = x  in
                            {
                              FStar_Syntax_Syntax.ppname =
                                (uu___955_5050.FStar_Syntax_Syntax.ppname);
                              FStar_Syntax_Syntax.index =
                                (uu___955_5050.FStar_Syntax_Syntax.index);
                              FStar_Syntax_Syntax.sort = t1
                            }  in
                          ([(x1, t1)], (LocalBinder (x1, aq)))
                       in
                    (match uu____5002 with
                     | (annots',binder1) ->
                         ((match p3.FStar_Syntax_Syntax.v with
                           | FStar_Syntax_Syntax.Pat_var uu____5096 -> ()
                           | FStar_Syntax_Syntax.Pat_wild uu____5097 -> ()
                           | uu____5098 when top && top_level_ascr_allowed ->
                               ()
                           | uu____5099 ->
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
              let uu____5117 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild x)  in
              (loc, env1, (LocalBinder (x, aq1)), uu____5117, [])
          | FStar_Parser_AST.PatConst c ->
              let x =
                FStar_Syntax_Syntax.new_bv
                  (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange))
                  FStar_Syntax_Syntax.tun
                 in
              let uu____5130 =
                FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant c)
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5130, [])
          | FStar_Parser_AST.PatTvar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5148 = resolvex loc env1 x  in
              (match uu____5148 with
               | (loc1,env2,xbv) ->
                   let uu____5180 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5180, []))
          | FStar_Parser_AST.PatVar (x,aq) ->
              let aq1 = trans_aqual env1 aq  in
              let uu____5198 = resolvex loc env1 x  in
              (match uu____5198 with
               | (loc1,env2,xbv) ->
                   let uu____5230 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_var xbv)
                      in
                   (loc1, env2, (LocalBinder (xbv, aq1)), uu____5230, []))
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
              let uu____5244 =
                FStar_All.pipe_left pos
                  (FStar_Syntax_Syntax.Pat_cons (l1, []))
                 in
              (loc, env1, (LocalBinder (x, FStar_Pervasives_Native.None)),
                uu____5244, [])
          | FStar_Parser_AST.PatApp
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatName l;
                 FStar_Parser_AST.prange = uu____5272;_},args)
              ->
              let uu____5278 =
                FStar_List.fold_right
                  (fun arg  ->
                     fun uu____5339  ->
                       match uu____5339 with
                       | (loc1,env2,annots,args1) ->
                           let uu____5420 = aux loc1 env2 arg  in
                           (match uu____5420 with
                            | (loc2,env3,b,arg1,ans) ->
                                let imp = is_implicit b  in
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((arg1, imp) :: args1)))) args
                  (loc, env1, [], [])
                 in
              (match uu____5278 with
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
                   let uu____5592 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args1))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____5592, annots))
          | FStar_Parser_AST.PatApp uu____5608 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern, "Unexpected pattern")
                p1.FStar_Parser_AST.prange
          | FStar_Parser_AST.PatList pats ->
              let uu____5636 =
                FStar_List.fold_right
                  (fun pat  ->
                     fun uu____5686  ->
                       match uu____5686 with
                       | (loc1,env2,annots,pats1) ->
                           let uu____5747 = aux loc1 env2 pat  in
                           (match uu____5747 with
                            | (loc2,env3,uu____5786,pat1,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  (pat1 :: pats1)))) pats (loc, env1, [], [])
                 in
              (match uu____5636 with
               | (loc1,env2,annots,pats1) ->
                   let pat =
                     let uu____5880 =
                       let uu____5883 =
                         let uu____5890 =
                           FStar_Range.end_range p1.FStar_Parser_AST.prange
                            in
                         pos_r uu____5890  in
                       let uu____5891 =
                         let uu____5892 =
                           let uu____5906 =
                             FStar_Syntax_Syntax.lid_as_fv
                               FStar_Parser_Const.nil_lid
                               FStar_Syntax_Syntax.delta_constant
                               (FStar_Pervasives_Native.Some
                                  FStar_Syntax_Syntax.Data_ctor)
                              in
                           (uu____5906, [])  in
                         FStar_Syntax_Syntax.Pat_cons uu____5892  in
                       FStar_All.pipe_left uu____5883 uu____5891  in
                     FStar_List.fold_right
                       (fun hd1  ->
                          fun tl1  ->
                            let r =
                              FStar_Range.union_ranges
                                hd1.FStar_Syntax_Syntax.p
                                tl1.FStar_Syntax_Syntax.p
                               in
                            let uu____5940 =
                              let uu____5941 =
                                let uu____5955 =
                                  FStar_Syntax_Syntax.lid_as_fv
                                    FStar_Parser_Const.cons_lid
                                    FStar_Syntax_Syntax.delta_constant
                                    (FStar_Pervasives_Native.Some
                                       FStar_Syntax_Syntax.Data_ctor)
                                   in
                                (uu____5955, [(hd1, false); (tl1, false)])
                                 in
                              FStar_Syntax_Syntax.Pat_cons uu____5941  in
                            FStar_All.pipe_left (pos_r r) uu____5940) pats1
                       uu____5880
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
              let uu____6011 =
                FStar_List.fold_left
                  (fun uu____6070  ->
                     fun p2  ->
                       match uu____6070 with
                       | (loc1,env2,annots,pats) ->
                           let uu____6152 = aux loc1 env2 p2  in
                           (match uu____6152 with
                            | (loc2,env3,uu____6196,pat,ans) ->
                                (loc2, env3, (FStar_List.append ans annots),
                                  ((pat, false) :: pats))))
                  (loc, env1, [], []) args
                 in
              (match uu____6011 with
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
                     | uu____6359 -> failwith "impossible"  in
                   let x =
                     FStar_Syntax_Syntax.new_bv
                       (FStar_Pervasives_Native.Some
                          (p1.FStar_Parser_AST.prange))
                       FStar_Syntax_Syntax.tun
                      in
                   let uu____6362 =
                     FStar_All.pipe_left pos
                       (FStar_Syntax_Syntax.Pat_cons (l1, args2))
                      in
                   (loc1, env2,
                     (LocalBinder (x, FStar_Pervasives_Native.None)),
                     uu____6362, annots))
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
                     (fun uu____6438  ->
                        match uu____6438 with
                        | (f,p2) -> ((f.FStar_Ident.ident), p2)))
                 in
              let args =
                FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                  (FStar_List.map
                     (fun uu____6468  ->
                        match uu____6468 with
                        | (f,uu____6474) ->
                            let uu____6475 =
                              FStar_All.pipe_right fields1
                                (FStar_List.tryFind
                                   (fun uu____6501  ->
                                      match uu____6501 with
                                      | (g,uu____6508) ->
                                          f.FStar_Ident.idText =
                                            g.FStar_Ident.idText))
                               in
                            (match uu____6475 with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Parser_AST.mk_pattern
                                   (FStar_Parser_AST.PatWild
                                      FStar_Pervasives_Native.None)
                                   p1.FStar_Parser_AST.prange
                             | FStar_Pervasives_Native.Some (uu____6514,p2)
                                 -> p2)))
                 in
              let app =
                let uu____6521 =
                  let uu____6522 =
                    let uu____6529 =
                      let uu____6530 =
                        let uu____6531 =
                          FStar_Ident.lid_of_ids
                            (FStar_List.append
                               (record.FStar_Syntax_DsEnv.typename).FStar_Ident.ns
                               [record.FStar_Syntax_DsEnv.constrname])
                           in
                        FStar_Parser_AST.PatName uu____6531  in
                      FStar_Parser_AST.mk_pattern uu____6530
                        p1.FStar_Parser_AST.prange
                       in
                    (uu____6529, args)  in
                  FStar_Parser_AST.PatApp uu____6522  in
                FStar_Parser_AST.mk_pattern uu____6521
                  p1.FStar_Parser_AST.prange
                 in
              let uu____6534 = aux loc env1 app  in
              (match uu____6534 with
               | (env2,e,b,p2,annots) ->
                   let p3 =
                     match p2.FStar_Syntax_Syntax.v with
                     | FStar_Syntax_Syntax.Pat_cons (fv,args1) ->
                         let uu____6611 =
                           let uu____6612 =
                             let uu____6626 =
                               let uu___1105_6627 = fv  in
                               let uu____6628 =
                                 let uu____6631 =
                                   let uu____6632 =
                                     let uu____6639 =
                                       FStar_All.pipe_right
                                         record.FStar_Syntax_DsEnv.fields
                                         (FStar_List.map
                                            FStar_Pervasives_Native.fst)
                                        in
                                     ((record.FStar_Syntax_DsEnv.typename),
                                       uu____6639)
                                      in
                                   FStar_Syntax_Syntax.Record_ctor uu____6632
                                    in
                                 FStar_Pervasives_Native.Some uu____6631  in
                               {
                                 FStar_Syntax_Syntax.fv_name =
                                   (uu___1105_6627.FStar_Syntax_Syntax.fv_name);
                                 FStar_Syntax_Syntax.fv_delta =
                                   (uu___1105_6627.FStar_Syntax_Syntax.fv_delta);
                                 FStar_Syntax_Syntax.fv_qual = uu____6628
                               }  in
                             (uu____6626, args1)  in
                           FStar_Syntax_Syntax.Pat_cons uu____6612  in
                         FStar_All.pipe_left pos uu____6611
                     | uu____6665 -> p2  in
                   (env2, e, b, p3, annots))
        
        and aux loc env1 p1 = aux' false loc env1 p1
         in
        let aux_maybe_or env1 p1 =
          let loc = []  in
          match p1.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOr [] -> failwith "impossible"
          | FStar_Parser_AST.PatOr (p2::ps) ->
              let uu____6749 = aux' true loc env1 p2  in
              (match uu____6749 with
               | (loc1,env2,var,p3,ans) ->
                   let uu____6802 =
                     FStar_List.fold_left
                       (fun uu____6850  ->
                          fun p4  ->
                            match uu____6850 with
                            | (loc2,env3,ps1) ->
                                let uu____6915 = aux' true loc2 env3 p4  in
                                (match uu____6915 with
                                 | (loc3,env4,uu____6953,p5,ans1) ->
                                     (loc3, env4, ((p5, ans1) :: ps1))))
                       (loc1, env2, []) ps
                      in
                   (match uu____6802 with
                    | (loc2,env3,ps1) ->
                        let pats = (p3, ans) :: (FStar_List.rev ps1)  in
                        (env3, var, pats)))
          | uu____7114 ->
              let uu____7115 = aux' true loc env1 p1  in
              (match uu____7115 with
               | (loc1,env2,vars,pat,ans) -> (env2, vars, [(pat, ans)]))
           in
        let uu____7206 = aux_maybe_or env p  in
        match uu____7206 with
        | (env1,b,pats) ->
            ((let uu____7261 =
                FStar_List.map FStar_Pervasives_Native.fst pats  in
              check_linear_pattern_variables uu____7261
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
            let uu____7335 =
              let uu____7336 =
                let uu____7347 = FStar_Syntax_DsEnv.qualify env x  in
                (uu____7347, (ty, tacopt))  in
              LetBinder uu____7336  in
            (env, uu____7335, [])  in
          let op_to_ident x =
            let uu____7364 =
              let uu____7370 =
                FStar_Parser_AST.compile_op Prims.int_zero
                  x.FStar_Ident.idText x.FStar_Ident.idRange
                 in
              (uu____7370, (x.FStar_Ident.idRange))  in
            FStar_Ident.mk_ident uu____7364  in
          match p.FStar_Parser_AST.pat with
          | FStar_Parser_AST.PatOp x ->
              let uu____7383 = op_to_ident x  in
              mklet uu____7383 FStar_Syntax_Syntax.tun
                FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatVar (x,uu____7385) ->
              mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None
          | FStar_Parser_AST.PatAscribed
              ({ FStar_Parser_AST.pat = FStar_Parser_AST.PatOp x;
                 FStar_Parser_AST.prange = uu____7391;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7407 = op_to_ident x  in
              let uu____7408 = desugar_term env t  in
              mklet uu____7407 uu____7408 tacopt1
          | FStar_Parser_AST.PatAscribed
              ({
                 FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                   (x,uu____7410);
                 FStar_Parser_AST.prange = uu____7411;_},(t,tacopt))
              ->
              let tacopt1 = FStar_Util.map_opt tacopt (desugar_term env)  in
              let uu____7431 = desugar_term env t  in
              mklet x uu____7431 tacopt1
          | uu____7432 ->
              FStar_Errors.raise_error
                (FStar_Errors.Fatal_UnexpectedPattern,
                  "Unexpected pattern at the top-level")
                p.FStar_Parser_AST.prange
        else
          (let uu____7445 = desugar_data_pat true env p  in
           match uu____7445 with
           | (env1,binder,p1) ->
               let p2 =
                 match p1 with
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var
                        uu____7475;
                      FStar_Syntax_Syntax.p = uu____7476;_},uu____7477)::[]
                     -> []
                 | ({
                      FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild
                        uu____7490;
                      FStar_Syntax_Syntax.p = uu____7491;_},uu____7492)::[]
                     -> []
                 | uu____7505 -> p1  in
               (env1, binder, p2))

and (desugar_binding_pat :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.pattern -> (env_t * bnd * annotated_pat Prims.list))
  = fun env  -> fun p  -> desugar_binding_pat_maybe_top false env p

and (desugar_match_pat_maybe_top :
  Prims.bool ->
    env_t -> FStar_Parser_AST.pattern -> (env_t * annotated_pat Prims.list))
  =
  fun uu____7513  ->
    fun env  ->
      fun pat  ->
        let uu____7517 = desugar_data_pat false env pat  in
        match uu____7517 with | (env1,uu____7534,pat1) -> (env1, pat1)

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
      let uu____7556 = desugar_term_aq env e  in
      match uu____7556 with | (t,aq) -> (check_no_aq aq; t)

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
      let uu____7575 = desugar_typ_aq env e  in
      match uu____7575 with | (t,aq) -> (check_no_aq aq; t)

and (desugar_machine_integer :
  FStar_Syntax_DsEnv.env ->
    Prims.string ->
      (FStar_Const.signedness * FStar_Const.width) ->
        FStar_Range.range -> FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun repr  ->
      fun uu____7585  ->
        fun range  ->
          match uu____7585 with
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
              ((let uu____7607 =
                  let uu____7609 =
                    FStar_Const.within_bounds repr signedness width  in
                  Prims.op_Negation uu____7609  in
                if uu____7607
                then
                  let uu____7612 =
                    let uu____7618 =
                      FStar_Util.format2
                        "%s is not in the expected range for %s" repr tnm
                       in
                    (FStar_Errors.Error_OutOfRange, uu____7618)  in
                  FStar_Errors.log_issue range uu____7612
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
                  let uu____7639 = FStar_Ident.path_of_text intro_nm  in
                  FStar_Ident.lid_of_path uu____7639 range  in
                let lid1 =
                  let uu____7643 = FStar_Syntax_DsEnv.try_lookup_lid env lid
                     in
                  match uu____7643 with
                  | FStar_Pervasives_Native.Some intro_term ->
                      (match intro_term.FStar_Syntax_Syntax.n with
                       | FStar_Syntax_Syntax.Tm_fvar fv ->
                           let private_lid =
                             let uu____7653 =
                               FStar_Ident.path_of_text private_intro_nm  in
                             FStar_Ident.lid_of_path uu____7653 range  in
                           let private_fv =
                             let uu____7655 =
                               FStar_Syntax_Util.incr_delta_depth
                                 fv.FStar_Syntax_Syntax.fv_delta
                                in
                             FStar_Syntax_Syntax.lid_as_fv private_lid
                               uu____7655 fv.FStar_Syntax_Syntax.fv_qual
                              in
                           let uu___1272_7656 = intro_term  in
                           {
                             FStar_Syntax_Syntax.n =
                               (FStar_Syntax_Syntax.Tm_fvar private_fv);
                             FStar_Syntax_Syntax.pos =
                               (uu___1272_7656.FStar_Syntax_Syntax.pos);
                             FStar_Syntax_Syntax.vars =
                               (uu___1272_7656.FStar_Syntax_Syntax.vars)
                           }
                       | uu____7657 ->
                           failwith
                             (Prims.op_Hat "Unexpected non-fvar for "
                                intro_nm))
                  | FStar_Pervasives_Native.None  ->
                      let uu____7661 =
                        let uu____7667 =
                          FStar_Util.format1
                            "Unexpected numeric literal.  Restart F* to load %s."
                            tnm
                           in
                        (FStar_Errors.Fatal_UnexpectedNumericLiteral,
                          uu____7667)
                         in
                      FStar_Errors.raise_error uu____7661 range
                   in
                let repr1 =
                  FStar_Syntax_Syntax.mk
                    (FStar_Syntax_Syntax.Tm_constant
                       (FStar_Const.Const_int
                          (repr, FStar_Pervasives_Native.None)))
                    FStar_Pervasives_Native.None range
                   in
                let uu____7687 =
                  let uu____7694 =
                    let uu____7695 =
                      let uu____7712 =
                        let uu____7723 =
                          let uu____7732 =
                            FStar_Syntax_Syntax.as_implicit false  in
                          (repr1, uu____7732)  in
                        [uu____7723]  in
                      (lid1, uu____7712)  in
                    FStar_Syntax_Syntax.Tm_app uu____7695  in
                  FStar_Syntax_Syntax.mk uu____7694  in
                uu____7687 FStar_Pervasives_Native.None range))

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
          let uu___1288_7851 = e  in
          {
            FStar_Syntax_Syntax.n = (uu___1288_7851.FStar_Syntax_Syntax.n);
            FStar_Syntax_Syntax.pos = (top.FStar_Parser_AST.range);
            FStar_Syntax_Syntax.vars =
              (uu___1288_7851.FStar_Syntax_Syntax.vars)
          }  in
        let uu____7854 =
          let uu____7855 = unparen top  in uu____7855.FStar_Parser_AST.tm  in
        match uu____7854 with
        | FStar_Parser_AST.Wild  -> ((setpos FStar_Syntax_Syntax.tun), noaqs)
        | FStar_Parser_AST.Labeled uu____7860 ->
            let uu____7869 = desugar_formula env top  in (uu____7869, noaqs)
        | FStar_Parser_AST.Requires (t,lopt) ->
            let uu____7878 = desugar_formula env t  in (uu____7878, noaqs)
        | FStar_Parser_AST.Ensures (t,lopt) ->
            let uu____7887 = desugar_formula env t  in (uu____7887, noaqs)
        | FStar_Parser_AST.Attributes ts ->
            failwith
              "Attributes should not be desugared by desugar_term_maybe_top"
        | FStar_Parser_AST.Const (FStar_Const.Const_int
            (i,FStar_Pervasives_Native.Some size)) ->
            let uu____7914 =
              desugar_machine_integer env i size top.FStar_Parser_AST.range
               in
            (uu____7914, noaqs)
        | FStar_Parser_AST.Const c ->
            let uu____7916 = mk1 (FStar_Syntax_Syntax.Tm_constant c)  in
            (uu____7916, noaqs)
        | FStar_Parser_AST.Op
            ({ FStar_Ident.idText = "=!="; FStar_Ident.idRange = r;_},args)
            ->
            let e =
              let uu____7925 =
                let uu____7926 =
                  let uu____7933 = FStar_Ident.mk_ident ("==", r)  in
                  (uu____7933, args)  in
                FStar_Parser_AST.Op uu____7926  in
              FStar_Parser_AST.mk_term uu____7925 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            let uu____7938 =
              let uu____7939 =
                let uu____7940 =
                  let uu____7947 = FStar_Ident.mk_ident ("~", r)  in
                  (uu____7947, [e])  in
                FStar_Parser_AST.Op uu____7940  in
              FStar_Parser_AST.mk_term uu____7939 top.FStar_Parser_AST.range
                top.FStar_Parser_AST.level
               in
            desugar_term_aq env uu____7938
        | FStar_Parser_AST.Op (op_star,lhs::rhs::[]) when
            (let uu____7959 = FStar_Ident.text_of_id op_star  in
             uu____7959 = "*") &&
              (let uu____7964 =
                 op_as_term env (Prims.of_int (2)) top.FStar_Parser_AST.range
                   op_star
                  in
               FStar_All.pipe_right uu____7964 FStar_Option.isNone)
            ->
            let rec flatten1 t =
              match t.FStar_Parser_AST.tm with
              | FStar_Parser_AST.Op
                  ({ FStar_Ident.idText = "*";
                     FStar_Ident.idRange = uu____7981;_},t1::t2::[])
                  when
                  let uu____7987 =
                    op_as_term env (Prims.of_int (2))
                      top.FStar_Parser_AST.range op_star
                     in
                  FStar_All.pipe_right uu____7987 FStar_Option.isNone ->
                  let uu____7994 = flatten1 t1  in
                  FStar_List.append uu____7994 [t2]
              | uu____7997 -> [t]  in
            let terms = flatten1 lhs  in
            let t =
              let uu___1336_8002 = top  in
              let uu____8003 =
                let uu____8004 =
                  let uu____8015 =
                    FStar_List.map (fun _8026  -> FStar_Util.Inr _8026) terms
                     in
                  (uu____8015, rhs)  in
                FStar_Parser_AST.Sum uu____8004  in
              {
                FStar_Parser_AST.tm = uu____8003;
                FStar_Parser_AST.range =
                  (uu___1336_8002.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1336_8002.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env t
        | FStar_Parser_AST.Tvar a ->
            let uu____8034 =
              let uu____8035 =
                FStar_Syntax_DsEnv.fail_or2
                  (FStar_Syntax_DsEnv.try_lookup_id env) a
                 in
              FStar_All.pipe_left setpos uu____8035  in
            (uu____8034, noaqs)
        | FStar_Parser_AST.Uvar u ->
            let uu____8041 =
              let uu____8047 =
                let uu____8049 =
                  let uu____8051 = FStar_Ident.text_of_id u  in
                  Prims.op_Hat uu____8051 " in non-universe context"  in
                Prims.op_Hat "Unexpected universe variable " uu____8049  in
              (FStar_Errors.Fatal_UnexpectedUniverseVariable, uu____8047)  in
            FStar_Errors.raise_error uu____8041 top.FStar_Parser_AST.range
        | FStar_Parser_AST.Op (s,args) ->
            let uu____8066 =
              op_as_term env (FStar_List.length args)
                top.FStar_Parser_AST.range s
               in
            (match uu____8066 with
             | FStar_Pervasives_Native.None  ->
                 let uu____8073 =
                   let uu____8079 =
                     let uu____8081 = FStar_Ident.text_of_id s  in
                     Prims.op_Hat "Unexpected or unbound operator: "
                       uu____8081
                      in
                   (FStar_Errors.Fatal_UnepxectedOrUnboundOperator,
                     uu____8079)
                    in
                 FStar_Errors.raise_error uu____8073
                   top.FStar_Parser_AST.range
             | FStar_Pervasives_Native.Some op ->
                 if (FStar_List.length args) > Prims.int_zero
                 then
                   let uu____8096 =
                     let uu____8121 =
                       FStar_All.pipe_right args
                         (FStar_List.map
                            (fun t  ->
                               let uu____8183 = desugar_term_aq env t  in
                               match uu____8183 with
                               | (t',s1) ->
                                   ((t', FStar_Pervasives_Native.None), s1)))
                        in
                     FStar_All.pipe_right uu____8121 FStar_List.unzip  in
                   (match uu____8096 with
                    | (args1,aqs) ->
                        let uu____8316 =
                          mk1 (FStar_Syntax_Syntax.Tm_app (op, args1))  in
                        (uu____8316, (join_aqs aqs)))
                 else (op, noaqs))
        | FStar_Parser_AST.Construct (n1,(a,uu____8333)::[]) when
            n1.FStar_Ident.str = "SMTPat" ->
            let uu____8350 =
              let uu___1365_8351 = top  in
              let uu____8352 =
                let uu____8353 =
                  let uu____8360 =
                    let uu___1367_8361 = top  in
                    let uu____8362 =
                      let uu____8363 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8363  in
                    {
                      FStar_Parser_AST.tm = uu____8362;
                      FStar_Parser_AST.range =
                        (uu___1367_8361.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1367_8361.FStar_Parser_AST.level)
                    }  in
                  (uu____8360, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8353  in
              {
                FStar_Parser_AST.tm = uu____8352;
                FStar_Parser_AST.range =
                  (uu___1365_8351.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1365_8351.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8350
        | FStar_Parser_AST.Construct (n1,(a,uu____8371)::[]) when
            n1.FStar_Ident.str = "SMTPatT" ->
            (FStar_Errors.log_issue top.FStar_Parser_AST.range
               (FStar_Errors.Warning_SMTPatTDeprecated,
                 "SMTPatT is deprecated; please just use SMTPat");
             (let uu____8391 =
                let uu___1377_8392 = top  in
                let uu____8393 =
                  let uu____8394 =
                    let uu____8401 =
                      let uu___1379_8402 = top  in
                      let uu____8403 =
                        let uu____8404 =
                          FStar_Ident.lid_of_path ["Prims"; "smt_pat"]
                            top.FStar_Parser_AST.range
                           in
                        FStar_Parser_AST.Var uu____8404  in
                      {
                        FStar_Parser_AST.tm = uu____8403;
                        FStar_Parser_AST.range =
                          (uu___1379_8402.FStar_Parser_AST.range);
                        FStar_Parser_AST.level =
                          (uu___1379_8402.FStar_Parser_AST.level)
                      }  in
                    (uu____8401, a, FStar_Parser_AST.Nothing)  in
                  FStar_Parser_AST.App uu____8394  in
                {
                  FStar_Parser_AST.tm = uu____8393;
                  FStar_Parser_AST.range =
                    (uu___1377_8392.FStar_Parser_AST.range);
                  FStar_Parser_AST.level =
                    (uu___1377_8392.FStar_Parser_AST.level)
                }  in
              desugar_term_maybe_top top_level env uu____8391))
        | FStar_Parser_AST.Construct (n1,(a,uu____8412)::[]) when
            n1.FStar_Ident.str = "SMTPatOr" ->
            let uu____8429 =
              let uu___1388_8430 = top  in
              let uu____8431 =
                let uu____8432 =
                  let uu____8439 =
                    let uu___1390_8440 = top  in
                    let uu____8441 =
                      let uu____8442 =
                        FStar_Ident.lid_of_path ["Prims"; "smt_pat_or"]
                          top.FStar_Parser_AST.range
                         in
                      FStar_Parser_AST.Var uu____8442  in
                    {
                      FStar_Parser_AST.tm = uu____8441;
                      FStar_Parser_AST.range =
                        (uu___1390_8440.FStar_Parser_AST.range);
                      FStar_Parser_AST.level =
                        (uu___1390_8440.FStar_Parser_AST.level)
                    }  in
                  (uu____8439, a, FStar_Parser_AST.Nothing)  in
                FStar_Parser_AST.App uu____8432  in
              {
                FStar_Parser_AST.tm = uu____8431;
                FStar_Parser_AST.range =
                  (uu___1388_8430.FStar_Parser_AST.range);
                FStar_Parser_AST.level =
                  (uu___1388_8430.FStar_Parser_AST.level)
              }  in
            desugar_term_maybe_top top_level env uu____8429
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8448; FStar_Ident.ident = uu____8449;
              FStar_Ident.nsstr = uu____8450; FStar_Ident.str = "Type0";_}
            ->
            let uu____8455 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_zero)
               in
            (uu____8455, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8456; FStar_Ident.ident = uu____8457;
              FStar_Ident.nsstr = uu____8458; FStar_Ident.str = "Type";_}
            ->
            let uu____8463 =
              mk1 (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
               in
            (uu____8463, noaqs)
        | FStar_Parser_AST.Construct
            ({ FStar_Ident.ns = uu____8464; FStar_Ident.ident = uu____8465;
               FStar_Ident.nsstr = uu____8466; FStar_Ident.str = "Type";_},
             (t,FStar_Parser_AST.UnivApp )::[])
            ->
            let uu____8486 =
              let uu____8487 =
                let uu____8488 = desugar_universe t  in
                FStar_Syntax_Syntax.Tm_type uu____8488  in
              mk1 uu____8487  in
            (uu____8486, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8489; FStar_Ident.ident = uu____8490;
              FStar_Ident.nsstr = uu____8491; FStar_Ident.str = "Effect";_}
            ->
            let uu____8496 =
              mk1 (FStar_Syntax_Syntax.Tm_constant FStar_Const.Const_effect)
               in
            (uu____8496, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8497; FStar_Ident.ident = uu____8498;
              FStar_Ident.nsstr = uu____8499; FStar_Ident.str = "True";_}
            ->
            let uu____8504 =
              let uu____8505 =
                FStar_Ident.set_lid_range FStar_Parser_Const.true_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8505
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8504, noaqs)
        | FStar_Parser_AST.Name
            { FStar_Ident.ns = uu____8506; FStar_Ident.ident = uu____8507;
              FStar_Ident.nsstr = uu____8508; FStar_Ident.str = "False";_}
            ->
            let uu____8513 =
              let uu____8514 =
                FStar_Ident.set_lid_range FStar_Parser_Const.false_lid
                  top.FStar_Parser_AST.range
                 in
              FStar_Syntax_Syntax.fvar uu____8514
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            (uu____8513, noaqs)
        | FStar_Parser_AST.Projector
            (eff_name,{ FStar_Ident.idText = txt;
                        FStar_Ident.idRange = uu____8517;_})
            when
            (is_special_effect_combinator txt) &&
              (FStar_Syntax_DsEnv.is_effect_name env eff_name)
            ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name;
             (let uu____8520 =
                FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name  in
              match uu____8520 with
              | FStar_Pervasives_Native.Some ed ->
                  let lid = FStar_Syntax_Util.dm4f_lid ed txt  in
                  let uu____8529 =
                    FStar_Syntax_Syntax.fvar lid
                      (FStar_Syntax_Syntax.Delta_constant_at_level
                         Prims.int_one) FStar_Pervasives_Native.None
                     in
                  (uu____8529, noaqs)
              | FStar_Pervasives_Native.None  ->
                  let uu____8531 =
                    let uu____8533 = FStar_Ident.text_of_lid eff_name  in
                    FStar_Util.format2
                      "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)"
                      uu____8533 txt
                     in
                  failwith uu____8531))
        | FStar_Parser_AST.Var l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8542 = desugar_name mk1 setpos env true l  in
              (uu____8542, noaqs)))
        | FStar_Parser_AST.Name l ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8551 = desugar_name mk1 setpos env true l  in
              (uu____8551, noaqs)))
        | FStar_Parser_AST.Projector (l,i) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let name =
                let uu____8569 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                   in
                match uu____8569 with
                | FStar_Pervasives_Native.Some uu____8579 ->
                    FStar_Pervasives_Native.Some (true, l)
                | FStar_Pervasives_Native.None  ->
                    let uu____8587 =
                      FStar_Syntax_DsEnv.try_lookup_root_effect_name env l
                       in
                    (match uu____8587 with
                     | FStar_Pervasives_Native.Some new_name ->
                         FStar_Pervasives_Native.Some (false, new_name)
                     | uu____8605 -> FStar_Pervasives_Native.None)
                 in
              match name with
              | FStar_Pervasives_Native.Some (resolve,new_name) ->
                  let uu____8626 =
                    let uu____8627 =
                      FStar_Syntax_Util.mk_field_projector_name_from_ident
                        new_name i
                       in
                    desugar_name mk1 setpos env resolve uu____8627  in
                  (uu____8626, noaqs)
              | uu____8633 ->
                  let uu____8641 =
                    let uu____8647 =
                      FStar_Util.format1
                        "Data constructor or effect %s not found"
                        l.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_EffectNotFound, uu____8647)  in
                  FStar_Errors.raise_error uu____8641
                    top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Discrim lid ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid;
             (let uu____8657 = FStar_Syntax_DsEnv.try_lookup_datacon env lid
                 in
              match uu____8657 with
              | FStar_Pervasives_Native.None  ->
                  let uu____8664 =
                    let uu____8670 =
                      FStar_Util.format1 "Data constructor %s not found"
                        lid.FStar_Ident.str
                       in
                    (FStar_Errors.Fatal_DataContructorNotFound, uu____8670)
                     in
                  FStar_Errors.raise_error uu____8664
                    top.FStar_Parser_AST.range
              | uu____8678 ->
                  let lid' = FStar_Syntax_Util.mk_discriminator lid  in
                  let uu____8682 = desugar_name mk1 setpos env true lid'  in
                  (uu____8682, noaqs)))
        | FStar_Parser_AST.Construct (l,args) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l;
             (let uu____8704 = FStar_Syntax_DsEnv.try_lookup_datacon env l
                 in
              match uu____8704 with
              | FStar_Pervasives_Native.Some head1 ->
                  let head2 = mk1 (FStar_Syntax_Syntax.Tm_fvar head1)  in
                  (match args with
                   | [] -> (head2, noaqs)
                   | uu____8723 ->
                       let uu____8730 =
                         FStar_Util.take
                           (fun uu____8754  ->
                              match uu____8754 with
                              | (uu____8760,imp) ->
                                  imp = FStar_Parser_AST.UnivApp) args
                          in
                       (match uu____8730 with
                        | (universes,args1) ->
                            let universes1 =
                              FStar_List.map
                                (fun x  ->
                                   desugar_universe
                                     (FStar_Pervasives_Native.fst x))
                                universes
                               in
                            let uu____8805 =
                              let uu____8830 =
                                FStar_List.map
                                  (fun uu____8873  ->
                                     match uu____8873 with
                                     | (t,imp) ->
                                         let uu____8890 =
                                           desugar_term_aq env t  in
                                         (match uu____8890 with
                                          | (te,aq) ->
                                              ((arg_withimp_e imp te), aq)))
                                  args1
                                 in
                              FStar_All.pipe_right uu____8830
                                FStar_List.unzip
                               in
                            (match uu____8805 with
                             | (args2,aqs) ->
                                 let head3 =
                                   if universes1 = []
                                   then head2
                                   else
                                     mk1
                                       (FStar_Syntax_Syntax.Tm_uinst
                                          (head2, universes1))
                                    in
                                 let uu____9033 =
                                   mk1
                                     (FStar_Syntax_Syntax.Tm_app
                                        (head3, args2))
                                    in
                                 (uu____9033, (join_aqs aqs)))))
              | FStar_Pervasives_Native.None  ->
                  let err =
                    let uu____9052 =
                      FStar_Syntax_DsEnv.try_lookup_effect_name env l  in
                    match uu____9052 with
                    | FStar_Pervasives_Native.None  ->
                        (FStar_Errors.Fatal_ConstructorNotFound,
                          (Prims.op_Hat "Constructor "
                             (Prims.op_Hat l.FStar_Ident.str " not found")))
                    | FStar_Pervasives_Native.Some uu____9063 ->
                        (FStar_Errors.Fatal_UnexpectedEffect,
                          (Prims.op_Hat "Effect "
                             (Prims.op_Hat l.FStar_Ident.str
                                " used at an unexpected position")))
                     in
                  FStar_Errors.raise_error err top.FStar_Parser_AST.range))
        | FStar_Parser_AST.Sum (binders,t) when
            FStar_Util.for_all
              (fun uu___8_9091  ->
                 match uu___8_9091 with
                 | FStar_Util.Inr uu____9097 -> true
                 | uu____9099 -> false) binders
            ->
            let terms =
              let uu____9108 =
                FStar_All.pipe_right binders
                  (FStar_List.map
                     (fun uu___9_9125  ->
                        match uu___9_9125 with
                        | FStar_Util.Inr x -> x
                        | FStar_Util.Inl uu____9131 -> failwith "Impossible"))
                 in
              FStar_List.append uu____9108 [t]  in
            let uu____9133 =
              let uu____9158 =
                FStar_All.pipe_right terms
                  (FStar_List.map
                     (fun t1  ->
                        let uu____9215 = desugar_typ_aq env t1  in
                        match uu____9215 with
                        | (t',aq) ->
                            let uu____9226 = FStar_Syntax_Syntax.as_arg t'
                               in
                            (uu____9226, aq)))
                 in
              FStar_All.pipe_right uu____9158 FStar_List.unzip  in
            (match uu____9133 with
             | (targs,aqs) ->
                 let tup =
                   let uu____9336 =
                     FStar_Parser_Const.mk_tuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env
                     (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9336
                    in
                 let uu____9345 =
                   mk1 (FStar_Syntax_Syntax.Tm_app (tup, targs))  in
                 (uu____9345, (join_aqs aqs)))
        | FStar_Parser_AST.Sum (binders,t) ->
            let uu____9372 =
              let uu____9389 =
                let uu____9396 =
                  let uu____9403 =
                    FStar_All.pipe_left (fun _9412  -> FStar_Util.Inl _9412)
                      (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName t)
                         t.FStar_Parser_AST.range FStar_Parser_AST.Type_level
                         FStar_Pervasives_Native.None)
                     in
                  [uu____9403]  in
                FStar_List.append binders uu____9396  in
              FStar_List.fold_left
                (fun uu____9457  ->
                   fun b  ->
                     match uu____9457 with
                     | (env1,tparams,typs) ->
                         let uu____9518 =
                           match b with
                           | FStar_Util.Inl b1 -> desugar_binder env1 b1
                           | FStar_Util.Inr t1 ->
                               let uu____9533 = desugar_typ env1 t1  in
                               (FStar_Pervasives_Native.None, uu____9533)
                            in
                         (match uu____9518 with
                          | (xopt,t1) ->
                              let uu____9558 =
                                match xopt with
                                | FStar_Pervasives_Native.None  ->
                                    let uu____9567 =
                                      FStar_Syntax_Syntax.new_bv
                                        (FStar_Pervasives_Native.Some
                                           (top.FStar_Parser_AST.range))
                                        FStar_Syntax_Syntax.tun
                                       in
                                    (env1, uu____9567)
                                | FStar_Pervasives_Native.Some x ->
                                    FStar_Syntax_DsEnv.push_bv env1 x
                                 in
                              (match uu____9558 with
                               | (env2,x) ->
                                   let uu____9587 =
                                     let uu____9590 =
                                       let uu____9593 =
                                         let uu____9594 =
                                           no_annot_abs tparams t1  in
                                         FStar_All.pipe_left
                                           FStar_Syntax_Syntax.as_arg
                                           uu____9594
                                          in
                                       [uu____9593]  in
                                     FStar_List.append typs uu____9590  in
                                   (env2,
                                     (FStar_List.append tparams
                                        [(((let uu___1549_9620 = x  in
                                            {
                                              FStar_Syntax_Syntax.ppname =
                                                (uu___1549_9620.FStar_Syntax_Syntax.ppname);
                                              FStar_Syntax_Syntax.index =
                                                (uu___1549_9620.FStar_Syntax_Syntax.index);
                                              FStar_Syntax_Syntax.sort = t1
                                            })),
                                           FStar_Pervasives_Native.None)]),
                                     uu____9587)))) (env, [], []) uu____9389
               in
            (match uu____9372 with
             | (env1,uu____9648,targs) ->
                 let tup =
                   let uu____9671 =
                     FStar_Parser_Const.mk_dtuple_lid
                       (FStar_List.length targs) top.FStar_Parser_AST.range
                      in
                   FStar_Syntax_DsEnv.fail_or env1
                     (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9671
                    in
                 let uu____9672 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_app (tup, targs))
                    in
                 (uu____9672, noaqs))
        | FStar_Parser_AST.Product (binders,t) ->
            let uu____9691 = uncurry binders t  in
            (match uu____9691 with
             | (bs,t1) ->
                 let rec aux env1 bs1 uu___10_9735 =
                   match uu___10_9735 with
                   | [] ->
                       let cod =
                         desugar_comp top.FStar_Parser_AST.range true env1 t1
                          in
                       let uu____9752 =
                         FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod  in
                       FStar_All.pipe_left setpos uu____9752
                   | hd1::tl1 ->
                       let bb = desugar_binder env1 hd1  in
                       let uu____9776 =
                         as_binder env1 hd1.FStar_Parser_AST.aqual bb  in
                       (match uu____9776 with
                        | (b,env2) -> aux env2 (b :: bs1) tl1)
                    in
                 let uu____9809 = aux env [] bs  in (uu____9809, noaqs))
        | FStar_Parser_AST.Refine (b,f) ->
            let uu____9818 = desugar_binder env b  in
            (match uu____9818 with
             | (FStar_Pervasives_Native.None ,uu____9829) ->
                 failwith "Missing binder in refinement"
             | b1 ->
                 let uu____9844 =
                   as_binder env FStar_Pervasives_Native.None b1  in
                 (match uu____9844 with
                  | ((x,uu____9860),env1) ->
                      let f1 = desugar_formula env1 f  in
                      let uu____9873 =
                        let uu____9874 = FStar_Syntax_Util.refine x f1  in
                        FStar_All.pipe_left setpos uu____9874  in
                      (uu____9873, noaqs)))
        | FStar_Parser_AST.Abs (binders,body) ->
            let bvss = FStar_List.map gather_pattern_bound_vars binders  in
            let check_disjoint sets =
              let rec aux acc sets1 =
                match sets1 with
                | [] -> FStar_Pervasives_Native.None
                | set1::sets2 ->
                    let i = FStar_Util.set_intersect acc set1  in
                    let uu____9952 = FStar_Util.set_is_empty i  in
                    if uu____9952
                    then
                      let uu____9957 = FStar_Util.set_union acc set1  in
                      aux uu____9957 sets2
                    else
                      (let uu____9962 =
                         let uu____9963 = FStar_Util.set_elements i  in
                         FStar_List.hd uu____9963  in
                       FStar_Pervasives_Native.Some uu____9962)
                 in
              let uu____9966 = FStar_Syntax_Syntax.new_id_set ()  in
              aux uu____9966 sets  in
            ((let uu____9970 = check_disjoint bvss  in
              match uu____9970 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some id1 ->
                  let uu____9974 =
                    let uu____9980 =
                      FStar_Util.format1
                        "Non-linear patterns are not permitted: `%s` appears more than once in this function definition."
                        id1.FStar_Ident.idText
                       in
                    (FStar_Errors.Fatal_NonLinearPatternNotPermitted,
                      uu____9980)
                     in
                  let uu____9984 = FStar_Ident.range_of_id id1  in
                  FStar_Errors.raise_error uu____9974 uu____9984);
             (let binders1 =
                FStar_All.pipe_right binders
                  (FStar_List.map replace_unit_pattern)
                 in
              let uu____9992 =
                FStar_List.fold_left
                  (fun uu____10012  ->
                     fun pat  ->
                       match uu____10012 with
                       | (env1,ftvs) ->
                           (match pat.FStar_Parser_AST.pat with
                            | FStar_Parser_AST.PatAscribed
                                (uu____10038,(t,FStar_Pervasives_Native.None
                                              ))
                                ->
                                let uu____10048 =
                                  let uu____10051 = free_type_vars env1 t  in
                                  FStar_List.append uu____10051 ftvs  in
                                (env1, uu____10048)
                            | FStar_Parser_AST.PatAscribed
                                (uu____10056,(t,FStar_Pervasives_Native.Some
                                              tac))
                                ->
                                let uu____10067 =
                                  let uu____10070 = free_type_vars env1 t  in
                                  let uu____10073 =
                                    let uu____10076 = free_type_vars env1 tac
                                       in
                                    FStar_List.append uu____10076 ftvs  in
                                  FStar_List.append uu____10070 uu____10073
                                   in
                                (env1, uu____10067)
                            | uu____10081 -> (env1, ftvs))) (env, [])
                  binders1
                 in
              match uu____9992 with
              | (uu____10090,ftv) ->
                  let ftv1 = sort_ftv ftv  in
                  let binders2 =
                    let uu____10102 =
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
                    FStar_List.append uu____10102 binders1  in
                  let rec aux env1 bs sc_pat_opt pats =
                    match pats with
                    | [] ->
                        let uu____10182 = desugar_term_aq env1 body  in
                        (match uu____10182 with
                         | (body1,aq) ->
                             let body2 =
                               match sc_pat_opt with
                               | FStar_Pervasives_Native.Some (sc,pat) ->
                                   let body2 =
                                     let uu____10217 =
                                       let uu____10218 =
                                         FStar_Syntax_Syntax.pat_bvs pat  in
                                       FStar_All.pipe_right uu____10218
                                         (FStar_List.map
                                            FStar_Syntax_Syntax.mk_binder)
                                        in
                                     FStar_Syntax_Subst.close uu____10217
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
                             let uu____10287 =
                               let uu____10288 =
                                 no_annot_abs (FStar_List.rev bs) body2  in
                               setpos uu____10288  in
                             (uu____10287, aq))
                    | p::rest ->
                        let uu____10301 = desugar_binding_pat env1 p  in
                        (match uu____10301 with
                         | (env2,b,pat) ->
                             let pat1 =
                               match pat with
                               | [] -> FStar_Pervasives_Native.None
                               | (p1,uu____10333)::[] ->
                                   FStar_Pervasives_Native.Some p1
                               | uu____10348 ->
                                   FStar_Errors.raise_error
                                     (FStar_Errors.Fatal_UnsupportedDisjuctivePatterns,
                                       "Disjunctive patterns are not supported in abstractions")
                                     p.FStar_Parser_AST.prange
                                in
                             let uu____10357 =
                               match b with
                               | LetBinder uu____10398 ->
                                   failwith "Impossible"
                               | LocalBinder (x,aq) ->
                                   let sc_pat_opt1 =
                                     match (pat1, sc_pat_opt) with
                                     | (FStar_Pervasives_Native.None
                                        ,uu____10467) -> sc_pat_opt
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.None ) ->
                                         let uu____10521 =
                                           let uu____10530 =
                                             FStar_Syntax_Syntax.bv_to_name x
                                              in
                                           (uu____10530, p1)  in
                                         FStar_Pervasives_Native.Some
                                           uu____10521
                                     | (FStar_Pervasives_Native.Some
                                        p1,FStar_Pervasives_Native.Some
                                        (sc,p')) ->
                                         (match ((sc.FStar_Syntax_Syntax.n),
                                                  (p'.FStar_Syntax_Syntax.v))
                                          with
                                          | (FStar_Syntax_Syntax.Tm_name
                                             uu____10592,uu____10593) ->
                                              let tup2 =
                                                let uu____10595 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.of_int (2))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10595
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10600 =
                                                  let uu____10607 =
                                                    let uu____10608 =
                                                      let uu____10625 =
                                                        mk1
                                                          (FStar_Syntax_Syntax.Tm_fvar
                                                             tup2)
                                                         in
                                                      let uu____10628 =
                                                        let uu____10639 =
                                                          FStar_Syntax_Syntax.as_arg
                                                            sc
                                                           in
                                                        let uu____10648 =
                                                          let uu____10659 =
                                                            let uu____10668 =
                                                              FStar_Syntax_Syntax.bv_to_name
                                                                x
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_Syntax_Syntax.as_arg
                                                              uu____10668
                                                             in
                                                          [uu____10659]  in
                                                        uu____10639 ::
                                                          uu____10648
                                                         in
                                                      (uu____10625,
                                                        uu____10628)
                                                       in
                                                    FStar_Syntax_Syntax.Tm_app
                                                      uu____10608
                                                     in
                                                  FStar_Syntax_Syntax.mk
                                                    uu____10607
                                                   in
                                                uu____10600
                                                  FStar_Pervasives_Native.None
                                                  top.FStar_Parser_AST.range
                                                 in
                                              let p2 =
                                                let uu____10716 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tup2,
                                                       [(p', false);
                                                       (p1, false)]))
                                                  uu____10716
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | (FStar_Syntax_Syntax.Tm_app
                                             (uu____10767,args),FStar_Syntax_Syntax.Pat_cons
                                             (uu____10769,pats1)) ->
                                              let tupn =
                                                let uu____10814 =
                                                  FStar_Parser_Const.mk_tuple_data_lid
                                                    (Prims.int_one +
                                                       (FStar_List.length
                                                          args))
                                                    top.FStar_Parser_AST.range
                                                   in
                                                FStar_Syntax_Syntax.lid_as_fv
                                                  uu____10814
                                                  FStar_Syntax_Syntax.delta_constant
                                                  (FStar_Pervasives_Native.Some
                                                     FStar_Syntax_Syntax.Data_ctor)
                                                 in
                                              let sc1 =
                                                let uu____10827 =
                                                  let uu____10828 =
                                                    let uu____10845 =
                                                      mk1
                                                        (FStar_Syntax_Syntax.Tm_fvar
                                                           tupn)
                                                       in
                                                    let uu____10848 =
                                                      let uu____10859 =
                                                        let uu____10870 =
                                                          let uu____10879 =
                                                            FStar_Syntax_Syntax.bv_to_name
                                                              x
                                                             in
                                                          FStar_All.pipe_left
                                                            FStar_Syntax_Syntax.as_arg
                                                            uu____10879
                                                           in
                                                        [uu____10870]  in
                                                      FStar_List.append args
                                                        uu____10859
                                                       in
                                                    (uu____10845,
                                                      uu____10848)
                                                     in
                                                  FStar_Syntax_Syntax.Tm_app
                                                    uu____10828
                                                   in
                                                mk1 uu____10827  in
                                              let p2 =
                                                let uu____10927 =
                                                  FStar_Range.union_ranges
                                                    p'.FStar_Syntax_Syntax.p
                                                    p1.FStar_Syntax_Syntax.p
                                                   in
                                                FStar_Syntax_Syntax.withinfo
                                                  (FStar_Syntax_Syntax.Pat_cons
                                                     (tupn,
                                                       (FStar_List.append
                                                          pats1 [(p1, false)])))
                                                  uu____10927
                                                 in
                                              FStar_Pervasives_Native.Some
                                                (sc1, p2)
                                          | uu____10974 ->
                                              failwith "Impossible")
                                      in
                                   ((x, aq), sc_pat_opt1)
                                in
                             (match uu____10357 with
                              | (b1,sc_pat_opt1) ->
                                  aux env2 (b1 :: bs) sc_pat_opt1 rest))
                     in
                  aux env [] FStar_Pervasives_Native.None binders2))
        | FStar_Parser_AST.App
            (uu____11066,uu____11067,FStar_Parser_AST.UnivApp ) ->
            let rec aux universes e =
              let uu____11089 =
                let uu____11090 = unparen e  in
                uu____11090.FStar_Parser_AST.tm  in
              match uu____11089 with
              | FStar_Parser_AST.App (e1,t,FStar_Parser_AST.UnivApp ) ->
                  let univ_arg = desugar_universe t  in
                  aux (univ_arg :: universes) e1
              | uu____11100 ->
                  let uu____11101 = desugar_term_aq env e  in
                  (match uu____11101 with
                   | (head1,aq) ->
                       let uu____11114 =
                         mk1
                           (FStar_Syntax_Syntax.Tm_uinst (head1, universes))
                          in
                       (uu____11114, aq))
               in
            aux [] top
        | FStar_Parser_AST.App uu____11121 ->
            let rec aux args aqs e =
              let uu____11198 =
                let uu____11199 = unparen e  in
                uu____11199.FStar_Parser_AST.tm  in
              match uu____11198 with
              | FStar_Parser_AST.App (e1,t,imp) when
                  imp <> FStar_Parser_AST.UnivApp ->
                  let uu____11217 = desugar_term_aq env t  in
                  (match uu____11217 with
                   | (t1,aq) ->
                       let arg = arg_withimp_e imp t1  in
                       aux (arg :: args) (aq :: aqs) e1)
              | uu____11265 ->
                  let uu____11266 = desugar_term_aq env e  in
                  (match uu____11266 with
                   | (head1,aq) ->
                       let uu____11287 =
                         mk1 (FStar_Syntax_Syntax.Tm_app (head1, args))  in
                       (uu____11287, (join_aqs (aq :: aqs))))
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
            let uu____11350 =
              FStar_Parser_AST.mkExplicitApp bind1 [t1; k]
                top.FStar_Parser_AST.range
               in
            desugar_term_aq env uu____11350
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
            let uu____11402 = desugar_term_aq env t  in
            (match uu____11402 with
             | (tm,s) ->
                 let uu____11413 =
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (tm,
                          (FStar_Syntax_Syntax.Meta_desugared
                             FStar_Syntax_Syntax.Sequence)))
                    in
                 (uu____11413, s))
        | FStar_Parser_AST.LetOpen (lid,e) ->
            let env1 = FStar_Syntax_DsEnv.push_namespace env lid  in
            let uu____11419 =
              let uu____11432 = FStar_Syntax_DsEnv.expect_typ env1  in
              if uu____11432 then desugar_typ_aq else desugar_term_aq  in
            uu____11419 env1 e
        | FStar_Parser_AST.Let (qual,lbs,body) ->
            let is_rec = qual = FStar_Parser_AST.Rec  in
            let ds_let_rec_or_app uu____11499 =
              let bindings = lbs  in
              let funs =
                FStar_All.pipe_right bindings
                  (FStar_List.map
                     (fun uu____11642  ->
                        match uu____11642 with
                        | (attr_opt,(p,def)) ->
                            let uu____11700 = is_app_pattern p  in
                            if uu____11700
                            then
                              let uu____11733 =
                                destruct_app_pattern env top_level p  in
                              (attr_opt, uu____11733, def)
                            else
                              (match FStar_Parser_AST.un_function p def with
                               | FStar_Pervasives_Native.Some (p1,def1) ->
                                   let uu____11816 =
                                     destruct_app_pattern env top_level p1
                                      in
                                   (attr_opt, uu____11816, def1)
                               | uu____11861 ->
                                   (match p.FStar_Parser_AST.pat with
                                    | FStar_Parser_AST.PatAscribed
                                        ({
                                           FStar_Parser_AST.pat =
                                             FStar_Parser_AST.PatVar
                                             (id1,uu____11899);
                                           FStar_Parser_AST.prange =
                                             uu____11900;_},t)
                                        ->
                                        if top_level
                                        then
                                          let uu____11949 =
                                            let uu____11970 =
                                              let uu____11975 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____11975  in
                                            (uu____11970, [],
                                              (FStar_Pervasives_Native.Some t))
                                             in
                                          (attr_opt, uu____11949, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              (FStar_Pervasives_Native.Some t)),
                                            def)
                                    | FStar_Parser_AST.PatVar
                                        (id1,uu____12067) ->
                                        if top_level
                                        then
                                          let uu____12103 =
                                            let uu____12124 =
                                              let uu____12129 =
                                                FStar_Syntax_DsEnv.qualify
                                                  env id1
                                                 in
                                              FStar_Util.Inr uu____12129  in
                                            (uu____12124, [],
                                              FStar_Pervasives_Native.None)
                                             in
                                          (attr_opt, uu____12103, def)
                                        else
                                          (attr_opt,
                                            ((FStar_Util.Inl id1), [],
                                              FStar_Pervasives_Native.None),
                                            def)
                                    | uu____12220 ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_UnexpectedLetBinding,
                                            "Unexpected let binding")
                                          p.FStar_Parser_AST.prange))))
                 in
              let uu____12253 =
                FStar_List.fold_left
                  (fun uu____12342  ->
                     fun uu____12343  ->
                       match (uu____12342, uu____12343) with
                       | ((env1,fnames,rec_bindings,used_markers),(_attr_opt,
                                                                   (f,uu____12473,uu____12474),uu____12475))
                           ->
                           let uu____12609 =
                             match f with
                             | FStar_Util.Inl x ->
                                 let uu____12649 =
                                   FStar_Syntax_DsEnv.push_bv' env1 x  in
                                 (match uu____12649 with
                                  | (env2,xx,used_marker) ->
                                      let dummy_ref = FStar_Util.mk_ref true
                                         in
                                      let uu____12684 =
                                        let uu____12687 =
                                          FStar_Syntax_Syntax.mk_binder xx
                                           in
                                        uu____12687 :: rec_bindings  in
                                      (env2, (FStar_Util.Inl xx),
                                        uu____12684, (used_marker ::
                                        used_markers)))
                             | FStar_Util.Inr l ->
                                 let uu____12703 =
                                   FStar_Syntax_DsEnv.push_top_level_rec_binding
                                     env1 l.FStar_Ident.ident
                                     FStar_Syntax_Syntax.delta_equational
                                    in
                                 (match uu____12703 with
                                  | (env2,used_marker) ->
                                      (env2, (FStar_Util.Inr l),
                                        rec_bindings, (used_marker ::
                                        used_markers)))
                              in
                           (match uu____12609 with
                            | (env2,lbname,rec_bindings1,used_markers1) ->
                                (env2, (lbname :: fnames), rec_bindings1,
                                  used_markers1))) (env, [], [], []) funs
                 in
              match uu____12253 with
              | (env',fnames,rec_bindings,used_markers) ->
                  let fnames1 = FStar_List.rev fnames  in
                  let rec_bindings1 = FStar_List.rev rec_bindings  in
                  let used_markers1 = FStar_List.rev used_markers  in
                  let desugar_one_def env1 lbname uu____12956 =
                    match uu____12956 with
                    | (attrs_opt,(uu____12996,args,result_t),def) ->
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
                                let uu____13088 = is_comp_type env1 t  in
                                if uu____13088
                                then
                                  ((let uu____13092 =
                                      FStar_All.pipe_right args1
                                        (FStar_List.tryFind
                                           (fun x  ->
                                              let uu____13102 =
                                                is_var_pattern x  in
                                              Prims.op_Negation uu____13102))
                                       in
                                    match uu____13092 with
                                    | FStar_Pervasives_Native.None  -> ()
                                    | FStar_Pervasives_Native.Some p ->
                                        FStar_Errors.raise_error
                                          (FStar_Errors.Fatal_ComputationTypeNotAllowed,
                                            "Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")
                                          p.FStar_Parser_AST.prange);
                                   t)
                                else
                                  (let uu____13109 =
                                     ((FStar_Options.ml_ish ()) &&
                                        (let uu____13112 =
                                           FStar_Syntax_DsEnv.try_lookup_effect_name
                                             env1
                                             FStar_Parser_Const.effect_ML_lid
                                            in
                                         FStar_Option.isSome uu____13112))
                                       &&
                                       ((Prims.op_Negation is_rec) ||
                                          ((FStar_List.length args1) <>
                                             Prims.int_zero))
                                      in
                                   if uu____13109
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
                          | uu____13123 ->
                              FStar_Parser_AST.mk_term
                                (FStar_Parser_AST.un_curry_abs args1 def1)
                                top.FStar_Parser_AST.range
                                top.FStar_Parser_AST.level
                           in
                        let uu____13126 = desugar_term_aq env1 def2  in
                        (match uu____13126 with
                         | (body1,aq) ->
                             let lbname1 =
                               match lbname with
                               | FStar_Util.Inl x -> FStar_Util.Inl x
                               | FStar_Util.Inr l ->
                                   let uu____13148 =
                                     let uu____13149 =
                                       FStar_Syntax_Util.incr_delta_qualifier
                                         body1
                                        in
                                     FStar_Syntax_Syntax.lid_as_fv l
                                       uu____13149
                                       FStar_Pervasives_Native.None
                                      in
                                   FStar_Util.Inr uu____13148
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
                  let uu____13190 =
                    let uu____13207 =
                      FStar_List.map2
                        (desugar_one_def (if is_rec then env' else env))
                        fnames1 funs
                       in
                    FStar_All.pipe_right uu____13207 FStar_List.unzip  in
                  (match uu____13190 with
                   | (lbs1,aqss) ->
                       let uu____13349 = desugar_term_aq env' body  in
                       (match uu____13349 with
                        | (body1,aq) ->
                            (if is_rec
                             then
                               FStar_List.iter2
                                 (fun uu____13455  ->
                                    fun used_marker  ->
                                      match uu____13455 with
                                      | (_attr_opt,(f,uu____13529,uu____13530),uu____13531)
                                          ->
                                          let uu____13588 =
                                            let uu____13590 =
                                              FStar_ST.op_Bang used_marker
                                               in
                                            Prims.op_Negation uu____13590  in
                                          if uu____13588
                                          then
                                            let uu____13614 =
                                              match f with
                                              | FStar_Util.Inl x ->
                                                  let uu____13632 =
                                                    FStar_Ident.string_of_ident
                                                      x
                                                     in
                                                  let uu____13634 =
                                                    FStar_Ident.range_of_id x
                                                     in
                                                  (uu____13632, "Local",
                                                    uu____13634)
                                              | FStar_Util.Inr l ->
                                                  let uu____13639 =
                                                    FStar_Ident.string_of_lid
                                                      l
                                                     in
                                                  let uu____13641 =
                                                    FStar_Ident.range_of_lid
                                                      l
                                                     in
                                                  (uu____13639, "Global",
                                                    uu____13641)
                                               in
                                            (match uu____13614 with
                                             | (nm,gl,rng) ->
                                                 let uu____13652 =
                                                   let uu____13658 =
                                                     FStar_Util.format2
                                                       "%s binding %s is recursive but not used in its body"
                                                       gl nm
                                                      in
                                                   (FStar_Errors.Warning_UnusedLetRec,
                                                     uu____13658)
                                                    in
                                                 FStar_Errors.log_issue rng
                                                   uu____13652)
                                          else ()) funs used_markers1
                             else ();
                             (let uu____13666 =
                                let uu____13669 =
                                  let uu____13670 =
                                    let uu____13684 =
                                      FStar_Syntax_Subst.close rec_bindings1
                                        body1
                                       in
                                    ((is_rec, lbs1), uu____13684)  in
                                  FStar_Syntax_Syntax.Tm_let uu____13670  in
                                FStar_All.pipe_left mk1 uu____13669  in
                              (uu____13666,
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
              let uu____13786 = desugar_term_aq env t1  in
              match uu____13786 with
              | (t11,aq0) ->
                  let uu____13807 =
                    desugar_binding_pat_maybe_top top_level env pat  in
                  (match uu____13807 with
                   | (env1,binder,pat1) ->
                       let uu____13837 =
                         match binder with
                         | LetBinder (l,(t,_tacopt)) ->
                             let uu____13879 = desugar_term_aq env1 t2  in
                             (match uu____13879 with
                              | (body1,aq) ->
                                  let fv =
                                    let uu____13901 =
                                      FStar_Syntax_Util.incr_delta_qualifier
                                        t11
                                       in
                                    FStar_Syntax_Syntax.lid_as_fv l
                                      uu____13901
                                      FStar_Pervasives_Native.None
                                     in
                                  let uu____13902 =
                                    FStar_All.pipe_left mk1
                                      (FStar_Syntax_Syntax.Tm_let
                                         ((false,
                                            [mk_lb
                                               (attrs, (FStar_Util.Inr fv),
                                                 t, t11,
                                                 (t11.FStar_Syntax_Syntax.pos))]),
                                           body1))
                                     in
                                  (uu____13902, aq))
                         | LocalBinder (x,uu____13943) ->
                             let uu____13944 = desugar_term_aq env1 t2  in
                             (match uu____13944 with
                              | (body1,aq) ->
                                  let body2 =
                                    match pat1 with
                                    | [] -> body1
                                    | ({
                                         FStar_Syntax_Syntax.v =
                                           FStar_Syntax_Syntax.Pat_wild
                                           uu____13966;
                                         FStar_Syntax_Syntax.p = uu____13967;_},uu____13968)::[]
                                        -> body1
                                    | uu____13981 ->
                                        let uu____13984 =
                                          let uu____13991 =
                                            let uu____13992 =
                                              let uu____14015 =
                                                FStar_Syntax_Syntax.bv_to_name
                                                  x
                                                 in
                                              let uu____14018 =
                                                desugar_disjunctive_pattern
                                                  pat1
                                                  FStar_Pervasives_Native.None
                                                  body1
                                                 in
                                              (uu____14015, uu____14018)  in
                                            FStar_Syntax_Syntax.Tm_match
                                              uu____13992
                                             in
                                          FStar_Syntax_Syntax.mk uu____13991
                                           in
                                        uu____13984
                                          FStar_Pervasives_Native.None
                                          top.FStar_Parser_AST.range
                                     in
                                  let uu____14055 =
                                    let uu____14058 =
                                      let uu____14059 =
                                        let uu____14073 =
                                          let uu____14076 =
                                            let uu____14077 =
                                              FStar_Syntax_Syntax.mk_binder x
                                               in
                                            [uu____14077]  in
                                          FStar_Syntax_Subst.close
                                            uu____14076 body2
                                           in
                                        ((false,
                                           [mk_lb
                                              (attrs, (FStar_Util.Inl x),
                                                (x.FStar_Syntax_Syntax.sort),
                                                t11,
                                                (t11.FStar_Syntax_Syntax.pos))]),
                                          uu____14073)
                                         in
                                      FStar_Syntax_Syntax.Tm_let uu____14059
                                       in
                                    FStar_All.pipe_left mk1 uu____14058  in
                                  (uu____14055, aq))
                          in
                       (match uu____13837 with
                        | (tm,aq1) -> (tm, (FStar_List.append aq0 aq1))))
               in
            let uu____14185 = FStar_List.hd lbs  in
            (match uu____14185 with
             | (attrs,(head_pat,defn)) ->
                 let uu____14229 = is_rec || (is_app_pattern head_pat)  in
                 if uu____14229
                 then ds_let_rec_or_app ()
                 else ds_non_rec attrs head_pat defn body)
        | FStar_Parser_AST.If (t1,t2,t3) ->
            let x =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let t_bool1 =
              let uu____14245 =
                let uu____14246 =
                  FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid
                    FStar_Syntax_Syntax.delta_constant
                    FStar_Pervasives_Native.None
                   in
                FStar_Syntax_Syntax.Tm_fvar uu____14246  in
              mk1 uu____14245  in
            let uu____14247 = desugar_term_aq env t1  in
            (match uu____14247 with
             | (t1',aq1) ->
                 let uu____14258 = desugar_term_aq env t2  in
                 (match uu____14258 with
                  | (t2',aq2) ->
                      let uu____14269 = desugar_term_aq env t3  in
                      (match uu____14269 with
                       | (t3',aq3) ->
                           let uu____14280 =
                             let uu____14281 =
                               let uu____14282 =
                                 let uu____14305 =
                                   let uu____14322 =
                                     let uu____14337 =
                                       FStar_Syntax_Syntax.withinfo
                                         (FStar_Syntax_Syntax.Pat_constant
                                            (FStar_Const.Const_bool true))
                                         t1.FStar_Parser_AST.range
                                        in
                                     (uu____14337,
                                       FStar_Pervasives_Native.None, t2')
                                      in
                                   let uu____14351 =
                                     let uu____14368 =
                                       let uu____14383 =
                                         FStar_Syntax_Syntax.withinfo
                                           (FStar_Syntax_Syntax.Pat_wild x)
                                           t1.FStar_Parser_AST.range
                                          in
                                       (uu____14383,
                                         FStar_Pervasives_Native.None, t3')
                                        in
                                     [uu____14368]  in
                                   uu____14322 :: uu____14351  in
                                 (t1', uu____14305)  in
                               FStar_Syntax_Syntax.Tm_match uu____14282  in
                             mk1 uu____14281  in
                           (uu____14280, (join_aqs [aq1; aq2; aq3])))))
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
            let desugar_branch uu____14579 =
              match uu____14579 with
              | (pat,wopt,b) ->
                  let uu____14601 = desugar_match_pat env pat  in
                  (match uu____14601 with
                   | (env1,pat1) ->
                       let wopt1 =
                         match wopt with
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pervasives_Native.None
                         | FStar_Pervasives_Native.Some e1 ->
                             let uu____14632 = desugar_term env1 e1  in
                             FStar_Pervasives_Native.Some uu____14632
                          in
                       let uu____14637 = desugar_term_aq env1 b  in
                       (match uu____14637 with
                        | (b1,aq) ->
                            let uu____14650 =
                              desugar_disjunctive_pattern pat1 wopt1 b1  in
                            (uu____14650, aq)))
               in
            let uu____14655 = desugar_term_aq env e  in
            (match uu____14655 with
             | (e1,aq) ->
                 let uu____14666 =
                   let uu____14697 =
                     let uu____14730 = FStar_List.map desugar_branch branches
                        in
                     FStar_All.pipe_right uu____14730 FStar_List.unzip  in
                   FStar_All.pipe_right uu____14697
                     (fun uu____14948  ->
                        match uu____14948 with
                        | (x,y) -> ((FStar_List.flatten x), y))
                    in
                 (match uu____14666 with
                  | (brs,aqs) ->
                      let uu____15167 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_match (e1, brs))
                         in
                      (uu____15167, (join_aqs (aq :: aqs)))))
        | FStar_Parser_AST.Ascribed (e,t,tac_opt) ->
            let uu____15201 =
              let uu____15222 = is_comp_type env t  in
              if uu____15222
              then
                let comp = desugar_comp t.FStar_Parser_AST.range true env t
                   in
                ((FStar_Util.Inr comp), [])
              else
                (let uu____15277 = desugar_term_aq env t  in
                 match uu____15277 with
                 | (tm,aq) -> ((FStar_Util.Inl tm), aq))
               in
            (match uu____15201 with
             | (annot,aq0) ->
                 let tac_opt1 = FStar_Util.map_opt tac_opt (desugar_term env)
                    in
                 let uu____15369 = desugar_term_aq env e  in
                 (match uu____15369 with
                  | (e1,aq) ->
                      let uu____15380 =
                        FStar_All.pipe_left mk1
                          (FStar_Syntax_Syntax.Tm_ascribed
                             (e1, (annot, tac_opt1),
                               FStar_Pervasives_Native.None))
                         in
                      (uu____15380, (FStar_List.append aq0 aq))))
        | FStar_Parser_AST.Record (uu____15419,[]) ->
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_UnexpectedEmptyRecord,
                "Unexpected empty record") top.FStar_Parser_AST.range
        | FStar_Parser_AST.Record (eopt,fields) ->
            let record = check_fields env fields top.FStar_Parser_AST.range
               in
            let user_ns =
              let uu____15462 = FStar_List.hd fields  in
              match uu____15462 with | (f,uu____15474) -> f.FStar_Ident.ns
               in
            let get_field xopt f =
              let found =
                FStar_All.pipe_right fields
                  (FStar_Util.find_opt
                     (fun uu____15520  ->
                        match uu____15520 with
                        | (g,uu____15527) ->
                            f.FStar_Ident.idText =
                              (g.FStar_Ident.ident).FStar_Ident.idText))
                 in
              let fn = FStar_Ident.lid_of_ids (FStar_List.append user_ns [f])
                 in
              match found with
              | FStar_Pervasives_Native.Some (uu____15534,e) -> (fn, e)
              | FStar_Pervasives_Native.None  ->
                  (match xopt with
                   | FStar_Pervasives_Native.None  ->
                       let uu____15548 =
                         let uu____15554 =
                           FStar_Util.format2
                             "Field %s of record type %s is missing"
                             f.FStar_Ident.idText
                             (record.FStar_Syntax_DsEnv.typename).FStar_Ident.str
                            in
                         (FStar_Errors.Fatal_MissingFieldInRecord,
                           uu____15554)
                          in
                       FStar_Errors.raise_error uu____15548
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
                  let uu____15565 =
                    let uu____15576 =
                      FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                        (FStar_List.map
                           (fun uu____15607  ->
                              match uu____15607 with
                              | (f,uu____15617) ->
                                  let uu____15618 =
                                    let uu____15619 =
                                      get_field FStar_Pervasives_Native.None
                                        f
                                       in
                                    FStar_All.pipe_left
                                      FStar_Pervasives_Native.snd uu____15619
                                     in
                                  (uu____15618, FStar_Parser_AST.Nothing)))
                       in
                    (user_constrname, uu____15576)  in
                  FStar_Parser_AST.Construct uu____15565
              | FStar_Pervasives_Native.Some e ->
                  let x = FStar_Ident.gen e.FStar_Parser_AST.range  in
                  let xterm =
                    let uu____15637 =
                      let uu____15638 = FStar_Ident.lid_of_ids [x]  in
                      FStar_Parser_AST.Var uu____15638  in
                    FStar_Parser_AST.mk_term uu____15637
                      x.FStar_Ident.idRange FStar_Parser_AST.Expr
                     in
                  let record1 =
                    let uu____15640 =
                      let uu____15653 =
                        FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields
                          (FStar_List.map
                             (fun uu____15683  ->
                                match uu____15683 with
                                | (f,uu____15693) ->
                                    get_field
                                      (FStar_Pervasives_Native.Some xterm) f))
                         in
                      (FStar_Pervasives_Native.None, uu____15653)  in
                    FStar_Parser_AST.Record uu____15640  in
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
            let uu____15753 = desugar_term_aq env recterm1  in
            (match uu____15753 with
             | (e,s) ->
                 (match e.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_app
                      ({
                         FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar
                           fv;
                         FStar_Syntax_Syntax.pos = uu____15769;
                         FStar_Syntax_Syntax.vars = uu____15770;_},args)
                      ->
                      let uu____15796 =
                        let uu____15797 =
                          let uu____15798 =
                            let uu____15815 =
                              let uu____15818 =
                                FStar_Ident.set_lid_range
                                  (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  e.FStar_Syntax_Syntax.pos
                                 in
                              let uu____15819 =
                                let uu____15822 =
                                  let uu____15823 =
                                    let uu____15830 =
                                      FStar_All.pipe_right
                                        record.FStar_Syntax_DsEnv.fields
                                        (FStar_List.map
                                           FStar_Pervasives_Native.fst)
                                       in
                                    ((record.FStar_Syntax_DsEnv.typename),
                                      uu____15830)
                                     in
                                  FStar_Syntax_Syntax.Record_ctor uu____15823
                                   in
                                FStar_Pervasives_Native.Some uu____15822  in
                              FStar_Syntax_Syntax.fvar uu____15818
                                FStar_Syntax_Syntax.delta_constant
                                uu____15819
                               in
                            (uu____15815, args)  in
                          FStar_Syntax_Syntax.Tm_app uu____15798  in
                        FStar_All.pipe_left mk1 uu____15797  in
                      (uu____15796, s)
                  | uu____15859 -> (e, s)))
        | FStar_Parser_AST.Project (e,f) ->
            (FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f;
             (let uu____15863 =
                FStar_Syntax_DsEnv.fail_or env
                  (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f
                 in
              match uu____15863 with
              | (constrname,is_rec) ->
                  let uu____15882 = desugar_term_aq env e  in
                  (match uu____15882 with
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
                       let uu____15902 =
                         let uu____15903 =
                           let uu____15904 =
                             let uu____15921 =
                               let uu____15924 =
                                 let uu____15925 = FStar_Ident.range_of_lid f
                                    in
                                 FStar_Ident.set_lid_range projname
                                   uu____15925
                                  in
                               FStar_Syntax_Syntax.fvar uu____15924
                                 (FStar_Syntax_Syntax.Delta_equational_at_level
                                    Prims.int_one) qual
                                in
                             let uu____15927 =
                               let uu____15938 =
                                 FStar_Syntax_Syntax.as_arg e1  in
                               [uu____15938]  in
                             (uu____15921, uu____15927)  in
                           FStar_Syntax_Syntax.Tm_app uu____15904  in
                         FStar_All.pipe_left mk1 uu____15903  in
                       (uu____15902, s))))
        | FStar_Parser_AST.NamedTyp (n1,e) ->
            ((let uu____15978 = FStar_Ident.range_of_id n1  in
              FStar_Errors.log_issue uu____15978
                (FStar_Errors.Warning_IgnoredBinding,
                  "This name is being ignored"));
             desugar_term_aq env e)
        | FStar_Parser_AST.Paren e -> failwith "impossible"
        | FStar_Parser_AST.VQuote e ->
            let tm = desugar_term env e  in
            let uu____15989 =
              let uu____15990 = FStar_Syntax_Subst.compress tm  in
              uu____15990.FStar_Syntax_Syntax.n  in
            (match uu____15989 with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____15998 =
                   let uu___2118_15999 =
                     let uu____16000 =
                       let uu____16002 = FStar_Syntax_Syntax.lid_of_fv fv  in
                       FStar_Ident.string_of_lid uu____16002  in
                     FStar_Syntax_Util.exp_string uu____16000  in
                   {
                     FStar_Syntax_Syntax.n =
                       (uu___2118_15999.FStar_Syntax_Syntax.n);
                     FStar_Syntax_Syntax.pos = (e.FStar_Parser_AST.range);
                     FStar_Syntax_Syntax.vars =
                       (uu___2118_15999.FStar_Syntax_Syntax.vars)
                   }  in
                 (uu____15998, noaqs)
             | uu____16003 ->
                 let uu____16004 =
                   let uu____16010 =
                     let uu____16012 = FStar_Syntax_Print.term_to_string tm
                        in
                     Prims.op_Hat "VQuote, expected an fvar, got: "
                       uu____16012
                      in
                   (FStar_Errors.Fatal_UnexpectedTermVQuote, uu____16010)  in
                 FStar_Errors.raise_error uu____16004
                   top.FStar_Parser_AST.range)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Static ) ->
            let uu____16021 = desugar_term_aq env e  in
            (match uu____16021 with
             | (tm,vts) ->
                 let qi =
                   {
                     FStar_Syntax_Syntax.qkind =
                       FStar_Syntax_Syntax.Quote_static;
                     FStar_Syntax_Syntax.antiquotes = vts
                   }  in
                 let uu____16033 =
                   FStar_All.pipe_left mk1
                     (FStar_Syntax_Syntax.Tm_quoted (tm, qi))
                    in
                 (uu____16033, noaqs))
        | FStar_Parser_AST.Antiquote e ->
            let bv =
              FStar_Syntax_Syntax.new_bv
                (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range))
                FStar_Syntax_Syntax.tun
               in
            let uu____16038 = FStar_Syntax_Syntax.bv_to_name bv  in
            let uu____16039 =
              let uu____16040 =
                let uu____16047 = desugar_term env e  in (bv, uu____16047)
                 in
              [uu____16040]  in
            (uu____16038, uu____16039)
        | FStar_Parser_AST.Quote (e,FStar_Parser_AST.Dynamic ) ->
            let qi =
              {
                FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
                FStar_Syntax_Syntax.antiquotes = []
              }  in
            let uu____16072 =
              let uu____16073 =
                let uu____16074 =
                  let uu____16081 = desugar_term env e  in (uu____16081, qi)
                   in
                FStar_Syntax_Syntax.Tm_quoted uu____16074  in
              FStar_All.pipe_left mk1 uu____16073  in
            (uu____16072, noaqs)
        | FStar_Parser_AST.CalcProof (rel,init_expr,steps) ->
            let is_impl rel1 =
              let is_impl_t t =
                match t.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.imp_lid
                | uu____16110 -> false  in
              let uu____16112 =
                let uu____16113 = unparen rel1  in
                uu____16113.FStar_Parser_AST.tm  in
              match uu____16112 with
              | FStar_Parser_AST.Op (id1,uu____16116) ->
                  let uu____16121 =
                    op_as_term env (Prims.of_int (2)) FStar_Range.dummyRange
                      id1
                     in
                  (match uu____16121 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Var lid ->
                  let uu____16129 = desugar_name' (fun x  -> x) env true lid
                     in
                  (match uu____16129 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | FStar_Parser_AST.Tvar id1 ->
                  let uu____16140 = FStar_Syntax_DsEnv.try_lookup_id env id1
                     in
                  (match uu____16140 with
                   | FStar_Pervasives_Native.Some t -> is_impl_t t
                   | FStar_Pervasives_Native.None  -> false)
              | uu____16146 -> false  in
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
              let uu____16167 =
                let uu____16168 =
                  let uu____16175 =
                    let uu____16176 =
                      let uu____16177 =
                        let uu____16186 =
                          FStar_Parser_AST.mkApp rel1
                            [(xt, FStar_Parser_AST.Nothing);
                            (yt, FStar_Parser_AST.Nothing)]
                            rel1.FStar_Parser_AST.range
                           in
                        let uu____16199 =
                          let uu____16200 =
                            let uu____16201 = FStar_Ident.lid_of_str "Type0"
                               in
                            FStar_Parser_AST.Name uu____16201  in
                          FStar_Parser_AST.mk_term uu____16200
                            rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                           in
                        (uu____16186, uu____16199,
                          FStar_Pervasives_Native.None)
                         in
                      FStar_Parser_AST.Ascribed uu____16177  in
                    FStar_Parser_AST.mk_term uu____16176
                      rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr
                     in
                  (pats, uu____16175)  in
                FStar_Parser_AST.Abs uu____16168  in
              FStar_Parser_AST.mk_term uu____16167
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
              let uu____16222 = FStar_List.last steps  in
              match uu____16222 with
              | FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep
                  (uu____16225,uu____16226,last_expr)) -> last_expr
              | uu____16228 -> failwith "impossible: no last_expr on calc"
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
            let uu____16256 =
              FStar_List.fold_left
                (fun uu____16274  ->
                   fun uu____16275  ->
                     match (uu____16274, uu____16275) with
                     | ((e1,prev),FStar_Parser_AST.CalcStep
                        (rel2,just,next_expr)) ->
                         let just1 =
                           let uu____16298 = is_impl rel2  in
                           if uu____16298
                           then
                             let uu____16301 =
                               let uu____16308 =
                                 let uu____16313 =
                                   FStar_Parser_AST.thunk just  in
                                 (uu____16313, FStar_Parser_AST.Nothing)  in
                               [uu____16308]  in
                             FStar_Parser_AST.mkApp
                               (push_impl just.FStar_Parser_AST.range)
                               uu____16301 just.FStar_Parser_AST.range
                           else just  in
                         let pf =
                           let uu____16325 =
                             let uu____16332 =
                               let uu____16339 =
                                 let uu____16346 =
                                   let uu____16353 =
                                     let uu____16358 = eta_and_annot rel2  in
                                     (uu____16358, FStar_Parser_AST.Nothing)
                                      in
                                   let uu____16359 =
                                     let uu____16366 =
                                       let uu____16373 =
                                         let uu____16378 =
                                           FStar_Parser_AST.thunk e1  in
                                         (uu____16378,
                                           FStar_Parser_AST.Nothing)
                                          in
                                       let uu____16379 =
                                         let uu____16386 =
                                           let uu____16391 =
                                             FStar_Parser_AST.thunk just1  in
                                           (uu____16391,
                                             FStar_Parser_AST.Nothing)
                                            in
                                         [uu____16386]  in
                                       uu____16373 :: uu____16379  in
                                     (next_expr, FStar_Parser_AST.Nothing) ::
                                       uu____16366
                                      in
                                   uu____16353 :: uu____16359  in
                                 (prev, FStar_Parser_AST.Hash) :: uu____16346
                                  in
                               (init_expr, FStar_Parser_AST.Hash) ::
                                 uu____16339
                                in
                             ((wild rel2.FStar_Parser_AST.range),
                               FStar_Parser_AST.Hash) :: uu____16332
                              in
                           FStar_Parser_AST.mkApp
                             (step rel2.FStar_Parser_AST.range) uu____16325
                             FStar_Range.dummyRange
                            in
                         (pf, next_expr)) (e, init_expr) steps
               in
            (match uu____16256 with
             | (e1,uu____16429) ->
                 let e2 =
                   let uu____16431 =
                     let uu____16438 =
                       let uu____16445 =
                         let uu____16452 =
                           let uu____16457 = FStar_Parser_AST.thunk e1  in
                           (uu____16457, FStar_Parser_AST.Nothing)  in
                         [uu____16452]  in
                       (last_expr, FStar_Parser_AST.Hash) :: uu____16445  in
                     (init_expr, FStar_Parser_AST.Hash) :: uu____16438  in
                   FStar_Parser_AST.mkApp finish1 uu____16431
                     FStar_Range.dummyRange
                    in
                 desugar_term_maybe_top top_level env e2)
        | uu____16474 when
            top.FStar_Parser_AST.level = FStar_Parser_AST.Formula ->
            let uu____16475 = desugar_formula env top  in
            (uu____16475, noaqs)
        | uu____16476 ->
            let uu____16477 =
              let uu____16483 =
                let uu____16485 = FStar_Parser_AST.term_to_string top  in
                Prims.op_Hat "Unexpected term: " uu____16485  in
              (FStar_Errors.Fatal_UnexpectedTerm, uu____16483)  in
            FStar_Errors.raise_error uu____16477 top.FStar_Parser_AST.range

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
           (fun uu____16529  ->
              match uu____16529 with
              | (a,imp) ->
                  let uu____16542 = desugar_term env a  in
                  arg_withimp_e imp uu____16542))

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
          let is_requires uu____16579 =
            match uu____16579 with
            | (t1,uu____16586) ->
                let uu____16587 =
                  let uu____16588 = unparen t1  in
                  uu____16588.FStar_Parser_AST.tm  in
                (match uu____16587 with
                 | FStar_Parser_AST.Requires uu____16590 -> true
                 | uu____16599 -> false)
             in
          let is_ensures uu____16611 =
            match uu____16611 with
            | (t1,uu____16618) ->
                let uu____16619 =
                  let uu____16620 = unparen t1  in
                  uu____16620.FStar_Parser_AST.tm  in
                (match uu____16619 with
                 | FStar_Parser_AST.Ensures uu____16622 -> true
                 | uu____16631 -> false)
             in
          let is_app head1 uu____16649 =
            match uu____16649 with
            | (t1,uu____16657) ->
                let uu____16658 =
                  let uu____16659 = unparen t1  in
                  uu____16659.FStar_Parser_AST.tm  in
                (match uu____16658 with
                 | FStar_Parser_AST.App
                     ({ FStar_Parser_AST.tm = FStar_Parser_AST.Var d;
                        FStar_Parser_AST.range = uu____16662;
                        FStar_Parser_AST.level = uu____16663;_},uu____16664,uu____16665)
                     -> (d.FStar_Ident.ident).FStar_Ident.idText = head1
                 | uu____16667 -> false)
             in
          let is_smt_pat uu____16679 =
            match uu____16679 with
            | (t1,uu____16686) ->
                let uu____16687 =
                  let uu____16688 = unparen t1  in
                  uu____16688.FStar_Parser_AST.tm  in
                (match uu____16687 with
                 | FStar_Parser_AST.Construct
                     (cons1,({
                               FStar_Parser_AST.tm =
                                 FStar_Parser_AST.Construct
                                 (smtpat,uu____16692);
                               FStar_Parser_AST.range = uu____16693;
                               FStar_Parser_AST.level = uu____16694;_},uu____16695)::uu____16696::[])
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
                               FStar_Parser_AST.range = uu____16745;
                               FStar_Parser_AST.level = uu____16746;_},uu____16747)::uu____16748::[])
                     ->
                     (FStar_Ident.lid_equals cons1
                        FStar_Parser_Const.cons_lid)
                       &&
                       (FStar_Util.for_some
                          (fun s  -> smtpat.FStar_Ident.str = s)
                          ["smt_pat"; "smt_pat_or"])
                 | uu____16781 -> false)
             in
          let is_decreases = is_app "decreases"  in
          let pre_process_comp_typ t1 =
            let uu____16816 = head_and_args t1  in
            match uu____16816 with
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
                     let thunk_ens uu____16909 =
                       match uu____16909 with
                       | (e,i) ->
                           let uu____16920 = FStar_Parser_AST.thunk e  in
                           (uu____16920, i)
                        in
                     let fail_lemma uu____16932 =
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
                           let uu____17038 =
                             let uu____17045 =
                               let uu____17052 = thunk_ens ens  in
                               [uu____17052; nil_pat]  in
                             req_true :: uu____17045  in
                           unit_tm :: uu____17038
                       | req::ens::[] when
                           (is_requires req) && (is_ensures ens) ->
                           let uu____17099 =
                             let uu____17106 =
                               let uu____17113 = thunk_ens ens  in
                               [uu____17113; nil_pat]  in
                             req :: uu____17106  in
                           unit_tm :: uu____17099
                       | ens::smtpat::[] when
                           (((let uu____17162 = is_requires ens  in
                              Prims.op_Negation uu____17162) &&
                               (let uu____17165 = is_smt_pat ens  in
                                Prims.op_Negation uu____17165))
                              &&
                              (let uu____17168 = is_decreases ens  in
                               Prims.op_Negation uu____17168))
                             && (is_smt_pat smtpat)
                           ->
                           let uu____17170 =
                             let uu____17177 =
                               let uu____17184 = thunk_ens ens  in
                               [uu____17184; smtpat]  in
                             req_true :: uu____17177  in
                           unit_tm :: uu____17170
                       | ens::dec::[] when
                           (is_ensures ens) && (is_decreases dec) ->
                           let uu____17231 =
                             let uu____17238 =
                               let uu____17245 = thunk_ens ens  in
                               [uu____17245; nil_pat; dec]  in
                             req_true :: uu____17238  in
                           unit_tm :: uu____17231
                       | ens::dec::smtpat::[] when
                           ((is_ensures ens) && (is_decreases dec)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17305 =
                             let uu____17312 =
                               let uu____17319 = thunk_ens ens  in
                               [uu____17319; smtpat; dec]  in
                             req_true :: uu____17312  in
                           unit_tm :: uu____17305
                       | req::ens::dec::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_decreases dec)
                           ->
                           let uu____17379 =
                             let uu____17386 =
                               let uu____17393 = thunk_ens ens  in
                               [uu____17393; nil_pat; dec]  in
                             req :: uu____17386  in
                           unit_tm :: uu____17379
                       | req::ens::smtpat::[] when
                           ((is_requires req) && (is_ensures ens)) &&
                             (is_smt_pat smtpat)
                           ->
                           let uu____17453 =
                             let uu____17460 =
                               let uu____17467 = thunk_ens ens  in
                               [uu____17467; smtpat]  in
                             req :: uu____17460  in
                           unit_tm :: uu____17453
                       | req::ens::dec::smtpat::[] when
                           (((is_requires req) && (is_ensures ens)) &&
                              (is_smt_pat smtpat))
                             && (is_decreases dec)
                           ->
                           let uu____17532 =
                             let uu____17539 =
                               let uu____17546 = thunk_ens ens  in
                               [uu____17546; dec; smtpat]  in
                             req :: uu____17539  in
                           unit_tm :: uu____17532
                       | _other -> fail_lemma ()  in
                     let head_and_attributes =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) lemma
                        in
                     (head_and_attributes, args1)
                 | FStar_Parser_AST.Name l when
                     FStar_Syntax_DsEnv.is_effect_name env l ->
                     let uu____17608 =
                       FStar_Syntax_DsEnv.fail_or env
                         (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes
                            env) l
                        in
                     (uu____17608, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17636 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17636
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "Tot")
                     ->
                     let uu____17639 =
                       let uu____17646 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17646, [])  in
                     (uu____17639, args)
                 | FStar_Parser_AST.Name l when
                     (let uu____17664 = FStar_Syntax_DsEnv.current_module env
                         in
                      FStar_Ident.lid_equals uu____17664
                        FStar_Parser_Const.prims_lid)
                       && ((l.FStar_Ident.ident).FStar_Ident.idText = "GTot")
                     ->
                     let uu____17667 =
                       let uu____17674 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_GTot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17674, [])  in
                     (uu____17667, args)
                 | FStar_Parser_AST.Name l when
                     (((l.FStar_Ident.ident).FStar_Ident.idText = "Type") ||
                        ((l.FStar_Ident.ident).FStar_Ident.idText = "Type0"))
                       ||
                       ((l.FStar_Ident.ident).FStar_Ident.idText = "Effect")
                     ->
                     let uu____17696 =
                       let uu____17703 =
                         FStar_Ident.set_lid_range
                           FStar_Parser_Const.effect_Tot_lid
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17703, [])  in
                     (uu____17696, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17726 when allow_type_promotion ->
                     let default_effect =
                       let uu____17728 = FStar_Options.ml_ish ()  in
                       if uu____17728
                       then FStar_Parser_Const.effect_ML_lid
                       else
                         ((let uu____17734 =
                             FStar_Options.warn_default_effects ()  in
                           if uu____17734
                           then
                             FStar_Errors.log_issue
                               head1.FStar_Parser_AST.range
                               (FStar_Errors.Warning_UseDefaultEffect,
                                 "Using default effect Tot")
                           else ());
                          FStar_Parser_Const.effect_Tot_lid)
                        in
                     let uu____17741 =
                       let uu____17748 =
                         FStar_Ident.set_lid_range default_effect
                           head1.FStar_Parser_AST.range
                          in
                       (uu____17748, [])  in
                     (uu____17741, [(t1, FStar_Parser_AST.Nothing)])
                 | uu____17771 ->
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_EffectNotFound,
                         "Expected an effect constructor")
                       t1.FStar_Parser_AST.range)
             in
          let uu____17790 = pre_process_comp_typ t  in
          match uu____17790 with
          | ((eff,cattributes),args) ->
              (if (FStar_List.length args) = Prims.int_zero
               then
                 (let uu____17842 =
                    let uu____17848 =
                      let uu____17850 = FStar_Syntax_Print.lid_to_string eff
                         in
                      FStar_Util.format1 "Not enough args to effect %s"
                        uu____17850
                       in
                    (FStar_Errors.Fatal_NotEnoughArgsToEffect, uu____17848)
                     in
                  fail1 uu____17842)
               else ();
               (let is_universe uu____17866 =
                  match uu____17866 with
                  | (uu____17872,imp) -> imp = FStar_Parser_AST.UnivApp  in
                let uu____17874 = FStar_Util.take is_universe args  in
                match uu____17874 with
                | (universes,args1) ->
                    let universes1 =
                      FStar_List.map
                        (fun uu____17933  ->
                           match uu____17933 with
                           | (u,imp) -> desugar_universe u) universes
                       in
                    let uu____17940 =
                      let uu____17955 = FStar_List.hd args1  in
                      let uu____17964 = FStar_List.tl args1  in
                      (uu____17955, uu____17964)  in
                    (match uu____17940 with
                     | (result_arg,rest) ->
                         let result_typ =
                           desugar_typ env
                             (FStar_Pervasives_Native.fst result_arg)
                            in
                         let rest1 = desugar_args env rest  in
                         let uu____18019 =
                           let is_decrease uu____18058 =
                             match uu____18058 with
                             | (t1,uu____18069) ->
                                 (match t1.FStar_Syntax_Syntax.n with
                                  | FStar_Syntax_Syntax.Tm_app
                                      ({
                                         FStar_Syntax_Syntax.n =
                                           FStar_Syntax_Syntax.Tm_fvar fv;
                                         FStar_Syntax_Syntax.pos =
                                           uu____18080;
                                         FStar_Syntax_Syntax.vars =
                                           uu____18081;_},uu____18082::[])
                                      ->
                                      FStar_Syntax_Syntax.fv_eq_lid fv
                                        FStar_Parser_Const.decreases_lid
                                  | uu____18121 -> false)
                              in
                           FStar_All.pipe_right rest1
                             (FStar_List.partition is_decrease)
                            in
                         (match uu____18019 with
                          | (dec,rest2) ->
                              let decreases_clause =
                                FStar_All.pipe_right dec
                                  (FStar_List.map
                                     (fun uu____18238  ->
                                        match uu____18238 with
                                        | (t1,uu____18248) ->
                                            (match t1.FStar_Syntax_Syntax.n
                                             with
                                             | FStar_Syntax_Syntax.Tm_app
                                                 (uu____18257,(arg,uu____18259)::[])
                                                 ->
                                                 FStar_Syntax_Syntax.DECREASES
                                                   arg
                                             | uu____18298 ->
                                                 failwith "impos")))
                                 in
                              let no_additional_args =
                                let is_empty l =
                                  match l with
                                  | [] -> true
                                  | uu____18319 -> false  in
                                (((is_empty decreases_clause) &&
                                    (is_empty rest2))
                                   && (is_empty cattributes))
                                  && (is_empty universes1)
                                 in
                              let uu____18331 =
                                no_additional_args &&
                                  (FStar_Ident.lid_equals eff
                                     FStar_Parser_Const.effect_Tot_lid)
                                 in
                              if uu____18331
                              then FStar_Syntax_Syntax.mk_Total result_typ
                              else
                                (let uu____18338 =
                                   no_additional_args &&
                                     (FStar_Ident.lid_equals eff
                                        FStar_Parser_Const.effect_GTot_lid)
                                    in
                                 if uu____18338
                                 then
                                   FStar_Syntax_Syntax.mk_GTotal result_typ
                                 else
                                   (let flags =
                                      let uu____18348 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18348
                                      then [FStar_Syntax_Syntax.LEMMA]
                                      else
                                        (let uu____18355 =
                                           FStar_Ident.lid_equals eff
                                             FStar_Parser_Const.effect_Tot_lid
                                            in
                                         if uu____18355
                                         then [FStar_Syntax_Syntax.TOTAL]
                                         else
                                           (let uu____18362 =
                                              FStar_Ident.lid_equals eff
                                                FStar_Parser_Const.effect_ML_lid
                                               in
                                            if uu____18362
                                            then
                                              [FStar_Syntax_Syntax.MLEFFECT]
                                            else
                                              (let uu____18369 =
                                                 FStar_Ident.lid_equals eff
                                                   FStar_Parser_Const.effect_GTot_lid
                                                  in
                                               if uu____18369
                                               then
                                                 [FStar_Syntax_Syntax.SOMETRIVIAL]
                                               else [])))
                                       in
                                    let flags1 =
                                      FStar_List.append flags cattributes  in
                                    let rest3 =
                                      let uu____18390 =
                                        FStar_Ident.lid_equals eff
                                          FStar_Parser_Const.effect_Lemma_lid
                                         in
                                      if uu____18390
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
                                                    let uu____18481 =
                                                      FStar_Ident.set_lid_range
                                                        FStar_Parser_Const.pattern_lid
                                                        pat.FStar_Syntax_Syntax.pos
                                                       in
                                                    FStar_Syntax_Syntax.fvar
                                                      uu____18481
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
                                              | uu____18502 -> pat  in
                                            let uu____18503 =
                                              let uu____18514 =
                                                let uu____18525 =
                                                  let uu____18534 =
                                                    FStar_Syntax_Syntax.mk
                                                      (FStar_Syntax_Syntax.Tm_meta
                                                         (pat1,
                                                           (FStar_Syntax_Syntax.Meta_desugared
                                                              FStar_Syntax_Syntax.Meta_smt_pat)))
                                                      FStar_Pervasives_Native.None
                                                      pat1.FStar_Syntax_Syntax.pos
                                                     in
                                                  (uu____18534, aq)  in
                                                [uu____18525]  in
                                              ens :: uu____18514  in
                                            req :: uu____18503
                                        | uu____18575 -> rest2
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
        let uu___2443_18610 = t  in
        {
          FStar_Syntax_Syntax.n = (uu___2443_18610.FStar_Syntax_Syntax.n);
          FStar_Syntax_Syntax.pos = (f.FStar_Parser_AST.range);
          FStar_Syntax_Syntax.vars =
            (uu___2443_18610.FStar_Syntax_Syntax.vars)
        }  in
      let desugar_quant q b pats body =
        let tk =
          desugar_binder env
            (let uu___2450_18664 = b  in
             {
               FStar_Parser_AST.b = (uu___2450_18664.FStar_Parser_AST.b);
               FStar_Parser_AST.brange =
                 (uu___2450_18664.FStar_Parser_AST.brange);
               FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
               FStar_Parser_AST.aqual =
                 (uu___2450_18664.FStar_Parser_AST.aqual)
             })
           in
        let with_pats env1 uu____18693 body1 =
          match uu____18693 with
          | (names1,pats1) ->
              (match (names1, pats1) with
               | ([],[]) -> body1
               | ([],uu____18739::uu____18740) ->
                   failwith
                     "Impossible: Annotated pattern without binders in scope"
               | uu____18758 ->
                   let names2 =
                     FStar_All.pipe_right names1
                       (FStar_List.map
                          (fun i  ->
                             let uu___2469_18785 =
                               FStar_Syntax_DsEnv.fail_or2
                                 (FStar_Syntax_DsEnv.try_lookup_id env1) i
                                in
                             {
                               FStar_Syntax_Syntax.n =
                                 (uu___2469_18785.FStar_Syntax_Syntax.n);
                               FStar_Syntax_Syntax.pos =
                                 (i.FStar_Ident.idRange);
                               FStar_Syntax_Syntax.vars =
                                 (uu___2469_18785.FStar_Syntax_Syntax.vars)
                             }))
                      in
                   let pats2 =
                     FStar_All.pipe_right pats1
                       (FStar_List.map
                          (fun es  ->
                             FStar_All.pipe_right es
                               (FStar_List.map
                                  (fun e  ->
                                     let uu____18848 = desugar_term env1 e
                                        in
                                     FStar_All.pipe_left
                                       (arg_withimp_t
                                          FStar_Parser_AST.Nothing)
                                       uu____18848))))
                      in
                   mk1
                     (FStar_Syntax_Syntax.Tm_meta
                        (body1,
                          (FStar_Syntax_Syntax.Meta_pattern (names2, pats2)))))
           in
        match tk with
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____18879 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____18879 with
             | (env1,a1) ->
                 let a2 =
                   let uu___2482_18889 = a1  in
                   {
                     FStar_Syntax_Syntax.ppname =
                       (uu___2482_18889.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (uu___2482_18889.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = k
                   }  in
                 let body1 = desugar_formula env1 body  in
                 let body2 = with_pats env1 pats body1  in
                 let body3 =
                   let uu____18895 =
                     let uu____18898 =
                       let uu____18899 = FStar_Syntax_Syntax.mk_binder a2  in
                       [uu____18899]  in
                     no_annot_abs uu____18898 body2  in
                   FStar_All.pipe_left setpos uu____18895  in
                 let uu____18920 =
                   let uu____18921 =
                     let uu____18938 =
                       let uu____18941 =
                         FStar_Ident.set_lid_range q
                           b.FStar_Parser_AST.brange
                          in
                       FStar_Syntax_Syntax.fvar uu____18941
                         (FStar_Syntax_Syntax.Delta_constant_at_level
                            Prims.int_one) FStar_Pervasives_Native.None
                        in
                     let uu____18943 =
                       let uu____18954 = FStar_Syntax_Syntax.as_arg body3  in
                       [uu____18954]  in
                     (uu____18938, uu____18943)  in
                   FStar_Syntax_Syntax.Tm_app uu____18921  in
                 FStar_All.pipe_left mk1 uu____18920)
        | uu____18993 -> failwith "impossible"  in
      let push_quant q binders pats body =
        match binders with
        | b::b'::_rest ->
            let rest = b' :: _rest  in
            let body1 =
              let uu____19058 = q (rest, pats, body)  in
              let uu____19061 =
                FStar_Range.union_ranges b'.FStar_Parser_AST.brange
                  body.FStar_Parser_AST.range
                 in
              FStar_Parser_AST.mk_term uu____19058 uu____19061
                FStar_Parser_AST.Formula
               in
            let uu____19062 = q ([b], ([], []), body1)  in
            FStar_Parser_AST.mk_term uu____19062 f.FStar_Parser_AST.range
              FStar_Parser_AST.Formula
        | uu____19073 -> failwith "impossible"  in
      let uu____19077 =
        let uu____19078 = unparen f  in uu____19078.FStar_Parser_AST.tm  in
      match uu____19077 with
      | FStar_Parser_AST.Labeled (f1,l,p) ->
          let f2 = desugar_formula env f1  in
          FStar_All.pipe_left mk1
            (FStar_Syntax_Syntax.Tm_meta
               (f2,
                 (FStar_Syntax_Syntax.Meta_labeled
                    (l, (f2.FStar_Syntax_Syntax.pos), p))))
      | FStar_Parser_AST.QForall ([],uu____19091,uu____19092) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QExists ([],uu____19116,uu____19117) ->
          failwith "Impossible: Quantifier without binders"
      | FStar_Parser_AST.QForall (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19173 =
            push_quant (fun x  -> FStar_Parser_AST.QForall x) binders pats
              body
             in
          desugar_formula env uu____19173
      | FStar_Parser_AST.QExists (_1::_2::_3,pats,body) ->
          let binders = _1 :: _2 :: _3  in
          let uu____19217 =
            push_quant (fun x  -> FStar_Parser_AST.QExists x) binders pats
              body
             in
          desugar_formula env uu____19217
      | FStar_Parser_AST.QForall (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.forall_lid b pats body
      | FStar_Parser_AST.QExists (b::[],pats,body) ->
          desugar_quant FStar_Parser_Const.exists_lid b pats body
      | FStar_Parser_AST.Paren f1 -> failwith "impossible"
      | uu____19281 -> desugar_term env f

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
          let uu____19292 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19292)
      | FStar_Parser_AST.Annotated (x,t) ->
          let uu____19297 = desugar_typ env t  in
          ((FStar_Pervasives_Native.Some x), uu____19297)
      | FStar_Parser_AST.TVariable x ->
          let uu____19301 =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_type FStar_Syntax_Syntax.U_unknown)
              FStar_Pervasives_Native.None x.FStar_Ident.idRange
             in
          ((FStar_Pervasives_Native.Some x), uu____19301)
      | FStar_Parser_AST.NoName t ->
          let uu____19305 = desugar_typ env t  in
          (FStar_Pervasives_Native.None, uu____19305)
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
      fun uu___11_19313  ->
        match uu___11_19313 with
        | (FStar_Pervasives_Native.None ,k) ->
            let uu____19335 = FStar_Syntax_Syntax.null_binder k  in
            (uu____19335, env)
        | (FStar_Pervasives_Native.Some a,k) ->
            let uu____19352 = FStar_Syntax_DsEnv.push_bv env a  in
            (match uu____19352 with
             | (env1,a1) ->
                 let uu____19369 =
                   let uu____19376 = trans_aqual env1 imp  in
                   ((let uu___2582_19382 = a1  in
                     {
                       FStar_Syntax_Syntax.ppname =
                         (uu___2582_19382.FStar_Syntax_Syntax.ppname);
                       FStar_Syntax_Syntax.index =
                         (uu___2582_19382.FStar_Syntax_Syntax.index);
                       FStar_Syntax_Syntax.sort = k
                     }), uu____19376)
                    in
                 (uu____19369, env1))

and (trans_aqual :
  env_t ->
    FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.aqual)
  =
  fun env  ->
    fun uu___12_19390  ->
      match uu___12_19390 with
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality ) ->
          FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Equality
      | FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta t) ->
          let uu____19394 =
            let uu____19395 = desugar_term env t  in
            FStar_Syntax_Syntax.Meta uu____19395  in
          FStar_Pervasives_Native.Some uu____19394
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None

let (typars_of_binders :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.binder Prims.list ->
      (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv *
        FStar_Syntax_Syntax.aqual) Prims.list))
  =
  fun env  ->
    fun bs  ->
      let uu____19423 =
        FStar_List.fold_left
          (fun uu____19456  ->
             fun b  ->
               match uu____19456 with
               | (env1,out) ->
                   let tk =
                     desugar_binder env1
                       (let uu___2600_19500 = b  in
                        {
                          FStar_Parser_AST.b =
                            (uu___2600_19500.FStar_Parser_AST.b);
                          FStar_Parser_AST.brange =
                            (uu___2600_19500.FStar_Parser_AST.brange);
                          FStar_Parser_AST.blevel = FStar_Parser_AST.Formula;
                          FStar_Parser_AST.aqual =
                            (uu___2600_19500.FStar_Parser_AST.aqual)
                        })
                      in
                   (match tk with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____19515 = FStar_Syntax_DsEnv.push_bv env1 a
                           in
                        (match uu____19515 with
                         | (env2,a1) ->
                             let a2 =
                               let uu___2610_19533 = a1  in
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (uu___2610_19533.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (uu___2610_19533.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = k
                               }  in
                             let uu____19534 =
                               let uu____19541 =
                                 let uu____19546 =
                                   trans_aqual env2 b.FStar_Parser_AST.aqual
                                    in
                                 (a2, uu____19546)  in
                               uu____19541 :: out  in
                             (env2, uu____19534))
                    | uu____19557 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_UnexpectedBinder,
                            "Unexpected binder") b.FStar_Parser_AST.brange))
          (env, []) bs
         in
      match uu____19423 with | (env1,tpars) -> (env1, (FStar_List.rev tpars))
  
let (desugar_attributes :
  env_t ->
    FStar_Parser_AST.term Prims.list -> FStar_Syntax_Syntax.cflag Prims.list)
  =
  fun env  ->
    fun cattributes  ->
      let desugar_attribute t =
        let uu____19645 =
          let uu____19646 = unparen t  in uu____19646.FStar_Parser_AST.tm  in
        match uu____19645 with
        | FStar_Parser_AST.Var
            { FStar_Ident.ns = uu____19647; FStar_Ident.ident = uu____19648;
              FStar_Ident.nsstr = uu____19649; FStar_Ident.str = "cps";_}
            -> FStar_Syntax_Syntax.CPS
        | uu____19654 ->
            let uu____19655 =
              let uu____19661 =
                let uu____19663 = FStar_Parser_AST.term_to_string t  in
                Prims.op_Hat "Unknown attribute " uu____19663  in
              (FStar_Errors.Fatal_UnknownAttribute, uu____19661)  in
            FStar_Errors.raise_error uu____19655 t.FStar_Parser_AST.range
         in
      FStar_List.map desugar_attribute cattributes
  
let (binder_ident :
  FStar_Parser_AST.binder -> FStar_Ident.ident FStar_Pervasives_Native.option)
  =
  fun b  ->
    match b.FStar_Parser_AST.b with
    | FStar_Parser_AST.TAnnotated (x,uu____19680) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Annotated (x,uu____19682) ->
        FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.TVariable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.Variable x -> FStar_Pervasives_Native.Some x
    | FStar_Parser_AST.NoName uu____19685 -> FStar_Pervasives_Native.None
  
let (binder_idents :
  FStar_Parser_AST.binder Prims.list -> FStar_Ident.ident Prims.list) =
  fun bs  ->
    FStar_List.collect
      (fun b  ->
         let uu____19703 = binder_ident b  in
         FStar_Common.list_of_option uu____19703) bs
  
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
               (fun uu___13_19740  ->
                  match uu___13_19740 with
                  | FStar_Syntax_Syntax.NoExtract  -> true
                  | FStar_Syntax_Syntax.Abstract  -> true
                  | FStar_Syntax_Syntax.Private  -> true
                  | uu____19745 -> false))
           in
        let quals2 q =
          let uu____19759 =
            (let uu____19763 = FStar_Syntax_DsEnv.iface env  in
             Prims.op_Negation uu____19763) ||
              (FStar_Syntax_DsEnv.admitted_iface env)
             in
          if uu____19759
          then FStar_List.append (FStar_Syntax_Syntax.Assumption :: q) quals1
          else FStar_List.append q quals1  in
        FStar_All.pipe_right datas
          (FStar_List.map
             (fun d  ->
                let disc_name = FStar_Syntax_Util.mk_discriminator d  in
                let uu____19780 = FStar_Ident.range_of_lid disc_name  in
                let uu____19781 =
                  quals2
                    [FStar_Syntax_Syntax.OnlyName;
                    FStar_Syntax_Syntax.Discriminator d]
                   in
                {
                  FStar_Syntax_Syntax.sigel =
                    (FStar_Syntax_Syntax.Sig_declare_typ
                       (disc_name, [], FStar_Syntax_Syntax.tun));
                  FStar_Syntax_Syntax.sigrng = uu____19780;
                  FStar_Syntax_Syntax.sigquals = uu____19781;
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
            let uu____19821 =
              FStar_All.pipe_right fields
                (FStar_List.mapi
                   (fun i  ->
                      fun uu____19859  ->
                        match uu____19859 with
                        | (x,uu____19870) ->
                            let uu____19875 =
                              FStar_Syntax_Util.mk_field_projector_name lid x
                                i
                               in
                            (match uu____19875 with
                             | (field_name,uu____19883) ->
                                 let only_decl =
                                   ((let uu____19888 =
                                       FStar_Syntax_DsEnv.current_module env
                                        in
                                     FStar_Ident.lid_equals
                                       FStar_Parser_Const.prims_lid
                                       uu____19888)
                                      ||
                                      (fvq <> FStar_Syntax_Syntax.Data_ctor))
                                     ||
                                     (let uu____19890 =
                                        let uu____19892 =
                                          FStar_Syntax_DsEnv.current_module
                                            env
                                           in
                                        uu____19892.FStar_Ident.str  in
                                      FStar_Options.dont_gen_projectors
                                        uu____19890)
                                    in
                                 let no_decl =
                                   FStar_Syntax_Syntax.is_type
                                     x.FStar_Syntax_Syntax.sort
                                    in
                                 let quals q =
                                   if only_decl
                                   then
                                     let uu____19910 =
                                       FStar_List.filter
                                         (fun uu___14_19914  ->
                                            match uu___14_19914 with
                                            | FStar_Syntax_Syntax.Abstract 
                                                -> false
                                            | uu____19917 -> true) q
                                        in
                                     FStar_Syntax_Syntax.Assumption ::
                                       uu____19910
                                   else q  in
                                 let quals1 =
                                   let iquals1 =
                                     FStar_All.pipe_right iquals
                                       (FStar_List.filter
                                          (fun uu___15_19932  ->
                                             match uu___15_19932 with
                                             | FStar_Syntax_Syntax.NoExtract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Abstract 
                                                 -> true
                                             | FStar_Syntax_Syntax.Private 
                                                 -> true
                                             | uu____19937 -> false))
                                      in
                                   quals (FStar_Syntax_Syntax.OnlyName ::
                                     (FStar_Syntax_Syntax.Projector
                                        (lid, (x.FStar_Syntax_Syntax.ppname)))
                                     :: iquals1)
                                    in
                                 let decl =
                                   let uu____19940 =
                                     FStar_Ident.range_of_lid field_name  in
                                   {
                                     FStar_Syntax_Syntax.sigel =
                                       (FStar_Syntax_Syntax.Sig_declare_typ
                                          (field_name, [],
                                            FStar_Syntax_Syntax.tun));
                                     FStar_Syntax_Syntax.sigrng = uu____19940;
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
                                      let uu____19947 =
                                        FStar_All.pipe_right quals1
                                          (FStar_List.contains
                                             FStar_Syntax_Syntax.Abstract)
                                         in
                                      if uu____19947
                                      then
                                        FStar_Syntax_Syntax.Delta_abstract
                                          (FStar_Syntax_Syntax.Delta_equational_at_level
                                             Prims.int_one)
                                      else
                                        FStar_Syntax_Syntax.Delta_equational_at_level
                                          Prims.int_one
                                       in
                                    let lb =
                                      let uu____19958 =
                                        let uu____19963 =
                                          FStar_Syntax_Syntax.lid_as_fv
                                            field_name dd
                                            FStar_Pervasives_Native.None
                                           in
                                        FStar_Util.Inr uu____19963  in
                                      {
                                        FStar_Syntax_Syntax.lbname =
                                          uu____19958;
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
                                      let uu____19967 =
                                        let uu____19968 =
                                          let uu____19975 =
                                            let uu____19978 =
                                              let uu____19979 =
                                                FStar_All.pipe_right
                                                  lb.FStar_Syntax_Syntax.lbname
                                                  FStar_Util.right
                                                 in
                                              FStar_All.pipe_right
                                                uu____19979
                                                (fun fv  ->
                                                   (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v)
                                               in
                                            [uu____19978]  in
                                          ((false, [lb]), uu____19975)  in
                                        FStar_Syntax_Syntax.Sig_let
                                          uu____19968
                                         in
                                      {
                                        FStar_Syntax_Syntax.sigel =
                                          uu____19967;
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
            FStar_All.pipe_right uu____19821 FStar_List.flatten
  
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
            (lid,uu____20028,t,uu____20030,n1,uu____20032) when
            let uu____20039 =
              FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid  in
            Prims.op_Negation uu____20039 ->
            let uu____20041 = FStar_Syntax_Util.arrow_formals t  in
            (match uu____20041 with
             | (formals,uu____20059) ->
                 (match formals with
                  | [] -> []
                  | uu____20088 ->
                      let filter_records uu___16_20104 =
                        match uu___16_20104 with
                        | FStar_Syntax_Syntax.RecordConstructor
                            (uu____20107,fns) ->
                            FStar_Pervasives_Native.Some
                              (FStar_Syntax_Syntax.Record_ctor (lid, fns))
                        | uu____20119 -> FStar_Pervasives_Native.None  in
                      let fv_qual =
                        let uu____20121 =
                          FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals
                            filter_records
                           in
                        match uu____20121 with
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
                      let uu____20133 = FStar_Util.first_N n1 formals  in
                      (match uu____20133 with
                       | (uu____20162,rest) ->
                           mk_indexed_projector_names iquals1 fv_qual env lid
                             rest)))
        | uu____20196 -> []
  
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
                        let uu____20290 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env lid
                           in
                        FStar_All.pipe_right uu____20290
                          FStar_Pervasives_Native.snd
                         in
                      let dd =
                        let uu____20314 =
                          FStar_All.pipe_right quals
                            (FStar_List.contains FStar_Syntax_Syntax.Abstract)
                           in
                        if uu____20314
                        then
                          let uu____20320 =
                            FStar_Syntax_Util.incr_delta_qualifier t  in
                          FStar_Syntax_Syntax.Delta_abstract uu____20320
                        else FStar_Syntax_Util.incr_delta_qualifier t  in
                      let lb =
                        let uu____20324 =
                          let uu____20329 =
                            FStar_Syntax_Syntax.lid_as_fv lid dd
                              FStar_Pervasives_Native.None
                             in
                          FStar_Util.Inr uu____20329  in
                        let uu____20330 =
                          if FStar_Util.is_some kopt
                          then
                            let uu____20336 =
                              let uu____20339 =
                                FStar_All.pipe_right kopt FStar_Util.must  in
                              FStar_Syntax_Syntax.mk_Total uu____20339  in
                            FStar_Syntax_Util.arrow typars uu____20336
                          else FStar_Syntax_Syntax.tun  in
                        let uu____20344 = no_annot_abs typars t  in
                        {
                          FStar_Syntax_Syntax.lbname = uu____20324;
                          FStar_Syntax_Syntax.lbunivs = uvs;
                          FStar_Syntax_Syntax.lbtyp = uu____20330;
                          FStar_Syntax_Syntax.lbeff =
                            FStar_Parser_Const.effect_Tot_lid;
                          FStar_Syntax_Syntax.lbdef = uu____20344;
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
          let tycon_id uu___17_20398 =
            match uu___17_20398 with
            | FStar_Parser_AST.TyconAbstract (id1,uu____20400,uu____20401) ->
                id1
            | FStar_Parser_AST.TyconAbbrev
                (id1,uu____20411,uu____20412,uu____20413) -> id1
            | FStar_Parser_AST.TyconRecord
                (id1,uu____20423,uu____20424,uu____20425) -> id1
            | FStar_Parser_AST.TyconVariant
                (id1,uu____20447,uu____20448,uu____20449) -> id1
             in
          let binder_to_term1 b =
            match b.FStar_Parser_AST.b with
            | FStar_Parser_AST.Annotated (x,uu____20487) ->
                let uu____20488 =
                  let uu____20489 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20489  in
                FStar_Parser_AST.mk_term uu____20488 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.Variable x ->
                let uu____20491 =
                  let uu____20492 = FStar_Ident.lid_of_ids [x]  in
                  FStar_Parser_AST.Var uu____20492  in
                FStar_Parser_AST.mk_term uu____20491 x.FStar_Ident.idRange
                  FStar_Parser_AST.Expr
            | FStar_Parser_AST.TAnnotated (a,uu____20494) ->
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
              | uu____20525 -> FStar_Parser_AST.Nothing  in
            FStar_List.fold_left
              (fun out  ->
                 fun b  ->
                   let uu____20533 =
                     let uu____20534 =
                       let uu____20541 = binder_to_term1 b  in
                       (out, uu____20541, (imp_of_aqual b))  in
                     FStar_Parser_AST.App uu____20534  in
                   FStar_Parser_AST.mk_term uu____20533
                     out.FStar_Parser_AST.range out.FStar_Parser_AST.level) t
              binders
             in
          let tycon_record_as_variant uu___18_20553 =
            match uu___18_20553 with
            | FStar_Parser_AST.TyconRecord (id1,parms,kopt,fields) ->
                let constrName =
                  FStar_Ident.mk_ident
                    ((Prims.op_Hat "Mk" id1.FStar_Ident.idText),
                      (id1.FStar_Ident.idRange))
                   in
                let mfields =
                  FStar_List.map
                    (fun uu____20597  ->
                       match uu____20597 with
                       | (x,t) ->
                           FStar_Parser_AST.mk_binder
                             (FStar_Parser_AST.Annotated (x, t))
                             x.FStar_Ident.idRange FStar_Parser_AST.Expr
                             FStar_Pervasives_Native.None) fields
                   in
                let result =
                  let uu____20605 =
                    let uu____20606 =
                      let uu____20607 = FStar_Ident.lid_of_ids [id1]  in
                      FStar_Parser_AST.Var uu____20607  in
                    FStar_Parser_AST.mk_term uu____20606
                      id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                     in
                  apply_binders uu____20605 parms  in
                let constrTyp =
                  FStar_Parser_AST.mk_term
                    (FStar_Parser_AST.Product
                       (mfields, (with_constructor_effect result)))
                    id1.FStar_Ident.idRange FStar_Parser_AST.Type_level
                   in
                let names1 =
                  let uu____20614 = binder_idents parms  in id1 ::
                    uu____20614
                   in
                (FStar_List.iter
                   (fun uu____20627  ->
                      match uu____20627 with
                      | (f,uu____20633) ->
                          let uu____20634 =
                            FStar_Util.for_some
                              (fun i  -> FStar_Ident.ident_equals f i) names1
                             in
                          if uu____20634
                          then
                            let uu____20639 =
                              let uu____20645 =
                                let uu____20647 =
                                  FStar_Ident.string_of_ident f  in
                                FStar_Util.format1
                                  "Field %s shadows the record's name or a parameter of it, please rename it"
                                  uu____20647
                                 in
                              (FStar_Errors.Error_FieldShadow, uu____20645)
                               in
                            FStar_Errors.raise_error uu____20639
                              f.FStar_Ident.idRange
                          else ()) fields;
                 (let uu____20653 =
                    FStar_All.pipe_right fields
                      (FStar_List.map FStar_Pervasives_Native.fst)
                     in
                  ((FStar_Parser_AST.TyconVariant
                      (id1, parms, kopt,
                        [(constrName,
                           (FStar_Pervasives_Native.Some constrTyp), false)])),
                    uu____20653)))
            | uu____20707 -> failwith "impossible"  in
          let desugar_abstract_tc quals1 _env mutuals uu___19_20747 =
            match uu___19_20747 with
            | FStar_Parser_AST.TyconAbstract (id1,binders,kopt) ->
                let uu____20771 = typars_of_binders _env binders  in
                (match uu____20771 with
                 | (_env',typars) ->
                     let k =
                       match kopt with
                       | FStar_Pervasives_Native.None  ->
                           FStar_Syntax_Util.ktype
                       | FStar_Pervasives_Native.Some k ->
                           desugar_term _env' k
                        in
                     let tconstr =
                       let uu____20807 =
                         let uu____20808 =
                           let uu____20809 = FStar_Ident.lid_of_ids [id1]  in
                           FStar_Parser_AST.Var uu____20809  in
                         FStar_Parser_AST.mk_term uu____20808
                           id1.FStar_Ident.idRange
                           FStar_Parser_AST.Type_level
                          in
                       apply_binders uu____20807 binders  in
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
                     let uu____20818 =
                       FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1
                         FStar_Syntax_Syntax.delta_constant
                        in
                     (match uu____20818 with
                      | (_env1,uu____20835) ->
                          let uu____20842 =
                            FStar_Syntax_DsEnv.push_top_level_rec_binding
                              _env' id1 FStar_Syntax_Syntax.delta_constant
                             in
                          (match uu____20842 with
                           | (_env2,uu____20859) ->
                               (_env1, _env2, se, tconstr))))
            | uu____20866 -> failwith "Unexpected tycon"  in
          let push_tparams env1 bs =
            let uu____20909 =
              FStar_List.fold_left
                (fun uu____20943  ->
                   fun uu____20944  ->
                     match (uu____20943, uu____20944) with
                     | ((env2,tps),(x,imp)) ->
                         let uu____21013 =
                           FStar_Syntax_DsEnv.push_bv env2
                             x.FStar_Syntax_Syntax.ppname
                            in
                         (match uu____21013 with
                          | (env3,y) -> (env3, ((y, imp) :: tps))))
                (env1, []) bs
               in
            match uu____20909 with
            | (env2,bs1) -> (env2, (FStar_List.rev bs1))  in
          match tcs with
          | (FStar_Parser_AST.TyconAbstract (id1,bs,kopt))::[] ->
              let kopt1 =
                match kopt with
                | FStar_Pervasives_Native.None  ->
                    let uu____21104 = tm_type_z id1.FStar_Ident.idRange  in
                    FStar_Pervasives_Native.Some uu____21104
                | uu____21105 -> kopt  in
              let tc = FStar_Parser_AST.TyconAbstract (id1, bs, kopt1)  in
              let uu____21113 = desugar_abstract_tc quals env [] tc  in
              (match uu____21113 with
               | (uu____21126,uu____21127,se,uu____21129) ->
                   let se1 =
                     match se.FStar_Syntax_Syntax.sigel with
                     | FStar_Syntax_Syntax.Sig_inductive_typ
                         (l,uu____21132,typars,k,[],[]) ->
                         let quals1 = se.FStar_Syntax_Syntax.sigquals  in
                         let quals2 =
                           if
                             FStar_List.contains
                               FStar_Syntax_Syntax.Assumption quals1
                           then quals1
                           else
                             ((let uu____21151 =
                                 let uu____21153 = FStar_Options.ml_ish ()
                                    in
                                 Prims.op_Negation uu____21153  in
                               if uu____21151
                               then
                                 let uu____21156 =
                                   let uu____21162 =
                                     let uu____21164 =
                                       FStar_Syntax_Print.lid_to_string l  in
                                     FStar_Util.format1
                                       "Adding an implicit 'assume new' qualifier on %s"
                                       uu____21164
                                      in
                                   (FStar_Errors.Warning_AddImplicitAssumeNewQualifier,
                                     uu____21162)
                                    in
                                 FStar_Errors.log_issue
                                   se.FStar_Syntax_Syntax.sigrng uu____21156
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
                           | uu____21177 ->
                               let uu____21178 =
                                 let uu____21185 =
                                   let uu____21186 =
                                     let uu____21201 =
                                       FStar_Syntax_Syntax.mk_Total k  in
                                     (typars, uu____21201)  in
                                   FStar_Syntax_Syntax.Tm_arrow uu____21186
                                    in
                                 FStar_Syntax_Syntax.mk uu____21185  in
                               uu____21178 FStar_Pervasives_Native.None
                                 se.FStar_Syntax_Syntax.sigrng
                            in
                         let uu___2893_21214 = se  in
                         {
                           FStar_Syntax_Syntax.sigel =
                             (FStar_Syntax_Syntax.Sig_declare_typ (l, [], t));
                           FStar_Syntax_Syntax.sigrng =
                             (uu___2893_21214.FStar_Syntax_Syntax.sigrng);
                           FStar_Syntax_Syntax.sigquals = quals2;
                           FStar_Syntax_Syntax.sigmeta =
                             (uu___2893_21214.FStar_Syntax_Syntax.sigmeta);
                           FStar_Syntax_Syntax.sigattrs =
                             (uu___2893_21214.FStar_Syntax_Syntax.sigattrs);
                           FStar_Syntax_Syntax.sigopts =
                             (uu___2893_21214.FStar_Syntax_Syntax.sigopts)
                         }
                     | uu____21215 -> failwith "Impossible"  in
                   let env1 = FStar_Syntax_DsEnv.push_sigelt env se1  in
                   (env1, [se1]))
          | (FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t))::[] ->
              let uu____21230 = typars_of_binders env binders  in
              (match uu____21230 with
               | (env',typars) ->
                   let kopt1 =
                     match kopt with
                     | FStar_Pervasives_Native.None  ->
                         let uu____21264 =
                           FStar_Util.for_some
                             (fun uu___20_21267  ->
                                match uu___20_21267 with
                                | FStar_Syntax_Syntax.Effect  -> true
                                | uu____21270 -> false) quals
                            in
                         if uu____21264
                         then
                           FStar_Pervasives_Native.Some
                             FStar_Syntax_Syntax.teff
                         else FStar_Pervasives_Native.None
                     | FStar_Pervasives_Native.Some k ->
                         let uu____21278 = desugar_term env' k  in
                         FStar_Pervasives_Native.Some uu____21278
                      in
                   let t0 = t  in
                   let quals1 =
                     let uu____21283 =
                       FStar_All.pipe_right quals
                         (FStar_Util.for_some
                            (fun uu___21_21289  ->
                               match uu___21_21289 with
                               | FStar_Syntax_Syntax.Logic  -> true
                               | uu____21292 -> false))
                        in
                     if uu____21283
                     then quals
                     else
                       if
                         t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula
                       then FStar_Syntax_Syntax.Logic :: quals
                       else quals
                      in
                   let qlid = FStar_Syntax_DsEnv.qualify env id1  in
                   let se =
                     let uu____21306 =
                       FStar_All.pipe_right quals1
                         (FStar_List.contains FStar_Syntax_Syntax.Effect)
                        in
                     if uu____21306
                     then
                       let uu____21312 =
                         let uu____21319 =
                           let uu____21320 = unparen t  in
                           uu____21320.FStar_Parser_AST.tm  in
                         match uu____21319 with
                         | FStar_Parser_AST.Construct (head1,args) ->
                             let uu____21341 =
                               match FStar_List.rev args with
                               | (last_arg,uu____21371)::args_rev ->
                                   let uu____21383 =
                                     let uu____21384 = unparen last_arg  in
                                     uu____21384.FStar_Parser_AST.tm  in
                                   (match uu____21383 with
                                    | FStar_Parser_AST.Attributes ts ->
                                        (ts, (FStar_List.rev args_rev))
                                    | uu____21412 -> ([], args))
                               | uu____21421 -> ([], args)  in
                             (match uu____21341 with
                              | (cattributes,args1) ->
                                  let uu____21460 =
                                    desugar_attributes env cattributes  in
                                  ((FStar_Parser_AST.mk_term
                                      (FStar_Parser_AST.Construct
                                         (head1, args1))
                                      t.FStar_Parser_AST.range
                                      t.FStar_Parser_AST.level), uu____21460))
                         | uu____21471 -> (t, [])  in
                       match uu____21312 with
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
                                  (fun uu___22_21494  ->
                                     match uu___22_21494 with
                                     | FStar_Syntax_Syntax.Effect  -> false
                                     | uu____21497 -> true))
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
          | (FStar_Parser_AST.TyconRecord uu____21505)::[] ->
              let trec = FStar_List.hd tcs  in
              let uu____21525 = tycon_record_as_variant trec  in
              (match uu____21525 with
               | (t,fs) ->
                   let uu____21542 =
                     let uu____21545 =
                       let uu____21546 =
                         let uu____21555 =
                           let uu____21558 =
                             FStar_Syntax_DsEnv.current_module env  in
                           FStar_Ident.ids_of_lid uu____21558  in
                         (uu____21555, fs)  in
                       FStar_Syntax_Syntax.RecordType uu____21546  in
                     uu____21545 :: quals  in
                   desugar_tycon env d uu____21542 [t])
          | uu____21563::uu____21564 ->
              let env0 = env  in
              let mutuals =
                FStar_List.map
                  (fun x  ->
                     FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env)
                       (tycon_id x)) tcs
                 in
              let rec collect_tcs quals1 et tc =
                let uu____21722 = et  in
                match uu____21722 with
                | (env1,tcs1) ->
                    (match tc with
                     | FStar_Parser_AST.TyconRecord uu____21932 ->
                         let trec = tc  in
                         let uu____21952 = tycon_record_as_variant trec  in
                         (match uu____21952 with
                          | (t,fs) ->
                              let uu____22008 =
                                let uu____22011 =
                                  let uu____22012 =
                                    let uu____22021 =
                                      let uu____22024 =
                                        FStar_Syntax_DsEnv.current_module
                                          env1
                                         in
                                      FStar_Ident.ids_of_lid uu____22024  in
                                    (uu____22021, fs)  in
                                  FStar_Syntax_Syntax.RecordType uu____22012
                                   in
                                uu____22011 :: quals1  in
                              collect_tcs uu____22008 (env1, tcs1) t)
                     | FStar_Parser_AST.TyconVariant
                         (id1,binders,kopt,constructors) ->
                         let uu____22102 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22102 with
                          | (env2,uu____22159,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inl
                                    (se, constructors, tconstr, quals1)) ::
                                tcs1)))
                     | FStar_Parser_AST.TyconAbbrev (id1,binders,kopt,t) ->
                         let uu____22296 =
                           desugar_abstract_tc quals1 env1 mutuals
                             (FStar_Parser_AST.TyconAbstract
                                (id1, binders, kopt))
                            in
                         (match uu____22296 with
                          | (env2,uu____22353,se,tconstr) ->
                              (env2,
                                ((FStar_Util.Inr (se, binders, t, quals1)) ::
                                tcs1)))
                     | uu____22469 ->
                         FStar_Errors.raise_error
                           (FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType,
                             "Mutually defined type contains a non-inductive element")
                           rng)
                 in
              let uu____22515 =
                FStar_List.fold_left (collect_tcs quals) (env, []) tcs  in
              (match uu____22515 with
               | (env1,tcs1) ->
                   let tcs2 = FStar_List.rev tcs1  in
                   let tps_sigelts =
                     FStar_All.pipe_right tcs2
                       (FStar_List.collect
                          (fun uu___24_22967  ->
                             match uu___24_22967 with
                             | FStar_Util.Inr
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (id1,uvs,tpars,k,uu____23021,uu____23022);
                                    FStar_Syntax_Syntax.sigrng = uu____23023;
                                    FStar_Syntax_Syntax.sigquals =
                                      uu____23024;
                                    FStar_Syntax_Syntax.sigmeta = uu____23025;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23026;
                                    FStar_Syntax_Syntax.sigopts = uu____23027;_},binders,t,quals1)
                                 ->
                                 let t1 =
                                   let uu____23089 =
                                     typars_of_binders env1 binders  in
                                   match uu____23089 with
                                   | (env2,tpars1) ->
                                       let uu____23116 =
                                         push_tparams env2 tpars1  in
                                       (match uu____23116 with
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
                                 let uu____23145 =
                                   let uu____23156 =
                                     mk_typ_abbrev env1 d id1 uvs tpars
                                       (FStar_Pervasives_Native.Some k) t1
                                       [id1] quals1 rng
                                      in
                                   ([], uu____23156)  in
                                 [uu____23145]
                             | FStar_Util.Inl
                                 ({
                                    FStar_Syntax_Syntax.sigel =
                                      FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,univs1,tpars,k,mutuals1,uu____23192);
                                    FStar_Syntax_Syntax.sigrng = uu____23193;
                                    FStar_Syntax_Syntax.sigquals =
                                      tname_quals;
                                    FStar_Syntax_Syntax.sigmeta = uu____23195;
                                    FStar_Syntax_Syntax.sigattrs =
                                      uu____23196;
                                    FStar_Syntax_Syntax.sigopts = uu____23197;_},constrs,tconstr,quals1)
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
                                 let uu____23288 = push_tparams env1 tpars
                                    in
                                 (match uu____23288 with
                                  | (env_tps,tps) ->
                                      let data_tpars =
                                        FStar_List.map
                                          (fun uu____23347  ->
                                             match uu____23347 with
                                             | (x,uu____23359) ->
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
                                        let uu____23370 =
                                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                            env1 tname
                                           in
                                        FStar_All.pipe_right uu____23370
                                          FStar_Pervasives_Native.snd
                                         in
                                      let uu____23393 =
                                        let uu____23412 =
                                          FStar_All.pipe_right constrs
                                            (FStar_List.map
                                               (fun uu____23489  ->
                                                  match uu____23489 with
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
                                                        let uu____23532 =
                                                          close env_tps t  in
                                                        desugar_term env_tps
                                                          uu____23532
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
                                                                uu___23_23543
                                                                 ->
                                                                match uu___23_23543
                                                                with
                                                                | FStar_Syntax_Syntax.RecordType
                                                                    fns ->
                                                                    [
                                                                    FStar_Syntax_Syntax.RecordConstructor
                                                                    fns]
                                                                | uu____23555
                                                                    -> []))
                                                         in
                                                      let ntps =
                                                        FStar_List.length
                                                          data_tpars
                                                         in
                                                      let uu____23563 =
                                                        let uu____23574 =
                                                          let uu____23575 =
                                                            let uu____23576 =
                                                              let uu____23592
                                                                =
                                                                let uu____23593
                                                                  =
                                                                  let uu____23596
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    t1
                                                                    FStar_Syntax_Util.name_function_binders
                                                                     in
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    uu____23596
                                                                   in
                                                                FStar_Syntax_Util.arrow
                                                                  data_tpars
                                                                  uu____23593
                                                                 in
                                                              (name, univs1,
                                                                uu____23592,
                                                                tname, ntps,
                                                                mutuals1)
                                                               in
                                                            FStar_Syntax_Syntax.Sig_datacon
                                                              uu____23576
                                                             in
                                                          {
                                                            FStar_Syntax_Syntax.sigel
                                                              = uu____23575;
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
                                                        (tps, uu____23574)
                                                         in
                                                      (name, uu____23563)))
                                           in
                                        FStar_All.pipe_left FStar_List.split
                                          uu____23412
                                         in
                                      (match uu____23393 with
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
                             | uu____23728 -> failwith "impossible"))
                      in
                   let sigelts =
                     FStar_All.pipe_right tps_sigelts
                       (FStar_List.map
                          (fun uu____23809  ->
                             match uu____23809 with | (uu____23820,se) -> se))
                      in
                   let uu____23834 =
                     let uu____23841 =
                       FStar_List.collect FStar_Syntax_Util.lids_of_sigelt
                         sigelts
                        in
                     FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle
                       sigelts quals uu____23841 rng
                      in
                   (match uu____23834 with
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
                               (fun uu____23886  ->
                                  match uu____23886 with
                                  | (tps,se) ->
                                      mk_data_projector_names quals env3 se))
                           in
                        let discs =
                          FStar_All.pipe_right sigelts
                            (FStar_List.collect
                               (fun se  ->
                                  match se.FStar_Syntax_Syntax.sigel with
                                  | FStar_Syntax_Syntax.Sig_inductive_typ
                                      (tname,uu____23934,tps,k,uu____23937,constrs)
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
                                      let uu____23958 =
                                        FStar_All.pipe_right constrs
                                          (FStar_List.filter
                                             (fun data_lid  ->
                                                let data_quals =
                                                  let data_se =
                                                    let uu____23973 =
                                                      FStar_All.pipe_right
                                                        sigelts
                                                        (FStar_List.find
                                                           (fun se1  ->
                                                              match se1.FStar_Syntax_Syntax.sigel
                                                              with
                                                              | FStar_Syntax_Syntax.Sig_datacon
                                                                  (name,uu____23990,uu____23991,uu____23992,uu____23993,uu____23994)
                                                                  ->
                                                                  FStar_Ident.lid_equals
                                                                    name
                                                                    data_lid
                                                              | uu____24001
                                                                  -> false))
                                                       in
                                                    FStar_All.pipe_right
                                                      uu____23973
                                                      FStar_Util.must
                                                     in
                                                  data_se.FStar_Syntax_Syntax.sigquals
                                                   in
                                                let uu____24005 =
                                                  FStar_All.pipe_right
                                                    data_quals
                                                    (FStar_List.existsb
                                                       (fun uu___25_24012  ->
                                                          match uu___25_24012
                                                          with
                                                          | FStar_Syntax_Syntax.RecordConstructor
                                                              uu____24014 ->
                                                              true
                                                          | uu____24024 ->
                                                              false))
                                                   in
                                                Prims.op_Negation uu____24005))
                                         in
                                      mk_data_discriminators quals2 env3
                                        uu____23958
                                  | uu____24026 -> []))
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
      let uu____24063 =
        FStar_List.fold_left
          (fun uu____24098  ->
             fun b  ->
               match uu____24098 with
               | (env1,binders1) ->
                   let uu____24142 = desugar_binder env1 b  in
                   (match uu____24142 with
                    | (FStar_Pervasives_Native.Some a,k) ->
                        let uu____24165 =
                          as_binder env1 b.FStar_Parser_AST.aqual
                            ((FStar_Pervasives_Native.Some a), k)
                           in
                        (match uu____24165 with
                         | (binder,env2) -> (env2, (binder :: binders1)))
                    | uu____24218 ->
                        FStar_Errors.raise_error
                          (FStar_Errors.Fatal_MissingNameInBinder,
                            "Missing name in binder")
                          b.FStar_Parser_AST.brange)) (env, []) binders
         in
      match uu____24063 with
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
          let uu____24322 =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___26_24329  ->
                    match uu___26_24329 with
                    | FStar_Syntax_Syntax.Reflectable uu____24331 -> true
                    | uu____24333 -> false))
             in
          if uu____24322
          then
            let monad_env =
              FStar_Syntax_DsEnv.enter_monad_scope env
                effect_name.FStar_Ident.ident
               in
            let reflect_lid =
              let uu____24338 = FStar_Ident.id_of_text "reflect"  in
              FStar_All.pipe_right uu____24338
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
        let warn1 uu____24389 =
          if warn
          then
            let uu____24391 =
              let uu____24397 =
                let uu____24399 = FStar_Ident.string_of_lid head1  in
                FStar_Util.format1
                  "Found ill-applied '%s', argument should be a non-empty list of integer literals"
                  uu____24399
                 in
              (FStar_Errors.Warning_UnappliedFail, uu____24397)  in
            FStar_Errors.log_issue at.FStar_Syntax_Syntax.pos uu____24391
          else ()  in
        let uu____24405 = FStar_Syntax_Util.head_and_args at  in
        match uu____24405 with
        | (hd1,args) ->
            let uu____24458 =
              let uu____24459 = FStar_Syntax_Subst.compress hd1  in
              uu____24459.FStar_Syntax_Syntax.n  in
            (match uu____24458 with
             | FStar_Syntax_Syntax.Tm_fvar fv when
                 FStar_Syntax_Syntax.fv_eq_lid fv head1 ->
                 (match args with
                  | [] -> ((FStar_Pervasives_Native.Some []), true)
                  | (a1,uu____24503)::[] ->
                      let uu____24528 =
                        let uu____24533 =
                          let uu____24542 =
                            FStar_Syntax_Embeddings.e_list
                              FStar_Syntax_Embeddings.e_int
                             in
                          FStar_Syntax_Embeddings.unembed uu____24542 a1  in
                        uu____24533 true FStar_Syntax_Embeddings.id_norm_cb
                         in
                      (match uu____24528 with
                       | FStar_Pervasives_Native.Some es ->
                           let uu____24565 =
                             let uu____24571 =
                               FStar_List.map FStar_BigInt.to_int_fs es  in
                             FStar_Pervasives_Native.Some uu____24571  in
                           (uu____24565, true)
                       | uu____24586 ->
                           (warn1 (); (FStar_Pervasives_Native.None, true)))
                  | uu____24602 ->
                      (warn1 (); (FStar_Pervasives_Native.None, true)))
             | uu____24624 -> (FStar_Pervasives_Native.None, false))
  
let (lookup_effect_lid :
  FStar_Syntax_DsEnv.env ->
    FStar_Ident.lident -> FStar_Range.range -> FStar_Syntax_Syntax.eff_decl)
  =
  fun env  ->
    fun l  ->
      fun r  ->
        let uu____24651 = FStar_Syntax_DsEnv.try_lookup_effect_defn env l  in
        match uu____24651 with
        | FStar_Pervasives_Native.None  ->
            let uu____24654 =
              let uu____24660 =
                let uu____24662 =
                  let uu____24664 = FStar_Syntax_Print.lid_to_string l  in
                  Prims.op_Hat uu____24664 " not found"  in
                Prims.op_Hat "Effect name " uu____24662  in
              (FStar_Errors.Fatal_EffectNotFound, uu____24660)  in
            FStar_Errors.raise_error uu____24654 r
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
                    let uu____24820 = desugar_binders monad_env eff_binders
                       in
                    match uu____24820 with
                    | (env1,binders) ->
                        let eff_t = desugar_term env1 eff_typ  in
                        let num_indices =
                          let uu____24859 =
                            let uu____24868 =
                              FStar_Syntax_Util.arrow_formals eff_t  in
                            FStar_Pervasives_Native.fst uu____24868  in
                          FStar_List.length uu____24859  in
                        (if is_layered1 && (num_indices <= Prims.int_one)
                         then
                           (let uu____24902 =
                              let uu____24908 =
                                let uu____24910 =
                                  let uu____24912 =
                                    FStar_Ident.text_of_id eff_name  in
                                  Prims.op_Hat uu____24912
                                    "is defined as a layered effect but has no indices"
                                   in
                                Prims.op_Hat "Effect " uu____24910  in
                              (FStar_Errors.Fatal_NotEnoughArgumentsForEffect,
                                uu____24908)
                               in
                            FStar_Errors.raise_error uu____24902
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
                                (uu____24980,uu____24981,(FStar_Parser_AST.TyconAbbrev
                                 (name,uu____24983,uu____24984,uu____24985))::[])
                                -> FStar_Ident.text_of_id name
                            | uu____25000 ->
                                failwith
                                  "Malformed effect member declaration."
                             in
                          let uu____25003 =
                            FStar_List.partition
                              (fun decl  ->
                                 let uu____25015 = name_of_eff_decl decl  in
                                 FStar_List.mem uu____25015 mandatory_members)
                              eff_decls
                             in
                          match uu____25003 with
                          | (mandatory_members_decls,actions) ->
                              let uu____25034 =
                                FStar_All.pipe_right mandatory_members_decls
                                  (FStar_List.fold_left
                                     (fun uu____25063  ->
                                        fun decl  ->
                                          match uu____25063 with
                                          | (env2,out) ->
                                              let uu____25083 =
                                                desugar_decl env2 decl  in
                                              (match uu____25083 with
                                               | (env3,ses) ->
                                                   let uu____25096 =
                                                     let uu____25099 =
                                                       FStar_List.hd ses  in
                                                     uu____25099 :: out  in
                                                   (env3, uu____25096)))
                                     (env1, []))
                                 in
                              (match uu____25034 with
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
                                                 (uu____25145,uu____25146,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25149,
                                                   {
                                                     FStar_Parser_AST.tm =
                                                       FStar_Parser_AST.Construct
                                                       (uu____25150,(def,uu____25152)::
                                                        (cps_type,uu____25154)::[]);
                                                     FStar_Parser_AST.range =
                                                       uu____25155;
                                                     FStar_Parser_AST.level =
                                                       uu____25156;_}))::[])
                                                 when
                                                 Prims.op_Negation for_free
                                                 ->
                                                 let uu____25189 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25189 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25221 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25222 =
                                                        let uu____25223 =
                                                          desugar_term env3
                                                            def
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25223
                                                         in
                                                      let uu____25230 =
                                                        let uu____25231 =
                                                          desugar_typ env3
                                                            cps_type
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25231
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25221;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25222;
                                                        FStar_Syntax_Syntax.action_typ
                                                          = uu____25230
                                                      })
                                             | FStar_Parser_AST.Tycon
                                                 (uu____25238,uu____25239,(FStar_Parser_AST.TyconAbbrev
                                                  (name,action_params,uu____25242,defn))::[])
                                                 when for_free || is_layered1
                                                 ->
                                                 let uu____25258 =
                                                   desugar_binders env2
                                                     action_params
                                                    in
                                                 (match uu____25258 with
                                                  | (env3,action_params1) ->
                                                      let action_params2 =
                                                        FStar_Syntax_Subst.close_binders
                                                          action_params1
                                                         in
                                                      let uu____25290 =
                                                        FStar_Syntax_DsEnv.qualify
                                                          env3 name
                                                         in
                                                      let uu____25291 =
                                                        let uu____25292 =
                                                          desugar_term env3
                                                            defn
                                                           in
                                                        FStar_Syntax_Subst.close
                                                          (FStar_List.append
                                                             binders1
                                                             action_params2)
                                                          uu____25292
                                                         in
                                                      {
                                                        FStar_Syntax_Syntax.action_name
                                                          = uu____25290;
                                                        FStar_Syntax_Syntax.action_unqualified_name
                                                          = name;
                                                        FStar_Syntax_Syntax.action_univs
                                                          = [];
                                                        FStar_Syntax_Syntax.action_params
                                                          = action_params2;
                                                        FStar_Syntax_Syntax.action_defn
                                                          = uu____25291;
                                                        FStar_Syntax_Syntax.action_typ
                                                          =
                                                          FStar_Syntax_Syntax.tun
                                                      })
                                             | uu____25299 ->
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
                                       let uu____25318 =
                                         FStar_Ident.mk_ident
                                           (s, (d.FStar_Parser_AST.drange))
                                          in
                                       FStar_Syntax_DsEnv.qualify env2
                                         uu____25318
                                        in
                                     let uu____25320 =
                                       let uu____25321 =
                                         FStar_Syntax_DsEnv.fail_or env2
                                           (FStar_Syntax_DsEnv.try_lookup_definition
                                              env2) l
                                          in
                                       FStar_All.pipe_left
                                         (FStar_Syntax_Subst.close binders1)
                                         uu____25321
                                        in
                                     ([], uu____25320)  in
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
                                       let uu____25343 =
                                         let uu____25344 =
                                           let uu____25347 = lookup1 "repr"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25347
                                            in
                                         let uu____25349 =
                                           let uu____25352 = lookup1 "return"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25352
                                            in
                                         let uu____25354 =
                                           let uu____25357 = lookup1 "bind"
                                              in
                                           FStar_Pervasives_Native.Some
                                             uu____25357
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
                                             uu____25344;
                                           FStar_Syntax_Syntax.return_repr =
                                             uu____25349;
                                           FStar_Syntax_Syntax.bind_repr =
                                             uu____25354
                                         }  in
                                       FStar_Syntax_Syntax.DM4F_eff
                                         uu____25343
                                     else
                                       if is_layered1
                                       then
                                         (let to_comb uu____25391 =
                                            match uu____25391 with
                                            | (us,t) ->
                                                ((us, t), dummy_tscheme)
                                             in
                                          let uu____25438 =
                                            let uu____25439 =
                                              FStar_Ident.lid_of_str ""  in
                                            let uu____25441 =
                                              let uu____25446 =
                                                lookup1 "repr"  in
                                              FStar_All.pipe_right
                                                uu____25446 to_comb
                                               in
                                            let uu____25464 =
                                              let uu____25469 =
                                                lookup1 "return"  in
                                              FStar_All.pipe_right
                                                uu____25469 to_comb
                                               in
                                            let uu____25487 =
                                              let uu____25492 =
                                                lookup1 "bind"  in
                                              FStar_All.pipe_right
                                                uu____25492 to_comb
                                               in
                                            let uu____25510 =
                                              let uu____25515 =
                                                lookup1 "subcomp"  in
                                              FStar_All.pipe_right
                                                uu____25515 to_comb
                                               in
                                            let uu____25533 =
                                              let uu____25538 =
                                                lookup1 "if_then_else"  in
                                              FStar_All.pipe_right
                                                uu____25538 to_comb
                                               in
                                            {
                                              FStar_Syntax_Syntax.l_base_effect
                                                = uu____25439;
                                              FStar_Syntax_Syntax.l_repr =
                                                uu____25441;
                                              FStar_Syntax_Syntax.l_return =
                                                uu____25464;
                                              FStar_Syntax_Syntax.l_bind =
                                                uu____25487;
                                              FStar_Syntax_Syntax.l_subcomp =
                                                uu____25510;
                                              FStar_Syntax_Syntax.l_if_then_else
                                                = uu____25533
                                            }  in
                                          FStar_Syntax_Syntax.Layered_eff
                                            uu____25438)
                                       else
                                         (let rr =
                                            FStar_Util.for_some
                                              (fun uu___27_25561  ->
                                                 match uu___27_25561 with
                                                 | FStar_Syntax_Syntax.Reifiable
                                                      -> true
                                                 | FStar_Syntax_Syntax.Reflectable
                                                     uu____25564 -> true
                                                 | uu____25566 -> false)
                                              qualifiers
                                             in
                                          let uu____25568 =
                                            let uu____25569 =
                                              lookup1 "return_wp"  in
                                            let uu____25571 =
                                              lookup1 "bind_wp"  in
                                            let uu____25573 =
                                              lookup1 "stronger"  in
                                            let uu____25575 =
                                              lookup1 "if_then_else"  in
                                            let uu____25577 =
                                              lookup1 "ite_wp"  in
                                            let uu____25579 =
                                              lookup1 "close_wp"  in
                                            let uu____25581 =
                                              lookup1 "trivial"  in
                                            let uu____25583 =
                                              if rr
                                              then
                                                let uu____25589 =
                                                  lookup1 "repr"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25589
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25593 =
                                              if rr
                                              then
                                                let uu____25599 =
                                                  lookup1 "return"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25599
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            let uu____25603 =
                                              if rr
                                              then
                                                let uu____25609 =
                                                  lookup1 "bind"  in
                                                FStar_Pervasives_Native.Some
                                                  uu____25609
                                              else
                                                FStar_Pervasives_Native.None
                                               in
                                            {
                                              FStar_Syntax_Syntax.ret_wp =
                                                uu____25569;
                                              FStar_Syntax_Syntax.bind_wp =
                                                uu____25571;
                                              FStar_Syntax_Syntax.stronger =
                                                uu____25573;
                                              FStar_Syntax_Syntax.if_then_else
                                                = uu____25575;
                                              FStar_Syntax_Syntax.ite_wp =
                                                uu____25577;
                                              FStar_Syntax_Syntax.close_wp =
                                                uu____25579;
                                              FStar_Syntax_Syntax.trivial =
                                                uu____25581;
                                              FStar_Syntax_Syntax.repr =
                                                uu____25583;
                                              FStar_Syntax_Syntax.return_repr
                                                = uu____25593;
                                              FStar_Syntax_Syntax.bind_repr =
                                                uu____25603
                                            }  in
                                          FStar_Syntax_Syntax.Primitive_eff
                                            uu____25568)
                                      in
                                   let sigel =
                                     let uu____25614 =
                                       let uu____25615 =
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
                                           uu____25615
                                       }  in
                                     FStar_Syntax_Syntax.Sig_new_effect
                                       uu____25614
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
                                               let uu____25632 =
                                                 FStar_Syntax_Util.action_as_lb
                                                   mname a
                                                   (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                                  in
                                               FStar_Syntax_DsEnv.push_sigelt
                                                 env4 uu____25632) env3)
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
                let uu____25655 = desugar_binders env1 eff_binders  in
                match uu____25655 with
                | (env2,binders) ->
                    let uu____25692 =
                      let uu____25703 = head_and_args defn  in
                      match uu____25703 with
                      | (head1,args) ->
                          let lid =
                            match head1.FStar_Parser_AST.tm with
                            | FStar_Parser_AST.Name l -> l
                            | uu____25740 ->
                                let uu____25741 =
                                  let uu____25747 =
                                    let uu____25749 =
                                      let uu____25751 =
                                        FStar_Parser_AST.term_to_string head1
                                         in
                                      Prims.op_Hat uu____25751 " not found"
                                       in
                                    Prims.op_Hat "Effect " uu____25749  in
                                  (FStar_Errors.Fatal_EffectNotFound,
                                    uu____25747)
                                   in
                                FStar_Errors.raise_error uu____25741
                                  d.FStar_Parser_AST.drange
                             in
                          let ed =
                            FStar_Syntax_DsEnv.fail_or env2
                              (FStar_Syntax_DsEnv.try_lookup_effect_defn env2)
                              lid
                             in
                          let uu____25757 =
                            match FStar_List.rev args with
                            | (last_arg,uu____25787)::args_rev ->
                                let uu____25799 =
                                  let uu____25800 = unparen last_arg  in
                                  uu____25800.FStar_Parser_AST.tm  in
                                (match uu____25799 with
                                 | FStar_Parser_AST.Attributes ts ->
                                     (ts, (FStar_List.rev args_rev))
                                 | uu____25828 -> ([], args))
                            | uu____25837 -> ([], args)  in
                          (match uu____25757 with
                           | (cattributes,args1) ->
                               let uu____25880 = desugar_args env2 args1  in
                               let uu____25881 =
                                 desugar_attributes env2 cattributes  in
                               (lid, ed, uu____25880, uu____25881))
                       in
                    (match uu____25692 with
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
                          (let uu____25921 =
                             FStar_Syntax_Subst.open_term'
                               ed.FStar_Syntax_Syntax.binders
                               FStar_Syntax_Syntax.t_unit
                              in
                           match uu____25921 with
                           | (ed_binders,uu____25935,ed_binders_opening) ->
                               let sub' shift_n uu____25954 =
                                 match uu____25954 with
                                 | (us,x) ->
                                     let x1 =
                                       let uu____25969 =
                                         FStar_Syntax_Subst.shift_subst
                                           (shift_n + (FStar_List.length us))
                                           ed_binders_opening
                                          in
                                       FStar_Syntax_Subst.subst uu____25969 x
                                        in
                                     let s =
                                       FStar_Syntax_Util.subst_of_list
                                         ed_binders args
                                        in
                                     let uu____25973 =
                                       let uu____25974 =
                                         FStar_Syntax_Subst.subst s x1  in
                                       (us, uu____25974)  in
                                     FStar_Syntax_Subst.close_tscheme
                                       binders1 uu____25973
                                  in
                               let sub1 = sub' Prims.int_zero  in
                               let mname =
                                 FStar_Syntax_DsEnv.qualify env0 eff_name  in
                               let ed1 =
                                 let uu____25995 =
                                   sub1 ed.FStar_Syntax_Syntax.signature  in
                                 let uu____25996 =
                                   FStar_Syntax_Util.apply_eff_combinators
                                     sub1 ed.FStar_Syntax_Syntax.combinators
                                    in
                                 let uu____25997 =
                                   FStar_List.map
                                     (fun action  ->
                                        let nparam =
                                          FStar_List.length
                                            action.FStar_Syntax_Syntax.action_params
                                           in
                                        let uu____26013 =
                                          FStar_Syntax_DsEnv.qualify env2
                                            action.FStar_Syntax_Syntax.action_unqualified_name
                                           in
                                        let uu____26014 =
                                          let uu____26015 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_defn))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26015
                                           in
                                        let uu____26030 =
                                          let uu____26031 =
                                            sub' nparam
                                              ([],
                                                (action.FStar_Syntax_Syntax.action_typ))
                                             in
                                          FStar_Pervasives_Native.snd
                                            uu____26031
                                           in
                                        {
                                          FStar_Syntax_Syntax.action_name =
                                            uu____26013;
                                          FStar_Syntax_Syntax.action_unqualified_name
                                            =
                                            (action.FStar_Syntax_Syntax.action_unqualified_name);
                                          FStar_Syntax_Syntax.action_univs =
                                            (action.FStar_Syntax_Syntax.action_univs);
                                          FStar_Syntax_Syntax.action_params =
                                            (action.FStar_Syntax_Syntax.action_params);
                                          FStar_Syntax_Syntax.action_defn =
                                            uu____26014;
                                          FStar_Syntax_Syntax.action_typ =
                                            uu____26030
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
                                     uu____25995;
                                   FStar_Syntax_Syntax.combinators =
                                     uu____25996;
                                   FStar_Syntax_Syntax.actions = uu____25997;
                                   FStar_Syntax_Syntax.eff_attrs =
                                     (ed.FStar_Syntax_Syntax.eff_attrs)
                                 }  in
                               let se =
                                 let uu____26047 =
                                   let uu____26050 =
                                     trans_qual1
                                       (FStar_Pervasives_Native.Some mname)
                                      in
                                   FStar_List.map uu____26050 quals  in
                                 {
                                   FStar_Syntax_Syntax.sigel =
                                     (FStar_Syntax_Syntax.Sig_new_effect ed1);
                                   FStar_Syntax_Syntax.sigrng =
                                     (d.FStar_Parser_AST.drange);
                                   FStar_Syntax_Syntax.sigquals = uu____26047;
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
                                           let uu____26065 =
                                             FStar_Syntax_Util.action_as_lb
                                               mname a
                                               (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos
                                              in
                                           FStar_Syntax_DsEnv.push_sigelt
                                             env4 uu____26065) env3)
                                  in
                               let env5 =
                                 let uu____26067 =
                                   FStar_All.pipe_right quals
                                     (FStar_List.contains
                                        FStar_Parser_AST.Reflectable)
                                    in
                                 if uu____26067
                                 then
                                   let reflect_lid =
                                     let uu____26074 =
                                       FStar_Ident.id_of_text "reflect"  in
                                     FStar_All.pipe_right uu____26074
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
        let uu____26091 = FStar_Syntax_DsEnv.snapshot env  in
        FStar_All.pipe_right uu____26091 FStar_Pervasives_Native.snd  in
      let attrs = FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs
         in
      let uu____26106 = desugar_decl_noattrs env d  in
      match uu____26106 with
      | (env1,sigelts) ->
          let val_attrs =
            match sigelts with
            | {
                FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let
                  uu____26122;
                FStar_Syntax_Syntax.sigrng = uu____26123;
                FStar_Syntax_Syntax.sigquals = uu____26124;
                FStar_Syntax_Syntax.sigmeta = uu____26125;
                FStar_Syntax_Syntax.sigattrs = uu____26126;
                FStar_Syntax_Syntax.sigopts = uu____26127;_}::[] ->
                let uu____26140 =
                  let uu____26143 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____26143  in
                FStar_All.pipe_right uu____26140
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____26151 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____26151))
            | {
                FStar_Syntax_Syntax.sigel =
                  FStar_Syntax_Syntax.Sig_inductive_typ uu____26164;
                FStar_Syntax_Syntax.sigrng = uu____26165;
                FStar_Syntax_Syntax.sigquals = uu____26166;
                FStar_Syntax_Syntax.sigmeta = uu____26167;
                FStar_Syntax_Syntax.sigattrs = uu____26168;
                FStar_Syntax_Syntax.sigopts = uu____26169;_}::uu____26170 ->
                let uu____26195 =
                  let uu____26198 = FStar_List.hd sigelts  in
                  FStar_Syntax_Util.lids_of_sigelt uu____26198  in
                FStar_All.pipe_right uu____26195
                  (FStar_List.collect
                     (fun nm  ->
                        let uu____26206 =
                          FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                            env0 nm
                           in
                        FStar_Pervasives_Native.snd uu____26206))
            | uu____26219 -> []  in
          let attrs1 = FStar_List.append attrs val_attrs  in
          let uu____26223 =
            FStar_List.map
              (fun sigelt  ->
                 let uu___3426_26227 = sigelt  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (uu___3426_26227.FStar_Syntax_Syntax.sigel);
                   FStar_Syntax_Syntax.sigrng =
                     (uu___3426_26227.FStar_Syntax_Syntax.sigrng);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___3426_26227.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___3426_26227.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs = attrs1;
                   FStar_Syntax_Syntax.sigopts =
                     (uu___3426_26227.FStar_Syntax_Syntax.sigopts)
                 }) sigelts
             in
          (env1, uu____26223)

and (desugar_decl :
  env_t -> FStar_Parser_AST.decl -> (env_t * FStar_Syntax_Syntax.sigelts)) =
  fun env  ->
    fun d  ->
      let uu____26234 = desugar_decl_aux env d  in
      match uu____26234 with
      | (env1,ses) ->
          let uu____26245 =
            FStar_All.pipe_right ses
              (FStar_List.map generalize_annotated_univs)
             in
          (env1, uu____26245)

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
          let uu____26277 = FStar_Syntax_DsEnv.iface env  in
          if uu____26277
          then
            FStar_Errors.raise_error
              (FStar_Errors.Fatal_FriendInterface,
                "'friend' declarations are not allowed in interfaces")
              d.FStar_Parser_AST.drange
          else
            (let uu____26292 =
               let uu____26294 =
                 let uu____26296 = FStar_Syntax_DsEnv.dep_graph env  in
                 let uu____26297 = FStar_Syntax_DsEnv.current_module env  in
                 FStar_Parser_Dep.module_has_interface uu____26296
                   uu____26297
                  in
               Prims.op_Negation uu____26294  in
             if uu____26292
             then
               FStar_Errors.raise_error
                 (FStar_Errors.Fatal_FriendInterface,
                   "'friend' declarations are not allowed in modules that lack interfaces")
                 d.FStar_Parser_AST.drange
             else
               (let uu____26311 =
                  let uu____26313 =
                    let uu____26315 = FStar_Syntax_DsEnv.dep_graph env  in
                    FStar_Parser_Dep.module_has_interface uu____26315 lid  in
                  Prims.op_Negation uu____26313  in
                if uu____26311
                then
                  FStar_Errors.raise_error
                    (FStar_Errors.Fatal_FriendInterface,
                      "'friend' declarations cannot refer to modules that lack interfaces")
                    d.FStar_Parser_AST.drange
                else
                  (let uu____26329 =
                     let uu____26331 =
                       let uu____26333 = FStar_Syntax_DsEnv.dep_graph env  in
                       FStar_Parser_Dep.deps_has_implementation uu____26333
                         lid
                        in
                     Prims.op_Negation uu____26331  in
                   if uu____26329
                   then
                     FStar_Errors.raise_error
                       (FStar_Errors.Fatal_FriendInterface,
                         "'friend' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")
                       d.FStar_Parser_AST.drange
                   else (env, []))))
      | FStar_Parser_AST.Include lid ->
          let env1 = FStar_Syntax_DsEnv.push_include env lid  in (env1, [])
      | FStar_Parser_AST.ModuleAbbrev (x,l) ->
          let uu____26351 = FStar_Syntax_DsEnv.push_module_abbrev env x l  in
          (uu____26351, [])
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
              | (FStar_Parser_AST.TyconRecord uu____26380)::[] ->
                  FStar_Parser_AST.Noeq :: quals1
              | uu____26399 ->
                  FStar_Errors.raise_error
                    (FStar_Errors.Error_BadClassDecl,
                      "Ill-formed `class` declaration: definition must be a record type")
                    d.FStar_Parser_AST.drange
            else quals1  in
          let uu____26408 =
            let uu____26413 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals2
               in
            desugar_tycon env d uu____26413 tcs  in
          (match uu____26408 with
           | (env1,ses) ->
               let mkclass lid =
                 let uu____26430 =
                   let uu____26431 =
                     let uu____26438 =
                       FStar_Syntax_Syntax.new_bv
                         FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun
                        in
                     FStar_Syntax_Syntax.mk_binder uu____26438  in
                   [uu____26431]  in
                 let uu____26451 =
                   let uu____26454 =
                     FStar_Syntax_Syntax.tabbrev
                       FStar_Parser_Const.mk_class_lid
                      in
                   let uu____26457 =
                     let uu____26468 =
                       let uu____26477 =
                         let uu____26478 = FStar_Ident.string_of_lid lid  in
                         FStar_Syntax_Util.exp_string uu____26478  in
                       FStar_Syntax_Syntax.as_arg uu____26477  in
                     [uu____26468]  in
                   FStar_Syntax_Util.mk_app uu____26454 uu____26457  in
                 FStar_Syntax_Util.abs uu____26430 uu____26451
                   FStar_Pervasives_Native.None
                  in
               let get_meths se =
                 let rec get_fname quals3 =
                   match quals3 with
                   | (FStar_Syntax_Syntax.Projector
                       (uu____26518,id1))::uu____26520 ->
                       FStar_Pervasives_Native.Some id1
                   | uu____26523::quals4 -> get_fname quals4
                   | [] -> FStar_Pervasives_Native.None  in
                 let uu____26527 = get_fname se.FStar_Syntax_Syntax.sigquals
                    in
                 match uu____26527 with
                 | FStar_Pervasives_Native.None  -> []
                 | FStar_Pervasives_Native.Some id1 ->
                     let uu____26533 = FStar_Syntax_DsEnv.qualify env1 id1
                        in
                     [uu____26533]
                  in
               let rec splice_decl meths se =
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_bundle (ses1,uu____26554) ->
                     FStar_List.concatMap (splice_decl meths) ses1
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (lid,uu____26564,uu____26565,uu____26566,uu____26567,uu____26568)
                     ->
                     let uu____26577 =
                       let uu____26578 =
                         let uu____26579 =
                           let uu____26586 = mkclass lid  in
                           (meths, uu____26586)  in
                         FStar_Syntax_Syntax.Sig_splice uu____26579  in
                       {
                         FStar_Syntax_Syntax.sigel = uu____26578;
                         FStar_Syntax_Syntax.sigrng =
                           (d.FStar_Parser_AST.drange);
                         FStar_Syntax_Syntax.sigquals = [];
                         FStar_Syntax_Syntax.sigmeta =
                           FStar_Syntax_Syntax.default_sigmeta;
                         FStar_Syntax_Syntax.sigattrs = [];
                         FStar_Syntax_Syntax.sigopts =
                           FStar_Pervasives_Native.None
                       }  in
                     [uu____26577]
                 | uu____26589 -> []  in
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
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatOp uu____26623;
                    FStar_Parser_AST.prange = uu____26624;_},uu____26625)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                      uu____26635;
                    FStar_Parser_AST.prange = uu____26636;_},uu____26637)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatOp
                           uu____26653;
                         FStar_Parser_AST.prange = uu____26654;_},uu____26655);
                    FStar_Parser_AST.prange = uu____26656;_},uu____26657)::[]
                   -> false
               | ({
                    FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed
                      ({
                         FStar_Parser_AST.pat = FStar_Parser_AST.PatVar
                           uu____26679;
                         FStar_Parser_AST.prange = uu____26680;_},uu____26681);
                    FStar_Parser_AST.prange = uu____26682;_},uu____26683)::[]
                   -> false
               | (p,uu____26712)::[] ->
                   let uu____26721 = is_app_pattern p  in
                   Prims.op_Negation uu____26721
               | uu____26723 -> false)
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
            let uu____26798 = desugar_term_maybe_top true env as_inner_let
               in
            (match uu____26798 with
             | (ds_lets,aq) ->
                 (check_no_aq aq;
                  (let uu____26811 =
                     let uu____26812 =
                       FStar_All.pipe_left FStar_Syntax_Subst.compress
                         ds_lets
                        in
                     uu____26812.FStar_Syntax_Syntax.n  in
                   match uu____26811 with
                   | FStar_Syntax_Syntax.Tm_let (lbs,uu____26822) ->
                       let fvs =
                         FStar_All.pipe_right
                           (FStar_Pervasives_Native.snd lbs)
                           (FStar_List.map
                              (fun lb  ->
                                 FStar_Util.right
                                   lb.FStar_Syntax_Syntax.lbname))
                          in
                       let uu____26853 =
                         FStar_List.fold_right
                           (fun fv  ->
                              fun uu____26878  ->
                                match uu____26878 with
                                | (qs,ats) ->
                                    let uu____26905 =
                                      FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs
                                        env
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    (match uu____26905 with
                                     | (qs',ats') ->
                                         ((FStar_List.append qs' qs),
                                           (FStar_List.append ats' ats))))
                           fvs ([], [])
                          in
                       (match uu____26853 with
                        | (val_quals,val_attrs) ->
                            let quals1 =
                              match quals with
                              | uu____26959::uu____26960 ->
                                  FStar_List.map
                                    (trans_qual1 FStar_Pervasives_Native.None)
                                    quals
                              | uu____26963 -> val_quals  in
                            let quals2 =
                              let uu____26967 =
                                FStar_All.pipe_right lets1
                                  (FStar_Util.for_some
                                     (fun uu____27000  ->
                                        match uu____27000 with
                                        | (uu____27014,(uu____27015,t)) ->
                                            t.FStar_Parser_AST.level =
                                              FStar_Parser_AST.Formula))
                                 in
                              if uu____26967
                              then FStar_Syntax_Syntax.Logic :: quals1
                              else quals1  in
                            let lbs1 =
                              let uu____27035 =
                                FStar_All.pipe_right quals2
                                  (FStar_List.contains
                                     FStar_Syntax_Syntax.Abstract)
                                 in
                              if uu____27035
                              then
                                let uu____27041 =
                                  FStar_All.pipe_right
                                    (FStar_Pervasives_Native.snd lbs)
                                    (FStar_List.map
                                       (fun lb  ->
                                          let fv =
                                            FStar_Util.right
                                              lb.FStar_Syntax_Syntax.lbname
                                             in
                                          let uu___3603_27056 = lb  in
                                          {
                                            FStar_Syntax_Syntax.lbname =
                                              (FStar_Util.Inr
                                                 (let uu___3605_27058 = fv
                                                     in
                                                  {
                                                    FStar_Syntax_Syntax.fv_name
                                                      =
                                                      (uu___3605_27058.FStar_Syntax_Syntax.fv_name);
                                                    FStar_Syntax_Syntax.fv_delta
                                                      =
                                                      (FStar_Syntax_Syntax.Delta_abstract
                                                         (fv.FStar_Syntax_Syntax.fv_delta));
                                                    FStar_Syntax_Syntax.fv_qual
                                                      =
                                                      (uu___3605_27058.FStar_Syntax_Syntax.fv_qual)
                                                  }));
                                            FStar_Syntax_Syntax.lbunivs =
                                              (uu___3603_27056.FStar_Syntax_Syntax.lbunivs);
                                            FStar_Syntax_Syntax.lbtyp =
                                              (uu___3603_27056.FStar_Syntax_Syntax.lbtyp);
                                            FStar_Syntax_Syntax.lbeff =
                                              (uu___3603_27056.FStar_Syntax_Syntax.lbeff);
                                            FStar_Syntax_Syntax.lbdef =
                                              (uu___3603_27056.FStar_Syntax_Syntax.lbdef);
                                            FStar_Syntax_Syntax.lbattrs =
                                              (uu___3603_27056.FStar_Syntax_Syntax.lbattrs);
                                            FStar_Syntax_Syntax.lbpos =
                                              (uu___3603_27056.FStar_Syntax_Syntax.lbpos)
                                          }))
                                   in
                                ((FStar_Pervasives_Native.fst lbs),
                                  uu____27041)
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
                   | uu____27083 ->
                       failwith "Desugaring a let did not produce a let")))
          else
            (let uu____27091 =
               match lets with
               | (pat,body)::[] -> (pat, body)
               | uu____27110 ->
                   failwith
                     "expand_toplevel_pattern should only allow single definition lets"
                in
             match uu____27091 with
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
                       let uu___3628_27147 = pat1  in
                       {
                         FStar_Parser_AST.pat =
                           (FStar_Parser_AST.PatAscribed (var_pat, ty));
                         FStar_Parser_AST.prange =
                           (uu___3628_27147.FStar_Parser_AST.prange)
                       }
                   | uu____27154 -> var_pat  in
                 let main_let =
                   desugar_decl env
                     (let uu___3632_27161 = d  in
                      {
                        FStar_Parser_AST.d =
                          (FStar_Parser_AST.TopLevelLet
                             (isrec, [(fresh_pat, body)]));
                        FStar_Parser_AST.drange =
                          (uu___3632_27161.FStar_Parser_AST.drange);
                        FStar_Parser_AST.quals = (FStar_Parser_AST.Private ::
                          (d.FStar_Parser_AST.quals));
                        FStar_Parser_AST.attrs =
                          (uu___3632_27161.FStar_Parser_AST.attrs)
                      })
                    in
                 let main =
                   let uu____27177 =
                     let uu____27178 =
                       FStar_Ident.lid_of_ids [fresh_toplevel_name]  in
                     FStar_Parser_AST.Var uu____27178  in
                   FStar_Parser_AST.mk_term uu____27177
                     pat.FStar_Parser_AST.prange FStar_Parser_AST.Expr
                    in
                 let build_generic_projection uu____27202 id_opt =
                   match uu____27202 with
                   | (env1,ses) ->
                       let uu____27224 =
                         match id_opt with
                         | FStar_Pervasives_Native.Some id1 ->
                             let lid = FStar_Ident.lid_of_ids [id1]  in
                             let branch1 =
                               let uu____27236 = FStar_Ident.range_of_lid lid
                                  in
                               FStar_Parser_AST.mk_term
                                 (FStar_Parser_AST.Var lid) uu____27236
                                 FStar_Parser_AST.Expr
                                in
                             let bv_pat =
                               let uu____27238 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____27238
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
                               let uu____27244 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatVar
                                    (id1, FStar_Pervasives_Native.None))
                                 uu____27244
                                in
                             let bv_pat1 =
                               let uu____27248 = FStar_Ident.range_of_id id1
                                  in
                               FStar_Parser_AST.mk_pattern
                                 (FStar_Parser_AST.PatAscribed
                                    (bv_pat,
                                      (unit_ty, FStar_Pervasives_Native.None)))
                                 uu____27248
                                in
                             (bv_pat1, branch1)
                          in
                       (match uu____27224 with
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
                            let uu____27309 = desugar_decl env1 id_decl  in
                            (match uu____27309 with
                             | (env2,ses') ->
                                 (env2, (FStar_List.append ses ses'))))
                    in
                 let build_projection uu____27345 id1 =
                   match uu____27345 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         (FStar_Pervasives_Native.Some id1)
                    in
                 let build_coverage_check uu____27384 =
                   match uu____27384 with
                   | (env1,ses) ->
                       build_generic_projection (env1, ses)
                         FStar_Pervasives_Native.None
                    in
                 let bvs =
                   let uu____27408 = gather_pattern_bound_vars pat  in
                   FStar_All.pipe_right uu____27408 FStar_Util.set_elements
                    in
                 let uu____27415 =
                   (FStar_List.isEmpty bvs) &&
                     (let uu____27418 = is_var_pattern pat  in
                      Prims.op_Negation uu____27418)
                    in
                 if uu____27415
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
            let uu____27442 = close_fun env t  in
            desugar_term env uu____27442  in
          let quals1 =
            let uu____27446 =
              (FStar_Syntax_DsEnv.iface env) &&
                (FStar_Syntax_DsEnv.admitted_iface env)
               in
            if uu____27446
            then FStar_Parser_AST.Assumption :: quals
            else quals  in
          let lid = FStar_Syntax_DsEnv.qualify env id1  in
          let attrs =
            FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs  in
          let se =
            let uu____27458 =
              FStar_List.map (trans_qual1 FStar_Pervasives_Native.None)
                quals1
               in
            {
              FStar_Syntax_Syntax.sigel =
                (FStar_Syntax_Syntax.Sig_declare_typ (lid, [], t1));
              FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
              FStar_Syntax_Syntax.sigquals = uu____27458;
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
                let uu____27471 =
                  let uu____27480 = FStar_Syntax_Syntax.null_binder t  in
                  [uu____27480]  in
                let uu____27499 =
                  let uu____27502 =
                    FStar_Syntax_DsEnv.fail_or env
                      (FStar_Syntax_DsEnv.try_lookup_lid env)
                      FStar_Parser_Const.exn_lid
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total
                    uu____27502
                   in
                FStar_Syntax_Util.arrow uu____27471 uu____27499
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
          let uu____27568 =
            let uu____27570 =
              (FStar_Syntax_Util.is_layered src_ed) ||
                (FStar_Syntax_Util.is_layered dst_ed)
               in
            Prims.op_Negation uu____27570  in
          if uu____27568
          then
            let uu____27577 =
              match l.FStar_Parser_AST.lift_op with
              | FStar_Parser_AST.NonReifiableLift t ->
                  let uu____27595 =
                    let uu____27598 =
                      let uu____27599 = desugar_term env t  in
                      ([], uu____27599)  in
                    FStar_Pervasives_Native.Some uu____27598  in
                  (uu____27595, FStar_Pervasives_Native.None)
              | FStar_Parser_AST.ReifiableLift (wp,t) ->
                  let uu____27612 =
                    let uu____27615 =
                      let uu____27616 = desugar_term env wp  in
                      ([], uu____27616)  in
                    FStar_Pervasives_Native.Some uu____27615  in
                  let uu____27623 =
                    let uu____27626 =
                      let uu____27627 = desugar_term env t  in
                      ([], uu____27627)  in
                    FStar_Pervasives_Native.Some uu____27626  in
                  (uu____27612, uu____27623)
              | FStar_Parser_AST.LiftForFree t ->
                  let uu____27639 =
                    let uu____27642 =
                      let uu____27643 = desugar_term env t  in
                      ([], uu____27643)  in
                    FStar_Pervasives_Native.Some uu____27642  in
                  (FStar_Pervasives_Native.None, uu____27639)
               in
            (match uu____27577 with
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
                   let uu____27677 =
                     let uu____27680 =
                       let uu____27681 = desugar_term env t  in
                       ([], uu____27681)  in
                     FStar_Pervasives_Native.Some uu____27680  in
                   {
                     FStar_Syntax_Syntax.source =
                       (src_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.target =
                       (dst_ed.FStar_Syntax_Syntax.mname);
                     FStar_Syntax_Syntax.lift_wp =
                       FStar_Pervasives_Native.None;
                     FStar_Syntax_Syntax.lift = uu____27677
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
             | uu____27688 ->
                 failwith
                   "Impossible! unexpected lift_op for lift to a layered effect")
      | FStar_Parser_AST.Polymonadic_bind (m_eff,n_eff,p_eff,bind1) ->
          let m = lookup_effect_lid env m_eff d.FStar_Parser_AST.drange  in
          let n1 = lookup_effect_lid env n_eff d.FStar_Parser_AST.drange  in
          let p = lookup_effect_lid env p_eff d.FStar_Parser_AST.drange  in
          let uu____27701 =
            let uu____27702 =
              let uu____27703 =
                let uu____27704 =
                  let uu____27715 =
                    let uu____27716 = desugar_term env bind1  in
                    ([], uu____27716)  in
                  ((m.FStar_Syntax_Syntax.mname),
                    (n1.FStar_Syntax_Syntax.mname),
                    (p.FStar_Syntax_Syntax.mname), uu____27715,
                    ([], FStar_Syntax_Syntax.tun))
                   in
                FStar_Syntax_Syntax.Sig_polymonadic_bind uu____27704  in
              {
                FStar_Syntax_Syntax.sigel = uu____27703;
                FStar_Syntax_Syntax.sigrng = (d.FStar_Parser_AST.drange);
                FStar_Syntax_Syntax.sigquals = [];
                FStar_Syntax_Syntax.sigmeta =
                  FStar_Syntax_Syntax.default_sigmeta;
                FStar_Syntax_Syntax.sigattrs = [];
                FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None
              }  in
            [uu____27702]  in
          (env, uu____27701)
      | FStar_Parser_AST.Splice (ids,t) ->
          let t1 = desugar_term env t  in
          let se =
            let uu____27735 =
              let uu____27736 =
                let uu____27743 =
                  FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids  in
                (uu____27743, t1)  in
              FStar_Syntax_Syntax.Sig_splice uu____27736  in
            {
              FStar_Syntax_Syntax.sigel = uu____27735;
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
            let uu____27761 = FStar_Syntax_DsEnv.snapshot env  in
            FStar_All.pipe_right uu____27761 FStar_Pervasives_Native.snd  in
          let uu____27773 =
            FStar_Errors.catch_errors
              (fun uu____27791  ->
                 FStar_Options.with_saved_options
                   (fun uu____27797  -> desugar_decl env d1))
             in
          (match uu____27773 with
           | (errs,r) ->
               (match (errs, r) with
                | ([],FStar_Pervasives_Native.Some (uu____27832,ses)) ->
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
                | (errs1,uu____27854) ->
                    if expected_errs = []
                    then (env0, [])
                    else
                      (let actual_errs =
                         FStar_List.concatMap
                           (fun i  ->
                              FStar_Common.list_of_option
                                i.FStar_Errors.issue_number) errs1
                          in
                       let uu____27890 =
                         FStar_Errors.find_multiset_discrepancy expected_errs
                           actual_errs
                          in
                       match uu____27890 with
                       | FStar_Pervasives_Native.None  -> (env0, [])
                       | FStar_Pervasives_Native.Some (e,n1,n2) ->
                           (FStar_List.iter FStar_Errors.print_issue errs1;
                            (let uu____27935 =
                               let uu____27941 =
                                 let uu____27943 =
                                   FStar_Common.string_of_list
                                     FStar_Util.string_of_int expected_errs
                                    in
                                 let uu____27946 =
                                   FStar_Common.string_of_list
                                     FStar_Util.string_of_int actual_errs
                                    in
                                 let uu____27949 = FStar_Util.string_of_int e
                                    in
                                 let uu____27951 =
                                   FStar_Util.string_of_int n2  in
                                 let uu____27953 =
                                   FStar_Util.string_of_int n1  in
                                 FStar_Util.format5
                                   "This top-level definition was expected to raise error codes %s, but it raised %s (at desugaring time). Error #%s was raised %s times, instead of %s."
                                   uu____27943 uu____27946 uu____27949
                                   uu____27951 uu____27953
                                  in
                               (FStar_Errors.Error_DidNotFail, uu____27941)
                                in
                             FStar_Errors.log_issue
                               d1.FStar_Parser_AST.drange uu____27935);
                            (env0, [])))))

let (desugar_decls :
  env_t ->
    FStar_Parser_AST.decl Prims.list ->
      (env_t * FStar_Syntax_Syntax.sigelt Prims.list))
  =
  fun env  ->
    fun decls  ->
      let uu____27978 =
        FStar_List.fold_left
          (fun uu____27998  ->
             fun d  ->
               match uu____27998 with
               | (env1,sigelts) ->
                   let uu____28018 = desugar_decl env1 d  in
                   (match uu____28018 with
                    | (env2,se) -> (env2, (FStar_List.append sigelts se))))
          (env, []) decls
         in
      match uu____27978 with | (env1,sigelts) -> (env1, sigelts)
  
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
          | (FStar_Pervasives_Native.None ,uu____28109) -> env
          | (FStar_Pervasives_Native.Some
             { FStar_Syntax_Syntax.name = prev_lid;
               FStar_Syntax_Syntax.declarations = uu____28113;
               FStar_Syntax_Syntax.exports = uu____28114;
               FStar_Syntax_Syntax.is_interface = uu____28115;_},FStar_Parser_AST.Module
             (current_lid,uu____28117)) when
              (FStar_Ident.lid_equals prev_lid current_lid) &&
                (FStar_Options.interactive ())
              -> env
          | (FStar_Pervasives_Native.Some prev_mod,uu____28126) ->
              let uu____28129 =
                FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod
                 in
              FStar_Pervasives_Native.fst uu____28129
           in
        let uu____28134 =
          match m with
          | FStar_Parser_AST.Interface (mname,decls,admitted) ->
              let uu____28176 =
                FStar_Syntax_DsEnv.prepare_module_or_interface true admitted
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28176, mname, decls, true)
          | FStar_Parser_AST.Module (mname,decls) ->
              let uu____28198 =
                FStar_Syntax_DsEnv.prepare_module_or_interface false false
                  env1 mname FStar_Syntax_DsEnv.default_mii
                 in
              (uu____28198, mname, decls, false)
           in
        match uu____28134 with
        | ((env2,pop_when_done),mname,decls,intf) ->
            let uu____28240 = desugar_decls env2 decls  in
            (match uu____28240 with
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
          let uu____28308 =
            (FStar_Options.interactive ()) &&
              (let uu____28311 =
                 let uu____28313 =
                   let uu____28315 = FStar_Options.file_list ()  in
                   FStar_List.hd uu____28315  in
                 FStar_Util.get_file_extension uu____28313  in
               FStar_List.mem uu____28311 ["fsti"; "fsi"])
             in
          if uu____28308 then as_interface m else m  in
        let uu____28329 = desugar_modul_common curmod env m1  in
        match uu____28329 with
        | (env1,modul,pop_when_done) ->
            if pop_when_done
            then
              let uu____28351 = FStar_Syntax_DsEnv.pop ()  in
              (uu____28351, modul)
            else (env1, modul)
  
let (desugar_modul :
  FStar_Syntax_DsEnv.env ->
    FStar_Parser_AST.modul -> (env_t * FStar_Syntax_Syntax.modul))
  =
  fun env  ->
    fun m  ->
      let uu____28373 =
        desugar_modul_common FStar_Pervasives_Native.None env m  in
      match uu____28373 with
      | (env1,modul,pop_when_done) ->
          let uu____28390 =
            FStar_Syntax_DsEnv.finish_module_or_interface env1 modul  in
          (match uu____28390 with
           | (env2,modul1) ->
               ((let uu____28402 =
                   FStar_Options.dump_module
                     (modul1.FStar_Syntax_Syntax.name).FStar_Ident.str
                    in
                 if uu____28402
                 then
                   let uu____28405 =
                     FStar_Syntax_Print.modul_to_string modul1  in
                   FStar_Util.print1 "Module after desugaring:\n%s\n"
                     uu____28405
                 else ());
                (let uu____28410 =
                   if pop_when_done
                   then
                     FStar_Syntax_DsEnv.export_interface
                       modul1.FStar_Syntax_Syntax.name env2
                   else env2  in
                 (uu____28410, modul1))))
  
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
        (fun uu____28460  ->
           let uu____28461 = desugar_modul env modul  in
           match uu____28461 with | (e,m) -> (m, e))
  
let (decls_to_sigelts :
  FStar_Parser_AST.decl Prims.list ->
    FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv)
  =
  fun decls  ->
    fun env  ->
      with_options
        (fun uu____28499  ->
           let uu____28500 = desugar_decls env decls  in
           match uu____28500 with | (env1,sigelts) -> (sigelts, env1))
  
let (partial_ast_modul_to_modul :
  FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option ->
    FStar_Parser_AST.modul ->
      FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv)
  =
  fun modul  ->
    fun a_modul  ->
      fun env  ->
        with_options
          (fun uu____28551  ->
             let uu____28552 = desugar_partial_modul modul env a_modul  in
             match uu____28552 with | (env1,modul1) -> (modul1, env1))
  
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
              | uu____28647 ->
                  let t =
                    let uu____28657 =
                      FStar_Syntax_Syntax.mk
                        (FStar_Syntax_Syntax.Tm_abs
                           (bs, FStar_Syntax_Syntax.t_unit,
                             FStar_Pervasives_Native.None))
                        FStar_Pervasives_Native.None FStar_Range.dummyRange
                       in
                    erase_univs uu____28657  in
                  let uu____28670 =
                    let uu____28671 = FStar_Syntax_Subst.compress t  in
                    uu____28671.FStar_Syntax_Syntax.n  in
                  (match uu____28670 with
                   | FStar_Syntax_Syntax.Tm_abs (bs1,uu____28683,uu____28684)
                       -> bs1
                   | uu____28709 -> failwith "Impossible")
               in
            let uu____28719 =
              let uu____28726 = erase_binders ed.FStar_Syntax_Syntax.binders
                 in
              FStar_Syntax_Subst.open_term' uu____28726
                FStar_Syntax_Syntax.t_unit
               in
            match uu____28719 with
            | (binders,uu____28728,binders_opening) ->
                let erase_term t =
                  let uu____28736 =
                    let uu____28737 =
                      FStar_Syntax_Subst.subst binders_opening t  in
                    erase_univs uu____28737  in
                  FStar_Syntax_Subst.close binders uu____28736  in
                let erase_tscheme uu____28755 =
                  match uu____28755 with
                  | (us,t) ->
                      let t1 =
                        let uu____28775 =
                          FStar_Syntax_Subst.shift_subst
                            (FStar_List.length us) binders_opening
                           in
                        FStar_Syntax_Subst.subst uu____28775 t  in
                      let uu____28778 =
                        let uu____28779 = erase_univs t1  in
                        FStar_Syntax_Subst.close binders uu____28779  in
                      ([], uu____28778)
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
                    | uu____28802 ->
                        let bs =
                          let uu____28812 =
                            FStar_Syntax_Subst.subst_binders opening
                              action.FStar_Syntax_Syntax.action_params
                             in
                          FStar_All.pipe_left erase_binders uu____28812  in
                        let t =
                          FStar_Syntax_Syntax.mk
                            (FStar_Syntax_Syntax.Tm_abs
                               (bs, FStar_Syntax_Syntax.t_unit,
                                 FStar_Pervasives_Native.None))
                            FStar_Pervasives_Native.None
                            FStar_Range.dummyRange
                           in
                        let uu____28852 =
                          let uu____28853 =
                            let uu____28856 =
                              FStar_Syntax_Subst.close binders t  in
                            FStar_Syntax_Subst.compress uu____28856  in
                          uu____28853.FStar_Syntax_Syntax.n  in
                        (match uu____28852 with
                         | FStar_Syntax_Syntax.Tm_abs
                             (bs1,uu____28858,uu____28859) -> bs1
                         | uu____28884 -> failwith "Impossible")
                     in
                  let erase_term1 t =
                    let uu____28892 =
                      let uu____28893 = FStar_Syntax_Subst.subst opening t
                         in
                      erase_univs uu____28893  in
                    FStar_Syntax_Subst.close binders uu____28892  in
                  let uu___3957_28894 = action  in
                  let uu____28895 =
                    erase_term1 action.FStar_Syntax_Syntax.action_defn  in
                  let uu____28896 =
                    erase_term1 action.FStar_Syntax_Syntax.action_typ  in
                  {
                    FStar_Syntax_Syntax.action_name =
                      (uu___3957_28894.FStar_Syntax_Syntax.action_name);
                    FStar_Syntax_Syntax.action_unqualified_name =
                      (uu___3957_28894.FStar_Syntax_Syntax.action_unqualified_name);
                    FStar_Syntax_Syntax.action_univs = [];
                    FStar_Syntax_Syntax.action_params = erased_action_params;
                    FStar_Syntax_Syntax.action_defn = uu____28895;
                    FStar_Syntax_Syntax.action_typ = uu____28896
                  }  in
                let uu___3959_28897 = ed  in
                let uu____28898 = FStar_Syntax_Subst.close_binders binders
                   in
                let uu____28899 =
                  erase_tscheme ed.FStar_Syntax_Syntax.signature  in
                let uu____28900 =
                  FStar_Syntax_Util.apply_eff_combinators erase_tscheme
                    ed.FStar_Syntax_Syntax.combinators
                   in
                let uu____28901 =
                  FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions
                   in
                {
                  FStar_Syntax_Syntax.mname =
                    (uu___3959_28897.FStar_Syntax_Syntax.mname);
                  FStar_Syntax_Syntax.cattributes =
                    (uu___3959_28897.FStar_Syntax_Syntax.cattributes);
                  FStar_Syntax_Syntax.univs = [];
                  FStar_Syntax_Syntax.binders = uu____28898;
                  FStar_Syntax_Syntax.signature = uu____28899;
                  FStar_Syntax_Syntax.combinators = uu____28900;
                  FStar_Syntax_Syntax.actions = uu____28901;
                  FStar_Syntax_Syntax.eff_attrs =
                    (uu___3959_28897.FStar_Syntax_Syntax.eff_attrs)
                }
             in
          let push_sigelt1 env se =
            match se.FStar_Syntax_Syntax.sigel with
            | FStar_Syntax_Syntax.Sig_new_effect ed ->
                let se' =
                  let uu___3966_28917 = se  in
                  let uu____28918 =
                    let uu____28919 = erase_univs_ed ed  in
                    FStar_Syntax_Syntax.Sig_new_effect uu____28919  in
                  {
                    FStar_Syntax_Syntax.sigel = uu____28918;
                    FStar_Syntax_Syntax.sigrng =
                      (uu___3966_28917.FStar_Syntax_Syntax.sigrng);
                    FStar_Syntax_Syntax.sigquals =
                      (uu___3966_28917.FStar_Syntax_Syntax.sigquals);
                    FStar_Syntax_Syntax.sigmeta =
                      (uu___3966_28917.FStar_Syntax_Syntax.sigmeta);
                    FStar_Syntax_Syntax.sigattrs =
                      (uu___3966_28917.FStar_Syntax_Syntax.sigattrs);
                    FStar_Syntax_Syntax.sigopts =
                      (uu___3966_28917.FStar_Syntax_Syntax.sigopts)
                  }  in
                let env1 = FStar_Syntax_DsEnv.push_sigelt env se'  in
                push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals
                  ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng
            | uu____28921 -> FStar_Syntax_DsEnv.push_sigelt env se  in
          let uu____28922 =
            FStar_Syntax_DsEnv.prepare_module_or_interface false false en
              m.FStar_Syntax_Syntax.name mii
             in
          match uu____28922 with
          | (en1,pop_when_done) ->
              let en2 =
                let uu____28939 =
                  FStar_Syntax_DsEnv.set_current_module en1
                    m.FStar_Syntax_Syntax.name
                   in
                FStar_List.fold_left push_sigelt1 uu____28939
                  m.FStar_Syntax_Syntax.exports
                 in
              let env = FStar_Syntax_DsEnv.finish en2 m  in
              let uu____28941 =
                if pop_when_done
                then
                  FStar_Syntax_DsEnv.export_interface
                    m.FStar_Syntax_Syntax.name env
                else env  in
              ((), uu____28941)
  